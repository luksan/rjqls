use anyhow::anyhow;

use crate::bail;
use crate::interpreter::generator::{GenCycle, GenGen};

use super::*;

macro_rules! ret_some_err {
    ($opt_res:expr) => {{
        match $opt_res {
            None => return None,

            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(v)) => v,
        }
    }};
}

impl<'f> ExprEval<'f> {
    pub(super) fn get_builtin<'expr>(
        &self,
        name: &str,
        args: &'expr [AstNode],
    ) -> EvalVisitorRet<'expr>
    where
        'f: 'expr,
        'expr: 'f,
    {
        match (name, args.len()) {
            ("add", 0) => {
                let mut sum: Value = ().into();
                for v in self.input.iterate()? {
                    sum = sum.add(v)?;
                }
                expr_val_from_value(sum)
            }
            ("empty", 0) => Ok(Default::default()),
            ("error", 0) => Err(EvalError::Value(self.input.clone())),
            ("error", 1) => {
                let mut arg = args[0].accept(self)?;
                let Some(val) = arg.next() else {
                    return Ok(Generator::empty());
                };
                Err(EvalError::Value(val?))
            }
            ("explode", 0) => {
                let input = self
                    .input
                    .as_str()
                    .context("explode input must be a string")?;
                expr_val_from_value(Value::from(
                    input
                        .chars()
                        .map(|c| Value::from(c as usize))
                        .collect::<Vec<_>>(),
                ))
            }
            ("floor", 0) => math::floor(&self.input),
            ("implode", 0) => {
                let input = self
                    .input
                    .as_array()
                    .context("implode input must be an array")?;
                expr_val_from_value(Value::from(
                    input
                        .iter()
                        .map(|c| {
                            c.as_bigint()
                                .context("Unicode codepoints must be numeric")
                                .and_then(|i| char::from_u32(i as _).context("Invalid codepoint"))
                        })
                        .collect::<Result<String>>()?,
                ))
            }
            ("length", 0) => expr_val_from_value(self.input.length()?),
            ("not", 0) => expr_val_from_value((!self.input.is_truthy()).into()),

            // Regex
            ("_match_impl", 3) => {
                let [regex, mods, testmode] = args else {
                    unreachable!()
                };
                let mut ret = vec![];
                for regex in regex.accept(self)? {
                    let regex = regex?; // TODO: push the error?
                    for mods in mods.accept(self)? {
                        let mods = mods?;
                        for testmode in testmode.accept(self)? {
                            let caps = regex::f_match(&self.input, &regex, &mods, &testmode?)
                                .map_err(|e| e.into());
                            ret.push(caps);
                        }
                    }
                }
                Ok(Generator::from_iter(ret))
            }
            ("range", 2) => {
                let start = args[0].accept(self)?.restrict(
                    |val| val.as_bigint().is_some(),
                    |_| anyhow!("Range bounds must be numeric"),
                );
                let end = GenCycle::new(args[1].accept(self)?.restrict(
                    |val| val.as_bigint().is_some(),
                    |_| anyhow!("Range bounds must be numeric"),
                ));
                let mut start_val = Value::Null;
                let g = GenGen::new((start, end), move |gens| -> Option<_> {
                    let mut retry_once = 1;
                    while retry_once >= 0 {
                        if start_val == Value::Null {
                            start_val = ret_some_err!(gens.0.next());
                        }
                        match gens.1.next() {
                            Some(Ok(val)) => {
                                return Some(Ok(Generator::from_iter(
                                    (start_val.as_bigint().unwrap()..val.as_bigint().unwrap())
                                        .map(|v| Ok(v.into())),
                                )))
                            }
                            Some(Err(err)) => return Some(Err(err)),
                            None => {
                                start_val = Value::Null;
                                retry_once -= 1;
                            }
                        }
                    }
                    None
                });
                Ok(Generator::from_iter(g))
            }
            ("split", 1) => {
                let input = self
                    .input
                    .as_str()
                    .context("split input must be a string")?;
                let sep_str = args[0].accept(self)?.next().context("Empty separator")??;
                let sep = sep_str
                    .as_str()
                    .context("split separator must be a string")?;
                // TODO: less copying of strings
                expr_val_from_value(Value::from(
                    input.split(sep).map(Value::from).collect::<Vec<_>>(),
                ))
            }
            ("tostring", 0) => expr_val_from_value(match self.input {
                // JSON encode input value
                Value::String(_) => self.input.clone(),
                _ => Value::from(format!("{}", self.input)),
            }),
            ("type", 0) => {
                let typ = match self.input {
                    Value::Array(_) => "array",
                    Value::Bool(_) => "boolean",
                    Value::Number(_) => "number",
                    Value::Null => "null",
                    Value::Object(_) => "object",
                    Value::String(_) => "string",
                };
                expr_val_from_value(Value::from(typ))
            }

            ("_strindices", 1) => {
                let input = self.input.as_str().context("input  must be a string")?;
                let needle = args[0].accept(self)?.next().unwrap()?;
                let needle = needle.as_str().context("needle must be a string")?;
                let mut ret = vec![];
                let mut pos = 0;

                while let Some(i) = input[pos..].find(needle) {
                    ret.push(Value::from(i + pos));
                    pos += i + 1;
                }
                expr_val_from_value(Value::from(ret))
            }

            (_, len) => bail!("Function {name}/{len} not found."),
        }
    }
}

#[cfg(test)]
mod test_builtins {
    use std::str::FromStr;

    use crate::parser::parse_program;
    use crate::src_reader::test_src_reader;

    use super::*;

    #[test]
    fn test_type() {
        let filter = "[.[] | type] ";
        let input = Value::from_str(r#"[0, false, [], {}, null, "hello"]"#).unwrap();
        let out_ref =
            Value::from_str(r#"["number", "boolean", "array", "object", "null", "string"]"#)
                .unwrap();
        let out = eval_expr(filter, input).unwrap();
        assert_eq!(out[0], out_ref);
    }

    fn eval_expr(filter: &str, input: Value) -> Result<Vec<Value>> {
        let scope = Arc::new(FuncScope::default());
        let var_scope = VarScope::new();
        let eval = ExprEval::new(scope, input, var_scope);
        let ast = parse_program(filter, &mut test_src_reader()).unwrap();
        eval.visit(&ast)
    }
}
