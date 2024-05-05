use anyhow::anyhow;
use itertools::Itertools;

use crate::bail;
use crate::interpreter::generator::{CrossProd, GenCycle};

use super::*;

impl<'f, Kind> ExprEval<'f, Kind>
where
    Kind: EvalKind + 'f,
{
    pub(super) fn call_builtin<'expr>(
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
                for v in self.input().iterate()? {
                    sum = sum.add(&v)?;
                }
                sum.into()
            }
            ("delpaths", 1) => {
                let evald = args[0].accept(self).next()??; // TODO: handle all paths
                let paths = evald
                    .as_array()
                    .context("Paths must be specified as an array")?;
                let mut paths: Vec<_> = paths
                    .iter()
                    .map(|p| {
                        p.as_array()
                            .context("Path must be specified as array, not TODO")
                    })
                    .try_collect()?;
                paths.sort_unstable();
                self.delpaths(self.input().clone(), &mut paths.into_iter())
                    .into()
            }
            ("empty", 0) => Default::default(),
            ("error", 0) => EvalError::Value(self.input().clone()).into(),
            ("error", 1) => {
                let mut arg = args[0].accept(self);
                EvalError::Value(arg.next()??).into()
            }
            ("explode", 0) => {
                let input = self
                    .input()
                    .as_str()
                    .context("explode input must be a string")?;
                Value::from(
                    input
                        .chars()
                        .map(|c| Value::from(c as usize))
                        .collect::<Vec<_>>(),
                )
                .into()
            }
            ("floor", 0) => math::floor(self.input()),
            ("implode", 0) => {
                let input = self
                    .input()
                    .as_array()
                    .context("implode input must be an array")?;
                Value::from(
                    input
                        .iter()
                        .map(|c| {
                            c.as_bigint()
                                .context("Unicode codepoints must be numeric")
                                .and_then(|i| char::from_u32(i as _).context("Invalid codepoint"))
                        })
                        .collect::<Result<String>>()?,
                )
                .into()
            }
            ("length", 0) => self.input().length().into(),
            ("not", 0) => Value::from(!self.input().is_truthy()).into(),

            // Regex
            ("_match_impl", 3) => {
                let [regex, mods, testmode] = args else { unreachable!() };
                let mut ret = vec![];
                for regex in regex.accept(self) {
                    let regex = regex?; // TODO: push the error?
                    for mods in mods.accept(self) {
                        let mods = mods?;
                        for testmode in testmode.accept(self) {
                            let caps = regex::f_match(self.input(), &regex, &mods, &testmode?)
                                .map_err(|e| e.into());
                            ret.push(caps);
                        }
                    }
                }
                Generator::from_iter(ret)
            }
            ("range", 2) => {
                let start = args[0].accept(self).restrict(
                    |val| val.as_bigint().is_some(),
                    |_| anyhow!("Range bounds must be numeric"),
                );
                let end = GenCycle::new(args[1].accept(self).restrict(
                    |val| val.as_bigint().is_some(),
                    |_| anyhow!("Range bounds must be numeric"),
                ));

                let g = CrossProd::new([Box::new(start), Box::new(end)], |[start, end]| {
                    Some(Ok(Generator::from_iter(
                        (start.as_bigint().unwrap()..end.as_bigint().unwrap())
                            .map(|v| Ok(v.into())),
                    )))
                });

                Generator::from_iter(g)
            }
            ("split", 1) => {
                let input = self
                    .input()
                    .as_str()
                    .context("split input must be a string")?;
                let sep_str = args[0].accept(self).next().context("Empty separator")??;
                let sep = sep_str
                    .as_str()
                    .context("split separator must be a string")?;
                // TODO: less copying of strings
                Value::from(input.split(sep).map(Value::from).collect::<Vec<_>>()).into()
            }
            ("tostring", 0) => {
                match self.input() {
                    // JSON encode input value
                    Value::String(_) => self.input().clone(),
                    _ => Value::from(format!("{}", self.input())),
                }
                .into()
            }
            ("type", 0) => {
                let typ = match self.input() {
                    Value::Array(_) => "array",
                    Value::Bool(_) => "boolean",
                    Value::Number(_) => "number",
                    Value::Null => "null",
                    Value::Object(_) => "object",
                    Value::String(_) => "string",
                };
                Value::from(typ).into()
            }

            ("_strindices", 1) => {
                let input = self.input().as_str().context("input  must be a string")?;
                let needle = args[0].accept(self).next()??;
                let needle = needle.as_str().context("needle must be a string")?;
                let mut ret = vec![];
                let mut pos = 0;

                while let Some(i) = input[pos..].find(needle) {
                    ret.push(Value::from(i + pos));
                    pos += i + 1;
                }
                Value::from(ret).into()
            }

            (_, len) => bail!("Function {name}/{len} not found."),
        }
    }

    /// paths must be sorted
    fn delpaths(&self, input: Value, paths: &mut dyn Iterator<Item = &[Value]>) -> Result<Value> {
        let mut del = vec![];
        let group = paths
            .filter_map(|p| p.split_first())
            .group_by(|(this, _)| *this);

        let mut out = input;
        for (this, paths) in group.into_iter() {
            let mut tail = paths.map(|p| p.1).peekable();
            if tail.peek().unwrap().is_empty() {
                del.push(this);
                continue
            }
            out = out.replace_field(&this, |slot_val| self.delpaths(slot_val, &mut tail))?;
        }

        for d in del.into_iter().rev() {
            out = out.del(d)?;
        }
        Ok(out)
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
