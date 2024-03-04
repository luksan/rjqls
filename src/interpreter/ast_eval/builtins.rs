use super::*;

impl<'f> ExprEval<'f> {
    pub(super) fn get_builtin<'expr>(&self, name: &str, args: &'expr [Expr]) -> ExprResult<'expr>
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
            ("length", 0) => expr_val_from_value(self.input.length()?),

            // Regex
            ("match", 1) => self.match_1(args),
            ("split", 1) => {
                let input = self
                    .input
                    .as_str()
                    .context("split input  must be a string")?;
                let sep_str = args[0].accept(self)?.next().context("Empty separator")??;
                let sep = sep_str
                    .as_str()
                    .context("split separator must be a string")?;
                // TODO: less copying of strings
                expr_val_from_value(Value::from(
                    input.split(sep).map(|s| Value::from(s)).collect::<Vec<_>>(),
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

            (_, len) => bail!("Function {name}/{len} not found."),
        }
    }
}

#[cfg(test)]
mod test_builtins {
    use std::str::FromStr;

    use pest::Parser;

    use crate::parser::{JqGrammar, Rule};
    use crate::parser::pratt_expr::pratt_parser;

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
        let ast = parse_filter(filter).unwrap();
        let rvals = ast.accept(&eval)?.collect();
        rvals
    }

    fn parse_filter(filter: &str) -> Result<Ast> {
        let mut pairs = JqGrammar::parse(Rule::pratt_prog, filter).context("Parse error")?;
        let mut pairs = pairs.next().unwrap().into_inner();
        let pairs = pairs.next().unwrap().into_inner();
        Ok(pratt_parser(pairs))
    }
}
