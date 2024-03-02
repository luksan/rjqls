use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Deref;
use std::sync::{Arc, RwLock};

use anyhow::{bail, Context, Result};
use onig::{Regex, RegexOptions, Syntax};

use crate::interpreter::bind_var_pattern::BindVars;
use crate::interpreter::BoundFunc;
use crate::interpreter::func_scope::FuncScope;
use crate::interpreter::generator::{Generator, ResVal};
use crate::parser::expr_ast::{Ast, BinOps, Expr, ExprVisitor};
use crate::value::{Map, Value, ValueOps};

#[derive(Debug)]
pub struct VarScope {
    entries: RwLock<HashMap<String, Value>>,
    parent: Option<Arc<Self>>,
}

impl VarScope {
    pub(crate) fn new() -> Arc<Self> {
        Self {
            entries: Default::default(),
            parent: None,
        }
        .into()
    }

    fn begin_scope(self: &Arc<Self>) -> Arc<Self> {
        Self {
            entries: Default::default(),
            parent: Some(self.clone()),
        }
        .into()
    }

    fn get_parent(&self) -> Option<&Arc<Self>> {
        self.parent.as_ref()
    }

    fn get_variable(&self, name: &str) -> ResVal {
        let entries = self.entries.read().unwrap();
        if let Some(val) = entries.get(name) {
            return Ok(val.clone());
        }
        match self.get_parent() {
            None => bail!("Variable '{name}' is not defined."),
            Some(p) => p.get_variable(name),
        }
    }
    pub(crate) fn set_variable(&self, name: &str, value: Value) {
        let mut entries = self.entries.write().unwrap();
        entries.insert(name.to_owned(), value);
    }
}

#[derive(Debug, Clone)]
pub struct ExprEval<'f> {
    input: Value,
    variables: RefCell<Arc<VarScope>>,
    func_scope: RefCell<Arc<FuncScope<'f>>>,
}

impl<'f> ExprEval<'f> {
    pub fn new(func_scope: Arc<FuncScope<'f>>, input: Value, var_scope: Arc<VarScope>) -> Self {
        Self {
            input,
            variables: var_scope.into(),
            func_scope: func_scope.into(),
        }
    }

    fn get_function<'expr>(&self, name: &str, args: &'expr [Expr]) -> Option<BoundFunc<'expr>>
    where
        'f: 'expr,
    {
        let scope = self.func_scope.borrow();
        let func = scope.get_func(name, args.len())?;
        let ret = func.bind(name.to_owned(), scope.clone(), args).unwrap();
        Some(ret)
    }

    fn get_builtin<'expr>(&self, name: &str, args: &'expr [Expr]) -> ExprResult<'expr>
    where
        'f: 'expr,
        'expr: 'f,
    {
        Ok(match (name, args.len()) {
            ("add", 0) => {
                let mut sum: Value = ().into();
                for v in self.input.iterate()? {
                    sum = sum.add(v)?;
                }
                expr_val_from_value(sum)?
            }
            ("empty", 0) => Default::default(),
            ("length", 0) => expr_val_from_value(self.input.length()?)?,

            // Regex
            ("match", 1) => {
                let regex = args[0]
                    .accept(self)?
                    .next()
                    .context("match argument must be a string")??;
                let regex = regex
                    .as_array()
                    .and_then(|a| a.get(0))
                    .unwrap_or(&regex)
                    .as_str()
                    .context("match argument must be a string")?;
                let input = self.input.as_str().with_context(|| {
                    format!(
                        "{} cannot be matched since it is not a string.",
                        &self.input
                    )
                })?;
                let regex_opts = RegexOptions::REGEX_OPTION_CAPTURE_GROUP;
                let re = Regex::with_options(regex, regex_opts, Syntax::perl_ng())
                    .context("Invalid regular expression")?;

                let caps: Vec<Value> = re
                    .captures_iter(input)
                    .map(|cap| {
                        let mut obj = Map::new();
                        let mtch = cap.at(0).unwrap();
                        obj.insert("offset".to_owned(), cap.offset().into());
                        obj.insert("length".to_owned(), mtch.len().into());
                        obj.insert("string".to_owned(), mtch.into());
                        let mut subs: Vec<Value> = cap
                            .iter_pos()
                            .skip(1)
                            .map(|tuple_opt| {
                                let mut obj = Map::new();
                                if let Some((start, end)) = tuple_opt {
                                    let a = start - cap.offset();
                                    let b = end - cap.offset();
                                    let txt = mtch[a..b].to_owned();
                                    let len = txt.len().into();
                                    obj.insert("offset".to_owned(), start.into());
                                    obj.insert("string".to_owned(), txt.into());
                                    obj.insert("length".to_owned(), len);
                                } else {
                                    obj.insert("offset".to_owned(), Value::from(-1));
                                    obj.insert("string".to_owned(), ().into());
                                    obj.insert("length".to_owned(), 0.into());
                                }
                                obj.insert("name".to_owned(), ().into());
                                obj.into()
                            })
                            .collect();

                        re.foreach_name(|name, pos| {
                            subs[pos[0] as usize - 1]
                                .as_mut_obj()
                                .unwrap()
                                .insert("name".to_owned(), name.into());
                            true
                        });

                        obj.insert("captures".to_owned(), subs.into());
                        obj.into()
                    })
                    .collect();
                Generator::from_iter(caps.into_iter().map(|o| Ok(o)))
            }

            (_, len) => bail!("Function {name}/{len} not found."),
        })
    }

    fn get_variable(&self, name: &str) -> ExprResult<'static> {
        Ok(self.variables.borrow().get_variable(name)?.into())
    }

    fn begin_scope(&self) {
        let mut vars = self.variables.borrow_mut();
        let inner = vars.begin_scope();
        *vars = inner;
    }

    fn end_scope(&self) {
        let mut vars = self.variables.borrow_mut();
        let outer = vars.get_parent().unwrap().clone();
        *vars = outer;
    }
    fn enter_func_scope(&self, scope: Arc<FuncScope<'f>>) {
        let mut s = self.func_scope.borrow_mut();
        *s = scope;
    }
}

pub type ExprValue<'e> = Generator<'e>;
pub type ExprResult<'e> = Result<ExprValue<'e>>;

fn expr_val_from_value(val: Value) -> ExprResult<'static> {
    Ok(val.into())
}

impl<'e> ExprVisitor<'e, ExprResult<'e>> for ExprEval<'e> {
    fn default(&self) -> ExprResult<'e> {
        panic!();
    }

    fn visit_array(&self, elements: &'e [Expr]) -> ExprResult<'e> {
        let mut ret = Generator::empty();
        for e in elements {
            let v = e.accept(self)?;
            ret = ret.chain(v.into_iter());
        }
        expr_val_from_value(Value::from(ret.collect::<Result<Vec<_>>>()?))
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast) -> ExprResult<'e> {
        let vals = vals.accept(self)?;
        for v in vals {
            // TODO this should bifurcate the execution
            BindVars::bind(&v?, vars, self.variables.borrow().deref())?;
        }
        expr_val_from_value(self.input.clone())
    }

    fn visit_binop(&self, op: BinOps, lhs: &'e Ast, rhs: &'e Ast) -> ExprResult<'e> {
        let lhs = lhs.accept(self)?;
        let mut ret = Vec::new(); // TODO generator
        for l in lhs {
            let l = &l?;
            let rhs = rhs.accept(self)?;
            for r in rhs {
                let r = &r?;
                let r = match op {
                    BinOps::Add => l.add(r),
                    BinOps::Sub => l.sub(r),
                    BinOps::Mul => l.mul(r),
                    BinOps::Div => l.div(r),

                    BinOps::Eq => Ok(Value::from(l == r)),
                    BinOps::NotEq => Ok(Value::from(l != r)),
                    BinOps::Less => Ok(l.less_than(r)),
                    op => unimplemented!("{op:?}"),
                };
                ret.push(r);
            }
        }
        Ok(Generator::from_iter(ret))
    }

    fn visit_call(&self, name: &str, args: &'e [Expr]) -> ExprResult<'e> {
        if let Some(bound_func) = self.get_function(name, args) {
            let eval = ExprEval::new(
                bound_func.func_scope,
                self.input.clone(),
                self.variables.borrow().clone(),
            );
            bound_func.function.filter.accept(&eval)
        } else {
            self.get_builtin(name, args)
        }
    }

    fn visit_comma(&self, lhs: &'e Expr, rhs: &'e Expr) -> ExprResult<'e> {
        let lhs = lhs.accept(self)?;
        let rhs = rhs.accept(self)?;
        Ok(lhs.chain(rhs))
    }

    fn visit_define_function(
        &self,
        name: &str,
        args: &'e [String],
        body: &'e Expr,
        rhs: &'e Expr,
    ) -> ExprResult<'e> {
        let mut scope = self.func_scope.borrow().new_inner();
        scope.push(name.to_owned(), args.into(), body);
        self.enter_func_scope(Arc::new(scope));
        rhs.accept(self)
    }

    fn visit_dot(&self) -> ExprResult<'e> {
        expr_val_from_value(self.input.clone())
    }

    fn visit_ident(&self, ident: &str) -> ExprResult<'e> {
        expr_val_from_value(Value::from(ident))
    }

    fn visit_if_else(&self, cond: &'e [Expr], branches: &'e [Expr]) -> ExprResult<'e> {
        let ret = Default::default();
        fn check_remaining<'g>(
            this: &ExprEval<'g>,
            mut ret: Generator<'g>,
            cond: &'g [Expr],
            branches: &'g [Expr],
        ) -> Result<Generator<'g>> {
            if cond.is_empty() {
                ret = ret.chain(branches[0].accept(this)?);
                return Ok(ret);
            }
            let vals = cond[0].accept(this)?;
            for v in vals {
                let v = v?;
                if v.is_truthy() {
                    ret = ret.chain(branches[0].accept(this)?);
                } else {
                    ret = check_remaining(this, ret, &cond[1..], &branches[1..])?;
                }
            }
            Ok(ret)
        }
        check_remaining(self, ret, cond, branches)
    }

    // array or object index
    fn visit_index(&self, expr: &'e Expr, idx: Option<&'e Expr>) -> ExprResult<'e> {
        let e = expr
            .accept(self)
            .with_context(|| format!("Eval of expr for indexing failed {expr:?}"))?;
        let Some(idx) = idx else {
            // iterate all values
            let mut ret = Vec::new();
            for v in e {
                ret.extend(v?.iterate()?.cloned().map(Ok));
            }
            return Ok(ret.into());
        };
        let mut ret = Vec::new();
        for v in e {
            let v = &v?;
            let idx = idx.accept(self).context("Index failed to evaluate")?;
            for i in idx {
                let i = &i?;
                let val = v
                    .index(i)
                    .with_context(|| format!("Failed to index {v} with {i}."));
                ret.push(val);
            }
        }
        Ok(ret.into())
    }

    fn visit_literal(&self, lit: &Value) -> ExprResult<'e> {
        expr_val_from_value(lit.clone())
    }

    fn visit_object(&self, members: &'e [Expr]) -> ExprResult<'e> {
        let mut objects: Vec<Map> = vec![Map::default()];
        for member in members {
            assert!(matches!(member, Expr::ObjectEntry { .. }));
            let mut keyvals = member.accept(self)?;
            let key = keyvals.next().unwrap()?;
            let key = key.as_str().context("Object key must be a string")?;
            let mut values = keyvals;

            let obj_cnt = objects.len();

            let mut val = values.next().unwrap()?;
            let mut obj_slice = &mut objects[0..];
            loop {
                for o in obj_slice {
                    o.insert(key.to_string(), val.clone());
                }
                let Some(n) = values.next() else {
                    break;
                };
                val = n?;
                let obj_len = objects.len();
                objects.extend_from_within(0..obj_cnt);
                obj_slice = &mut objects[obj_len..];
            }
        }
        Ok(objects
            .into_iter()
            .map(|m| Ok(Value::from(m)))
            .collect::<Vec<_>>()
            .into())
    }

    fn visit_obj_entry(&self, key: &'e Expr, value: &'e Expr) -> ExprResult<'e> {
        let mut key_gen = key.accept(self)?;
        let val = value.accept(self)?;
        let key = key_gen.next().unwrap();
        let mut ret = vec![key];
        ret.extend(val);
        Ok(ret.into())
    }

    fn visit_pipe(&self, lhs: &'e Expr, rhs: &'e Expr) -> ExprResult<'e> {
        let lhs = lhs.accept(self)?;
        let mut ret = Generator::empty();
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value?;
            ret = ret.chain(rhs.accept(&rhs_eval)?);
        }
        self.enter_func_scope(rhs_eval.func_scope.take());
        Ok(ret)
    }

    fn visit_scope(&self, inner: &'e Expr) -> ExprResult<'e> {
        self.begin_scope();
        let r = inner.accept(self);
        self.end_scope();
        r
    }

    fn visit_string_interp(&self, parts: &'e [Expr]) -> ExprResult<'e> {
        let mut ret: Vec<String> = vec!["".to_owned()];
        for part in parts {
            if let Expr::Literal(string_lit) = part {
                if let Some(s) = string_lit.as_str() {
                    for r in ret.iter_mut() {
                        r.push_str(s);
                    }
                    continue;
                }
            }
            let mut values = part.accept(self)?;
            let Some(val) = values.next() else {
                return Ok(Generator::empty());
            };
            let prefix = ret.clone();
            let mut strings = &mut ret[0..];
            let mut val = val?;
            loop {
                for s in strings {
                    s.push_str(&val.to_string());
                }
                let Some(next) = values.next() else {
                    break;
                };
                val = next?;
                let end = ret.len();
                ret.extend(prefix.iter().cloned());
                strings = &mut ret[end..]
            }
        }
        let ret = ret.into_iter().map(|s| Ok(s.into()));
        Ok(Generator::from_iter(ret))
    }

    fn visit_variable(&self, name: &str) -> ExprResult<'e> {
        self.get_variable(name)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::parser::parse_filter;

    use super::*;

    #[test]
    fn test_expr_eval() {
        let array = Value::from_str("[1, 2, 3]").unwrap();
        let filter = ". as [$a, $b] | $a + $b";
        let result = eval_expr(filter, array).unwrap();
        for _v in result {
            // println!("{_v},")
        }
    }

    #[test]
    fn test_scope_fail() {
        let filter = "(3 as $a | $a) | $a";
        let err = eval_expr(filter, ().into()).unwrap_err();
        assert_eq!(&err.to_string(), "Variable 'a' is not defined.")
    }

    #[test]
    fn test_if_else() {
        let filter = r#"if .[] then "hej" elif .[] == false then "hmm" else 4 end"#;
        let input = Value::from_str("[1,false,3]").unwrap();
        let val = eval_expr(filter, input).unwrap();
        assert_eq!(
            format!("{val:?}"),
            r#"[String("hej"), Number(4), String("hmm"), Number(4), String("hej")]"#
        )
    }

    #[test]
    fn test_regex_match() {
        let filter = r#"match("c(d)e") | [.string, .offset]"#;
        let input: Value = "abcde".into();
        let val = eval_expr(filter, input).unwrap();
        assert_eq!(format!("{val:?}"), r#"[Array([String("cde"), Number(2)])]"#)
    }

    fn eval_expr(filter: &str, input: Value) -> Result<Vec<Value>> {
        let scope = Arc::new(FuncScope::default());
        let var_scope = VarScope::new();
        let eval = ExprEval::new(scope, input, var_scope);
        let ast = parse_filter(filter).unwrap();
        let rvals = ast.accept(&eval)?.collect();
        rvals
    }
}
