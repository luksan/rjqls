use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Deref;
use std::sync::{Arc, RwLock};

use anyhow::{bail, Context, Result};
use serde_json::Map;

use crate::interpreter::bind_var_pattern::BindVars;
use crate::interpreter::func_scope::FuncScope;
use crate::interpreter::generator::{Generator, ResVal};
use crate::interpreter::Function;
use crate::parser::expr_ast::{Ast, BinOps, Expr, ExprVisitor};
use crate::value::{Value, ValueOps};

struct JqFunc<'expr> {
    fun: Box<dyn FnOnce(&Value) -> ExprResult<'expr> + 'expr>,
}

impl<'e> JqFunc<'e> {
    fn call(self, value: &Value) -> ExprResult<'e> {
        (self.fun)(value)
    }
}

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

    fn get_function<'expr>(&self, name: &str, args: &'expr [Expr]) -> Option<JqFunc<'expr>>
    where
        'f: 'expr,
    {
        let scope = self.func_scope.borrow();
        let func = scope.get_func(name, args.len())?;
        let func: Arc<Function<'expr>> = func.clone();
        let func_scope = scope.clone();
        let var_scope = self.variables.borrow().clone();
        let name = name.to_string();
        let ret = JqFunc {
            fun: Box::new(move |val: &Value| {
                let gen = func.bind(name, func_scope, args, var_scope).unwrap();
                let x = Ok(gen.apply(val)?.collect::<Vec<_>>().into());
                x
            }),
        };
        Some(ret)
    }

    fn get_builtin<'expr>(&self, name: &str, args: &'expr [Expr]) -> Result<JqFunc<'expr>>
    where
        'f: 'expr,
    {
        match (name, args.len()) {
            ("add", 0) => Ok(JqFunc {
                fun: Box::new(|val: &Value| {
                    let mut sum = Value::Null;
                    for v in val.iterate()? {
                        sum = sum.add(v)?;
                    }
                    expr_val_from_value(sum)
                }),
            }),
            ("empty", 0) => Ok(JqFunc {
                fun: Box::new(|_val| Ok(Default::default())),
            }),
            ("length", 0) => Ok(JqFunc {
                fun: Box::new(|val: &Value| expr_val_from_value(val.length()?)),
            }),

            (_, len) => bail!("Function {name}/{len} not found."),
        }
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
        expr_val_from_value(Value::Array(ret.collect::<Result<_>>()?))
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast) -> ExprResult<'e> {
        let vals = vals.accept(self)?;
        for v in vals {
            // TODO this should bifurcate the execution
            BindVars::bind(&v?, vars, self.variables.borrow().deref())?;
        }
        self.input.clone().to_expr_result()
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
                    BinOps::Eq => Ok(Value::Bool(l == r)),
                    BinOps::NotEq => Ok(Value::Bool(l != r)),
                    BinOps::Less => Ok(l.less_than(r)),
                };
                ret.push(r);
            }
        }
        Ok(Generator::from_iter(ret))
    }

    fn visit_call(&self, name: &str, args: &'e [Expr]) -> ExprResult<'e> {
        if let Some(func) = self.get_function(name, args) {
            func.call(&self.input)
        } else {
            self.get_builtin(name, args)?.call(&self.input)
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
        self.input.clone().to_expr_result()
    }

    fn visit_ident(&self, ident: &str) -> ExprResult<'e> {
        expr_val_from_value(Value::String(ident.to_string()))
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
        let mut objects: Vec<Map<String, Value>> = vec![Map::default()];
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
                let Some(n) = values.next() else { break };
                val = n?;
                let obj_len = objects.len();
                objects.extend_from_within(0..obj_cnt);
                obj_slice = &mut objects[obj_len..];
            }
        }
        Ok(objects
            .into_iter()
            .map(|m| Ok(Value::Object(m)))
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
            if let Expr::Literal(Value::String(s)) = part {
                for r in ret.iter_mut() {
                    r.push_str(s);
                }
            } else {
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
                    let Some(next) = values.next() else { break };
                    val = next?;
                    let end = ret.len();
                    ret.extend(prefix.iter().cloned());
                    strings = &mut ret[end..]
                }
            }
        }
        let ret = ret.into_iter().map(|s| Ok(Value::String(s)));
        Ok(Generator::from_iter(ret))
    }

    fn visit_variable(&self, name: &str) -> ExprResult<'e> {
        self.get_variable(name)
    }
}

#[cfg(test)]
mod test {
    use serde_json::to_value;

    use crate::parser::parse_filter;

    use super::*;

    #[test]
    fn test_expr_eval() {
        let array = to_value([1, 2, 3]).unwrap();
        let filter = ". as [$a, $b] | $a + $b";
        let result = eval_expr(filter, array).unwrap();
        for _v in result {
            // println!("{_v},")
        }
    }

    #[test]
    fn test_scope_fail() {
        let filter = "(3 as $a | $a) | $a";
        let err = eval_expr(filter, Value::Null).unwrap_err();
        assert_eq!(&err.to_string(), "Variable 'a' is not defined.")
    }

    #[test]
    fn test_if_else() {
        let filter = r#"if .[] then "hej" elif .[] == false then "hmm" else 4 end"#;
        let input = serde_json::from_str("[1,false,3]").unwrap();
        let val = eval_expr(filter, input).unwrap();
        assert_eq!(
            format!("{val:?}"),
            r#"[String("hej"), Number(4), String("hmm"), Number(4), String("hej")]"#
        )
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
