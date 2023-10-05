use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::sync::{Arc, RwLock};

use anyhow::{bail, Context, Result};
use serde_json::Map;
use smallvec::SmallVec;

use crate::interpreter::bind_var_pattern::BindVars;
use crate::parser::ast::{Ast, BinOps, Expr, ExprVisitor, Value};
use crate::parser::parse_filter;
use crate::value::ValueOps;

pub fn eval(input: &str, filter: &str) -> Result<Vec<Value>> {
    let ast = parse_filter(filter)?;
    let input: Value = serde_json::from_str(input)?;
    eval_parsed(input, &ast)
}

pub fn eval_parsed(input: Value, filter: &Expr) -> Result<Vec<Value>> {
    let evaluator = ExprEval::new(input);
    let vals = filter.accept(&evaluator)?;
    Ok(Vec::from_iter(vals))
}

struct JqFunc<'expr> {
    fun: Box<dyn Fn(&Value) -> ExprResult + 'expr>,
}

impl JqFunc<'_> {
    fn call(&self, value: &Value) -> ExprResult {
        (self.fun)(value)
    }
}

#[derive(Debug)]
pub struct VarScope {
    entries: RwLock<HashMap<String, ExprValue>>,
    parent: Option<Arc<Self>>,
}

impl VarScope {
    fn new() -> Arc<Self> {
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

    fn get_variable(&self, name: &str) -> ExprResult {
        let entries = self.entries.read().unwrap();
        if let Some(val) = entries.get(name) {
            return Ok(val.clone());
        }
        match self.get_parent() {
            None => bail!("Variable ${name} is not defined."),
            Some(p) => p.get_variable(name),
        }
    }
    pub(crate) fn set_variable(&self, name: &str, value: ExprValue) {
        let mut entries = self.entries.write().unwrap();
        entries.insert(name.to_owned(), value);
    }
}

#[derive(Debug, Clone)]
pub struct ExprEval {
    input: Value,
    variables: RefCell<Arc<VarScope>>,
}

impl ExprEval {
    pub fn new(input: Value) -> Self {
        Self {
            input,
            variables: VarScope::new().into(),
        }
    }
    fn get_function<'expr>(&self, name: &str, args: &[&'expr Expr]) -> Result<JqFunc<'expr>> {
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
            ("length", 0) => Ok(JqFunc {
                fun: Box::new(|val: &Value| expr_val_from_value(val.length()?)),
            }),
            ("select", 1) => {
                let arg = args[0];
                Ok(JqFunc {
                    fun: Box::new(|val: &Value| {
                        let eval = ExprEval::new(val.clone());
                        let vals = arg.accept(&eval)?;
                        let mut ret = SmallVec::new();
                        for bool in vals.iter().map(|v| v.is_truthy()) {
                            if bool {
                                ret.push(val.clone());
                            }
                        }
                        Ok(ret)
                    }),
                })
            }
            ("map", 1) => {
                let filter = args[0];
                Ok(JqFunc {
                    fun: Box::new(|val: &Value| {
                        let mut ret = Vec::new();
                        let mut eval = ExprEval::new(Value::Null);
                        for v in val.iterate()? {
                            eval.input = v.clone();
                            let vals = filter.accept(&eval)?;
                            ret.extend(vals.into_iter());
                        }
                        expr_val_from_value(Value::Array(ret))
                    }),
                })
            }

            (_, len) => bail!("Function {name}/{len} not found."),
        }
    }

    fn get_variable(&self, name: &str) -> ExprResult {
        self.variables.borrow().get_variable(name)
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
}

pub type ExprValue = SmallVec<[Value; 2]>;
pub type ExprResult = Result<ExprValue>;

fn expr_val_from_value(val: Value) -> ExprResult {
    Ok(SmallVec::from_elem(val, 1))
}
impl ExprVisitor<ExprResult> for ExprEval {
    fn default(&self) -> ExprResult {
        panic!();
    }

    fn visit_array(&self, elements: &[Expr]) -> ExprResult {
        let mut ret = Vec::with_capacity(elements.len());
        for e in elements {
            let v = e.accept(self)?;
            ret.extend(v.into_iter());
        }
        expr_val_from_value(Value::Array(ret))
    }

    fn visit_bind_vars(&self, vals: &Ast, vars: &Ast) -> ExprResult {
        let vals = vals.accept(self)?;
        for v in vals {
            // TODO this should bifurcate the execution
            BindVars::bind(&v, vars, self.variables.borrow().deref())?;
        }
        self.input.clone().to_expr_result()
    }

    fn visit_binop(&self, op: BinOps, lhs: &Ast, rhs: &Ast) -> ExprResult {
        let lhs = lhs.accept(self)?;
        let rhs = rhs.accept(self)?;
        let mut ret = SmallVec::with_capacity(lhs.len() + rhs.len());
        for l in lhs.iter() {
            for r in rhs.iter() {
                let r = match op {
                    BinOps::Add => l.add(r),
                    BinOps::Sub => l.sub(r),
                    BinOps::Mul => l.mul(r),
                    BinOps::Div => l.div(r),
                    BinOps::Eq => Ok(Value::Bool(l == r)),
                    BinOps::NotEq => Ok(Value::Bool(l != r)),
                };
                ret.push(r?);
            }
        }
        Ok(ret)
    }

    fn visit_call(&self, name: &Expr, args: Option<&Expr>) -> ExprResult {
        let name = name.accept(self)?;
        assert_eq!(name.len(), 1);
        let mut arg_vec: SmallVec<[_; 1]> = SmallVec::with_capacity(1);

        if let Some(args) = args {
            arg_vec.push(args)
        }
        self.get_function(name[0].as_str().unwrap(), &arg_vec)?
            .call(&self.input)
    }

    fn visit_comma(&self, lhs: &Expr, rhs: &Expr) -> ExprResult {
        let mut lhs = lhs.accept(self)?;
        let mut rhs = rhs.accept(self)?;
        lhs.append(&mut rhs);
        Ok(lhs)
    }

    fn visit_dot(&self) -> ExprResult {
        self.input.clone().to_expr_result()
    }

    fn visit_ident(&self, ident: &str) -> ExprResult {
        expr_val_from_value(Value::String(ident.to_string()))
    }
    // array or object index
    fn visit_index(&self, expr: &Expr, idx: Option<&Expr>) -> ExprResult {
        let e = expr
            .accept(self)
            .with_context(|| format!("Eval of expr for indexing failed {expr:?}"))?;
        let Some(idx) = idx else {
            // iterate all values
            let mut ret = SmallVec::new();
            for v in e {
                ret.extend(v.iterate()?.cloned());
            }
            return Ok(ret);
        };
        let idx = idx.accept(self).context("Index failed to evaluate")?;
        let mut ret = SmallVec::with_capacity(e.len() * idx.len());
        for v in e {
            for i in idx.iter() {
                let val = v
                    .index(i)
                    .with_context(|| format!("Failed to index {v} with {i}."))?;
                ret.push(val);
            }
        }
        Ok(ret)
    }

    fn visit_literal(&self, lit: &Value) -> ExprResult {
        expr_val_from_value(lit.clone())
    }

    fn visit_object(&self, members: &[Expr]) -> ExprResult {
        let mut objects: Vec<Map<String, Value>> = vec![Map::default()];
        for member in members {
            assert!(matches!(member, Expr::ObjectEntry { .. }));
            let keyvals = member.accept(self)?;
            let key: &str = keyvals[0].as_str().context("Object key must be a string")?;
            let mut values = keyvals[1..].iter();

            let obj_cnt = objects.len();

            let mut val = values.next().unwrap();
            let mut obj_slice = &mut objects[0..];
            loop {
                for o in obj_slice {
                    o.insert(key.to_string(), val.clone());
                }
                let Some(n) = values.next() else { break };
                val = n;
                let obj_len = objects.len();
                objects.extend_from_within(0..obj_cnt);
                obj_slice = &mut objects[obj_len..];
            }
        }
        Ok(objects.into_iter().map(Value::Object).collect())
    }

    fn visit_obj_entry(&self, key: &Expr, value: &Expr) -> ExprResult {
        let key = key.accept(self)?;
        let mut val = value.accept(self)?;
        assert_eq!(key.len(), 1);
        let mut ret = SmallVec::from_elem(key.into_iter().next().unwrap(), 1);
        ret.append(&mut val);
        Ok(ret)
    }

    fn visit_pipe(&self, lhs: &Expr, rhs: &Expr) -> ExprResult {
        let lhs = lhs.accept(self)?;
        let mut ret = SmallVec::with_capacity(lhs.len());
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value;
            ret.append(&mut rhs.accept(&rhs_eval)?);
        }
        Ok(ret)
    }

    fn visit_variable(&self, name: &str) -> ExprResult {
        self.get_variable(name)
    }

    fn visit_scope(&self, inner: &Expr) -> ExprResult {
        self.begin_scope();
        let r = inner.accept(self);
        self.end_scope();
        r
    }
}

#[cfg(test)]
mod test {
    use serde_json::to_value;

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
        assert_eq!(&err.to_string(), "Variable $a is not defined.")
    }

    fn eval_expr(filter: &str, input: Value) -> ExprResult {
        let eval = ExprEval::new(input);
        let ast = parse_filter(filter).unwrap();
        ast.accept(&eval)
    }
}
