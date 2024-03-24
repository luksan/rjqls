use std::fmt::Debug;
use std::sync::Arc;

use anyhow::{anyhow, Context, Result};

use crate::interpreter::bind_var_pattern::BindVars;
use crate::interpreter::BoundFunc;
use crate::interpreter::func_scope::FuncScope;
use crate::interpreter::generator::Generator;
use crate::parser::expr_ast::{Ast, AstNode, BinOps, ExprVisitor, ObjectEntry};
use crate::value::{Map, Value, ValueOps};

mod builtins;
mod math;
mod regex;

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("error: {0}")]
    Value(Value),
    #[error("{0}")]
    Anyhow(#[from] anyhow::Error),
}

#[macro_export]
macro_rules! bail {
    ($($args:tt),*) => {
        return Err(EvalError::Anyhow(anyhow!($($args),*)))
    };
}

impl From<Value> for EvalError {
    fn from(value: Value) -> Self {
        Self::Value(value.clone())
    }
}

#[derive(Debug)]
pub struct VarScope<'e> {
    name: Option<&'e str>,
    value: Value,
    parent: Option<Arc<Self>>,
}

impl<'e> VarScope<'e> {
    pub(crate) fn new() -> Arc<Self> {
        Self {
            name: None,
            value: Value::Null,
            parent: None,
        }
        .into()
    }

    fn get_variable(&self, name: &str) -> Option<Value> {
        if self.name == Some(name) {
            Some(self.value.clone())
        } else {
            self.parent.as_ref().and_then(|p| p.get_variable(name))
        }
    }

    pub(crate) fn set_variable<'new>(
        self: &Arc<Self>,
        name: &'new str,
        value: Value,
    ) -> Arc<VarScope<'new>>
    where
        'e: 'new,
    {
        VarScope {
            name: Some(name),
            value,
            parent: Some(self.clone()),
        }
        .into()
    }
}

#[derive(Debug, Clone)]
pub struct ExprEval<'f> {
    input: Value,
    func_scope: Arc<FuncScope<'f>>,
    var_scope: Arc<VarScope<'f>>,
}

impl<'f> ExprEval<'f> {
    pub fn new(func_scope: Arc<FuncScope<'f>>, input: Value, var_scope: Arc<VarScope<'f>>) -> Self {
        Self {
            input,
            func_scope,
            var_scope,
        }
    }

    fn clone_with_input(&self, input: Value) -> Self {
        Self {
            input,
            ..self.clone()
        }
    }

    fn clone_with_func_scope(&self, func_scope: Arc<FuncScope<'f>>) -> Self {
        Self {
            func_scope,
            ..self.clone()
        }
    }

    fn clone_with_var_scope(&self, var_scope: Arc<VarScope<'f>>) -> Self {
        Self {
            var_scope,
            ..self.clone()
        }
    }

    fn get_function<'expr>(&self, name: &str, args: &'expr [AstNode]) -> Option<BoundFunc<'expr>>
    where
        'f: 'expr,
    {
        let scope = &self.func_scope;
        let var_scope = &self.var_scope;
        let (func, func_scope) = scope.get_func(name, args.len())?;
        Some(func.bind(&func_scope, args, scope, var_scope))
    }

    fn get_variable(&self, name: &str) -> ExprResult<'static> {
        Ok(self
            .var_scope
            .get_variable(name)
            .with_context(|| format!("Variable '{name}' is not defined."))
            .into())
    }
}

pub type ExprValue<'e> = Generator<'e>;
pub type ExprResult<'e> = Result<ExprValue<'e>>;
pub type EvalVisitorRet<'e> = Result<Generator<'e>, EvalError>;

fn expr_val_from_value(val: Value) -> EvalVisitorRet<'static> {
    Ok(val.into())
}

impl<'e> ExprVisitor<'e, EvalVisitorRet<'e>> for ExprEval<'e> {
    fn default(&self) -> EvalVisitorRet<'e> {
        panic!("Missing func impl in ExprVisitor for ExprEval.");
    }

    fn visit_alternative(&self, lhs: &'e AstNode, defaults: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self)?;
        let mut ret = vec![];
        for v in lhs {
            let v = v?;
            if v.is_truthy() {
                ret.push(Ok(v))
            }
        }
        if ret.is_empty() {
            return defaults.accept(self);
        }
        Ok(Generator::from_iter(ret.into_iter()))
    }

    fn visit_array(&self, elements: &'e [AstNode]) -> EvalVisitorRet<'e> {
        let mut ret = Generator::empty();
        for e in elements {
            let v = e.accept(self)?;
            ret = ret.chain(v.into_iter());
        }
        // TODO: build array value with a closure
        Ok(Value::from(ret.collect::<Result<Vec<_>>>()?).into())
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast, rhs: &'e Ast) -> EvalVisitorRet<'e> {
        let mut ret = Generator::empty();
        for v in vals.accept(self)? {
            let new_scope = BindVars::bind(&v?, vars, &self.var_scope)?;
            let eval = self.clone_with_var_scope(new_scope);
            ret = ret.chain(rhs.accept(&eval)?);
        }
        Ok(ret)
    }

    fn visit_binop(&self, op: BinOps, lhs: &'e Ast, rhs: &'e Ast) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self)?;
        let mut ret = Vec::new(); // TODO generator
        for l in lhs {
            let l = &l?;
            let rhs = rhs.accept(self)?;
            for r in rhs {
                let r = &r?;

                macro_rules! cmp {
                    ($op:tt) => {Ok(Value::from(l $op r))};
                }
                let r = match op {
                    BinOps::Add => l.add(r),
                    BinOps::Sub => l.sub(r),
                    BinOps::Mul => l.mul(r),
                    BinOps::Div => l.div(r),

                    BinOps::Eq => cmp!(==),
                    BinOps::NotEq => cmp!(!=),
                    BinOps::Less => cmp!(<),
                    BinOps::LessEq => cmp!(<=),
                    BinOps::Greater => cmp!(>),
                    BinOps::GreaterEq => cmp!(>=),

                    BinOps::And => Ok(Value::from(l.is_truthy() && r.is_truthy())),
                    BinOps::Or => Ok(Value::from(l.is_truthy() || r.is_truthy())),

                    op => unimplemented!("{op:?}"),
                };
                ret.push(r);
            }
        }
        Ok(Generator::from_iter(ret))
    }

    fn visit_breakpoint(&self, expr: &'e Ast) -> EvalVisitorRet<'e> {
        println!("{:?}", self.func_scope.as_ref());
        println!("{:?}", self.var_scope.as_ref());
        expr.accept(self)
    }

    fn visit_call(&self, name: &str, args: &'e [AstNode]) -> EvalVisitorRet<'e> {
        if let Some(bound_func) = self.get_function(name, args) {
            let eval = ExprEval::new(
                bound_func.func_scope,
                self.input.clone(),
                bound_func.function.var_scope.clone(),
            );
            bound_func.function.filter.accept(&eval)
        } else {
            Ok(self.get_builtin(name, args)?)
        }
    }

    fn visit_comma(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self)?;
        let rhs = rhs.accept(self)?;
        Ok(lhs.chain(rhs))
    }

    fn visit_define_function(
        &self,
        name: &str,
        args: &'e [String],
        body: &'e AstNode,
        rhs: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        let mut scope = self.func_scope.new_inner();
        let var_scope = &self.var_scope;
        scope.push(name.to_owned(), args.into(), body, None, var_scope);
        let eval = self.clone_with_func_scope(Arc::new(scope));
        rhs.accept(&eval)
    }

    fn visit_dot(&self) -> EvalVisitorRet<'e> {
        Ok(self.input.clone().into())
    }

    fn visit_ident(&self, ident: &str) -> EvalVisitorRet<'e> {
        Ok(Value::from(ident).into())
    }

    fn visit_if_else(&self, cond: &'e [AstNode], branches: &'e [AstNode]) -> EvalVisitorRet<'e> {
        let ret = Default::default();
        fn check_remaining<'g>(
            this: &ExprEval<'g>,
            mut ret: Generator<'g>,
            cond: &'g [AstNode],
            branches: &'g [AstNode],
        ) -> EvalVisitorRet<'g> {
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
    fn visit_index(&self, expr: &'e AstNode, idx: Option<&'e AstNode>) -> EvalVisitorRet<'e> {
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

    fn visit_literal(&self, lit: &Value) -> EvalVisitorRet<'e> {
        Ok(lit.clone().into())
    }

    fn visit_object(&self, entries: &'e [ObjectEntry]) -> EvalVisitorRet<'e> {
        let visit_obj_entry = |e: &'e ObjectEntry| -> EvalVisitorRet<'e> {
            let (key, value) = (&e.key, &e.value);
            let mut key_gen = key.accept(self)?;
            let val = value.accept(self)?;
            let key = key_gen.next().unwrap();
            let mut ret = vec![key];
            ret.extend(val);
            Ok(ret.into())
        };

        let mut objects: Vec<Map> = vec![Map::default()];
        for e in entries {
            let mut keyvals = visit_obj_entry(e)?;
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

    fn visit_labeled_pipe(
        &self,
        label: &'e str,
        lhs: &'e AstNode,
        rhs: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        // TODO: implement "break"
        let lhs = lhs.accept(self)?;
        let mut ret = Generator::empty();
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value?;
            ret = ret.chain(rhs.accept(&rhs_eval)?);
        }
        Ok(ret)
    }

    fn visit_pipe(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self)?;
        let mut ret = Generator::empty();
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value?;
            ret = ret.chain(rhs.accept(&rhs_eval)?);
        }
        Ok(ret)
    }

    fn visit_reduce(
        &self,
        input_expr: &'e AstNode,
        var: &'e str,
        init: &'e AstNode,
        update: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        let input = input_expr.accept(self)?;
        let Some(init) = init.accept(self)?.next() else {
            return Ok(Generator::empty());
        };
        let mut update_eval = self.clone_with_input(init?);
        for v in input {
            update_eval.var_scope = self.var_scope.set_variable(var, v?);
            update_eval.input = update.accept(&update_eval)?.next().unwrap()?;
        }
        Ok(update_eval.input.into())
    }

    fn visit_scope(&self, inner: &'e AstNode) -> EvalVisitorRet<'e> {
        inner.accept(self)
    }

    fn visit_slice(
        &self,
        expr: &'e AstNode,
        start: Option<&'e AstNode>,
        end: Option<&'e AstNode>,
    ) -> EvalVisitorRet<'e> {
        let val = expr.accept(self)?;
        let mut ret = vec![];
        // TODO: lazy eval
        for v in val {
            let v = v?;
            let start = if let Some(start) = start {
                start.accept(self)?
            } else {
                expr_val_from_value(Value::from(0))?
            };
            for s in start {
                let s = s?;
                let end = if let Some(end) = end {
                    end.accept(self)?
                } else {
                    expr_val_from_value(Value::from(v.length()?))?
                };
                for e in end {
                    ret.push(v.slice(&s, &e?));
                }
            }
        }
        Ok(Generator::from_iter(ret.into_iter()))
    }

    fn visit_string_interp(&self, parts: &'e [AstNode]) -> EvalVisitorRet<'e> {
        let mut ret: Vec<String> = vec!["".to_owned()];
        for part in parts {
            let values = part.accept(self)?.collect::<Result<Vec<_>>>()?;
            if values.is_empty() {
                return Ok(Generator::empty());
            };
            let val_cnt = values.len();
            let prefix_len = ret.len();
            for _ in 1..val_cnt {
                // duplicate the prefix if the expression returned more than one value
                ret.extend_from_within(..prefix_len);
            }
            let mut prefix_offset = 0;
            for val in values {
                let (val_string, val_str);
                if let Some(val) = val.as_str() {
                    val_str = val;
                } else {
                    val_string = val.to_string();
                    val_str = val_string.as_str();
                }
                for s in &mut ret[prefix_offset..prefix_offset + prefix_len] {
                    s.push_str(val_str);
                }
                prefix_offset += prefix_len;
            }
        }
        let ret = ret.into_iter().map(|s| Ok(s.into()));
        Ok(Generator::from_iter(ret))
    }

    fn visit_try_catch(
        &self,
        try_expr: &'e AstNode,
        catch_expr: Option<&'e AstNode>,
    ) -> EvalVisitorRet<'e> {
        let maybe = try_expr.accept(self);
        match (catch_expr, maybe) {
            (Some(catch_expr), Err(e)) => {
                let val = match e {
                    EvalError::Value(v) => v,
                    EvalError::Anyhow(a) => a.to_string().into(),
                };
                catch_expr.accept(&self.clone_with_input(val))
            }
            (_, m) => m,
        }
    }

    fn visit_variable(&self, name: &str) -> EvalVisitorRet<'e> {
        Ok(self.get_variable(name)?)
    }
}

#[cfg(test)]
mod ast_eval_test {
    use std::str::FromStr;

    use crate::parser::parse_program;

    use super::*;

    macro_rules! one_test {
        ($test_name:ident, $filter:literal, $($input:literal,)? [$($expect:literal),*]) => {
              #[test]
              fn $test_name() {
                  let input = if false {unreachable!()} $(else if true { Value::from_str($input).unwrap() })? else { Value::Null };
                  let output = eval_expr($filter, input).expect("eval_expr() error");
                  let expect: Vec<_> = [$($expect),*].into_iter().map(|v|Value::from_str(v).unwrap()).collect();
                  assert_eq!(&output, &expect);
            }
        };
    }

    macro_rules! ast_eval_tests {
        ($([$test_name:ident, $filter:literal,$input:literal, $expect_one:literal]$(,)?)+) => {
            $( one_test!($test_name, $filter, $input, [$expect_one]); )+
        };
    }

    macro_rules! test_multiple_outputs {
        ($([$test_name:ident, $filter:literal, $($input:literal,)? [$($expect:literal),*]])+) => {
            $( one_test!($test_name, $filter, $($input,)? [$($expect),*]); )+
        };
    }

    test_multiple_outputs![
        [empty, ".[] | empty", "[1,2,3]", []]
        [error_empty, "try error(empty) catch 4", []]
    ];

    ast_eval_tests![
        [breakpoint, "§. | .", "1", "1"]
        [expr_eval, ".", "1", "1"]
        [error_0, "try error catch .", "1", "1"]
        [error_1, "try error(2) catch .", "null", "2"]
        [error_obj, "try error({a: 1}) catch .a", "null", "1"]
        [err_seq, "try error(1,2,3) catch .", "null", "1"]
        [err_seq2, "[.[]|try if . > 3 then error(0.5) else . end catch .]", "[1,3,5,2]", "[1,3,0.5,2]"]

        [func_def, r#"def a(s): . + s + .; .| a("3")"#, "\"2\"", "\"232\""]
        [func_redef, r#"def a: 1; def b: a; def a: "function scope error"; b"#, "0", "1"]
        [func_def_nested, r#"def a(s): def b: s + .; b + 1; . | a(2)"#, "0", "3"]
        [func_def_scope, ". + def f:3;f | f", "1", "4"]
        [func_complex_scope, r#"def a:"first "; def b(x):a + x; def a: "second"; b(a)"#, "0", "\"first second\""]
        [func_var_arg_name, r#"[ def a(a; $a): a, $a, def a: "inner"; a, $a; a("arg"; "var") ] "#,"null", r#"["var", "var", "inner", "var"]"#]
        [if_else, r#"[ if .[] then "hej" elif .[] == false then "hmm" else 4 end ]"#, "[1,false,3]", r#"["hej", 4, "hmm", 4, "hej"]"# ]
        [include, r#"include "tests/test_include.jq"; func_a"#, "null", "1"]
        [var_bind, ". as [$a, $b] | $a + $b", "[1,2,3]", "3"]
        [var_bind_term, "[.[]|.+1 as $v|.]", "[1,4,5,3]", "[2,8,10,6]"] // https://github.com/jqlang/jq/issues/2446
        [var_scope, r#"[. as $a|$a|def a: $a | .+" func" as $a|$a; "out" as $a| a,., $a]"#, "\"in\"", r#"["in func", "in", "out"]"#]
        [var_scope2, r#"[. as $a|$a|def f: $a | .+" func" as $b|$b; "out" as $c| f,$a, $c]"#, "\"in\"", r#"["in func", "in", "out"]"#]
        [var_gen, "[1,2,3 as $a | $a]", "null", "[1,2,3]"]
        [redef_literal, "def false: true; false", "null", "false"]
        [reduce, "reduce .[] as $a (0; $a + .)", "[1,2,3,4,5,6]", "21"]
        [slice_array, ".[1:3]", "[1,2,3,4,5,6]", "[2,3]"]
        [split_1, r#"split(" ")"#, "\"a b c de \"", r#"["a","b","c","de",""]"#]
        [str_iterp_comma, r#"["a\(1,2)b\(3)"]"#, "null", "[\"a1b3\", \"a2b3\"]"]
    ];

    #[test]
    fn test_scope_fail() {
        let filter = "(3 as $a | $a) | $a";
        let err = eval_expr(filter, ().into()).unwrap_err();
        assert_eq!(&err.to_string(), "Variable 'a' is not defined.")
    }

    #[test]
    fn test_scope_fail_func() {
        let filter = "(def a:.;.) | a";
        let err = eval_expr(filter, ().into()).unwrap_err();
        assert_eq!(&err.to_string(), "Function a/0 not found.")
    }

    fn eval_expr(filter: &str, input: Value) -> Result<Vec<Value>> {
        let scope = Arc::new(FuncScope::default());
        let var_scope = VarScope::new();
        let eval = ExprEval::new(scope, input, var_scope);
        let ast = parse_program(filter).unwrap();
        let ret = ast.accept(&eval)?.collect();
        ret // need to bind ret to variable, otherwise ast doesn't live long enough
    }
}
