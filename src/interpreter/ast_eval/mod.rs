use std::fmt::Debug;
use std::sync::Arc;

use anyhow::{Context, Result};

use crate::interpreter::bind_var_pattern::BindVars;
use crate::interpreter::BoundFunc;
use crate::interpreter::func_scope::FuncScope;
use crate::interpreter::generator::{Generator, ResVal};
use crate::parser::expr_ast::{Ast, AstNode, BinOps, BreakLabel, ExprVisitor, FuncDef, ObjectEntry};
use crate::value::{Map, Value, ValueOps};

mod builtins;
mod math;
mod regex;

#[derive(Debug, thiserror::Error)]
pub enum EvalError {
    #[error("error: {0}")]
    Value(Value),
    #[error("{0} is not defined")]
    Break(BreakLabel),
    #[error("{0}")]
    Anyhow(#[from] anyhow::Error),
}

#[macro_export]
macro_rules! bail {
    ($($args:tt),*) => {
        return EvalError::Anyhow(anyhow::anyhow!($($args),*)).into()
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

    pub fn visit(&self, ast: &'f AstNode) -> Result<Vec<Value>> {
        Ok(ast.accept(self).collect::<CollectVecResult>()?)
    }

    pub fn visit_with_input(&self, ast: &'f AstNode, input: Value) -> Result<Vec<Value>> {
        let x = self.clone_with_input(input);
        x.visit(ast)
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
        self.func_scope
            .get_func(name, args.len())
            .map(|(func, func_scope)| {
                func.bind(func_scope, args, &self.func_scope, &self.var_scope)
            })
    }

    fn get_variable(&self, name: &str) -> Result<Value> {
        self.var_scope
            .get_variable(name)
            .with_context(|| format!("Variable '{name}' is not defined."))
    }
}

pub type EvalVisitorRet<'e> = Generator<'e>;
type CollectVecResult = Result<Vec<Value>, EvalError>;

impl<'e> ExprVisitor<'e, EvalVisitorRet<'e>> for ExprEval<'e> {
    fn default(&self) -> EvalVisitorRet<'e> {
        panic!("Missing func impl in ExprVisitor for ExprEval.");
    }

    fn visit_alternative(&self, lhs: &'e AstNode, defaults: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self);
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
        Generator::from_iter(ret)
    }

    fn visit_array(&self, elements: &'e [AstNode]) -> EvalVisitorRet<'e> {
        let mut ret = Generator::empty();
        for e in elements {
            let v = e.accept(self);
            ret = ret.chain_gen(v.into_iter());
        }
        // TODO: build array value with a closure
        Value::from(ret.collect::<CollectVecResult>()?).into()
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast, rhs: &'e Ast) -> EvalVisitorRet<'e> {
        let mut ret = Generator::empty();
        for v in vals.accept(self) {
            let new_scope = BindVars::bind(&v?, vars, &self.var_scope)?;
            let eval = self.clone_with_var_scope(new_scope);
            ret = ret.chain_gen(rhs.accept(&eval));
        }
        ret
    }

    fn visit_binop(&self, op: BinOps, lhs: &'e Ast, rhs: &'e Ast) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self);
        let mut ret = Vec::new(); // TODO generator
        for l in lhs {
            let l = &l?;
            match op {
                // Short-circuit and/or
                BinOps::And if !l.is_truthy() => {
                    ret.push(Ok(false.into()));
                    continue;
                }
                BinOps::Or if l.is_truthy() => {
                    ret.push(Ok(true.into()));
                    continue;
                }
                _ => {} // check rhs
            }
            let rhs = rhs.accept(self);
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

                    BinOps::And | BinOps::Or => Ok(r.is_truthy().into()),

                    op => unimplemented!("{op:?}"),
                };
                ret.push(r.map_err(|e| e.into()));
            }
        }
        Generator::from_iter(ret)
    }

    fn visit_breakpoint(&self, expr: &'e Ast) -> EvalVisitorRet<'e> {
        println!("Breakpoint hit at {:?}", expr);
        println!("Current input: {:?}", self.input);
        print!("FuncScope:\n{:?}", self.func_scope.as_ref());
        println!("{:?}", self.var_scope.as_ref());
        println!("> Continuing <\n");
        expr.accept(self)
    }

    fn visit_call(&self, name: &str, args: &'e [AstNode]) -> EvalVisitorRet<'e> {
        if let Some(bound_func) = self.get_function(name, args) {
            let eval = ExprEval::new(
                bound_func.func_scope,
                self.input.clone(),
                bound_func.function.var_scope.clone(),
            );
            // bound_func.function.filter.accept(&eval)
            Generator::from_accept(eval, bound_func.function.filter)
        } else {
            self.get_builtin(name, args) // TODO: rename to call_builtin()
        }
    }

    fn visit_comma(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self);
        let rhs = rhs.accept(self);
        lhs.chain_gen(rhs)
    }

    fn visit_func_scope(&self, funcs: &'e [FuncDef], rhs: &'e AstNode) -> EvalVisitorRet<'e> {
        let mut scope = self.func_scope.clone();
        let var_scope = &self.var_scope;
        for f in funcs {
            scope = scope.push_func_def(f, var_scope);
        }
        let eval = self.clone_with_func_scope(scope);
        rhs.accept(&eval)
    }

    fn visit_dot(&self) -> EvalVisitorRet<'e> {
        self.input.clone().into()
    }

    fn visit_ident(&self, ident: &str) -> EvalVisitorRet<'e> {
        Value::from(ident).into()
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
                ret = ret.chain_gen(branches[0].accept(this));
                return ret;
            }
            let vals = cond[0].accept(this);
            for v in vals {
                let v = v?;
                if v.is_truthy() {
                    ret = ret.chain_gen(branches[0].accept(this));
                } else {
                    ret = check_remaining(this, ret, &cond[1..], &branches[1..]);
                }
            }
            ret
        }
        check_remaining(self, ret, cond, branches)
    }

    // array or object index
    fn visit_index(&self, expr: &'e AstNode, idx: Option<&'e AstNode>) -> EvalVisitorRet<'e> {
        let e = expr
            .accept(self)
            .with_context(|| format!("Eval of expr for indexing failed {expr:?}"));
        let Some(idx) = idx else {
            // iterate all values
            let mut ret = Vec::new();
            for v in e {
                ret.extend(v?.iterate()?.cloned().map(Ok));
            }
            return ret.into();
        };
        let mut ret = Vec::new();
        for v in e {
            let v = &v?;
            let idx = idx.accept(self).context("Index failed to evaluate");
            for i in idx {
                let i = &i?;
                let val = v
                    .index(i)
                    .with_context(|| format!("Failed to index {v} with {i}."))
                    .map_err(|e| e.into());
                ret.push(val);
            }
        }
        ret.into()
    }

    fn visit_literal(&self, lit: &Value) -> EvalVisitorRet<'e> {
        lit.clone().into()
    }

    fn visit_object(&self, entries: &'e [ObjectEntry]) -> EvalVisitorRet<'e> {
        let visit_obj_entry = |e: &'e ObjectEntry| -> EvalVisitorRet<'e> {
            let (key, value) = (&e.key, &e.value);
            let mut key_gen = key.accept(self);
            let val = value.accept(self);
            let key = key_gen.next()?;
            let mut ret = vec![key];
            ret.extend(val);
            ret.into()
        };

        let mut objects: Vec<Map> = vec![Map::default()];
        for e in entries {
            let mut keyvals = visit_obj_entry(e);
            let key = keyvals.next()??;
            let key = key.as_str().context("Object key must be a string")?;
            let mut values = keyvals;

            let obj_cnt = objects.len();

            let mut val = values.next()??;
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
        objects
            .into_iter()
            .map(|m| Ok(Value::from(m)))
            .collect::<Vec<_>>()
            .into()
    }

    fn visit_break(&self, name: &'e BreakLabel) -> EvalVisitorRet<'e> {
        Generator::from_break(name.clone())
    }

    fn visit_labeled_pipe(
        &self,
        label: &'e BreakLabel,
        lhs: &'e AstNode,
        rhs: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self);
        let mut ret = Generator::empty();
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value?;
            ret = ret.chain_break(rhs.accept(&rhs_eval), label.clone());
        }
        ret
    }

    fn visit_pipe(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> EvalVisitorRet<'e> {
        let lhs = lhs.accept(self);
        let mut ret = Generator::empty();
        let mut rhs_eval = self.clone();
        for value in lhs {
            rhs_eval.input = value?;
            ret = ret.chain_gen(rhs.accept(&rhs_eval));
        }
        ret
    }

    fn visit_foreach(
        &self,
        input: &'e AstNode,
        var: &'e str,
        init: &'e AstNode,
        update: &'e AstNode,
        extract: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        // foreach input as $var (init; update; extract)
        let this = self.clone();
        let g = init
            .accept(self)
            .map(move |init| -> Generator<'e> {
                let mut update_eval = this.clone_with_input(init?);
                let var_scope = this.var_scope.clone();
                let extract = input.accept(&this).map(move |inp| -> Generator<'e> {
                    let inp = inp?;
                    update_eval.var_scope = var_scope.set_variable(var, inp);
                    update_eval.input = update.accept(&update_eval).last()??;
                    extract.accept(&update_eval)
                });
                Generator::from_iter(extract.flatten())
            })
            .flatten();
        Generator::from_iter(g)
    }

    fn visit_reduce(
        &self,
        input_expr: &'e AstNode,
        var: &'e str,
        init: &'e AstNode,
        update: &'e AstNode,
    ) -> EvalVisitorRet<'e> {
        // reduce input as $var (init; update)
        let input = input_expr.accept(self);
        let init = init.accept(self).next()??;
        let mut update_eval = self.clone_with_input(init);
        for v in input {
            update_eval.var_scope = self.var_scope.set_variable(var, v?);
            update_eval.input = update.accept(&update_eval).last()??;
        }
        update_eval.input.into()
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
        let val = expr.accept(self);
        let mut ret = vec![];
        // TODO: lazy eval
        for v in val {
            let v = v?;
            let start = if let Some(start) = start {
                start.accept(self)
            } else {
                Value::from(0).into()
            };
            for s in start {
                let s = s?;
                let end = if let Some(end) = end {
                    end.accept(self)
                } else {
                    Value::from(v.length()?).into()
                };
                for e in end {
                    ret.push(v.slice(&s, &e?).map_err(|e| e.into()));
                }
            }
        }
        Generator::from_iter(ret)
    }

    fn visit_string_interp(&self, parts: &'e [AstNode]) -> EvalVisitorRet<'e> {
        let mut ret: Vec<String> = vec!["".to_owned()];
        for part in parts {
            let values = part.accept(self).collect::<CollectVecResult>()?;
            if values.is_empty() {
                return Generator::empty();
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
        Generator::from_iter(ret)
    }

    fn visit_try_catch(
        &self,
        try_expr: &'e AstNode,
        catch_expr: Option<&'e AstNode>,
    ) -> EvalVisitorRet<'e> {
        let try_gen = try_expr.accept(self);
        struct TryCatch<'e> {
            try_gen: Generator<'e>,
            catch_gen: Option<Generator<'e>>,
            catch_expr: Option<&'e AstNode>,
            eval: ExprEval<'e>,
        }
        impl<'e> Iterator for TryCatch<'e> {
            type Item = ResVal;

            fn next(&mut self) -> Option<Self::Item> {
                if let Some(catch) = self.catch_gen.as_mut() {
                    return catch.next();
                }
                let t = self.try_gen.next();
                let Some(Err(e)) = t else { return t };
                let Some(catch_expr) = self.catch_expr.take() else {
                    return None;
                };
                let val = match e {
                    EvalError::Value(v) => v,
                    // This is how jq does it, but maybe try/catch shouldn't affect break
                    EvalError::Break(label) => label.into(),
                    EvalError::Anyhow(a) => a.to_string().into(),
                };
                self.eval.input = val;
                self.try_gen = catch_expr.accept(&self.eval);
                self.next()
            }
        }
        Generator::from_iter(TryCatch {
            try_gen,
            catch_gen: None,
            catch_expr,
            eval: self.clone(),
        })
    }

    fn visit_variable(&self, name: &str) -> EvalVisitorRet<'e> {
        self.get_variable(name)?.into()
    }
}

#[cfg(test)]
mod ast_eval_test {
    use std::str::FromStr;

    use crate::parser::parse_program;
    use crate::src_reader::test_src_reader;

    use super::*;

    macro_rules! one_test {
        ($test_name:ident, $filter:literal, $($input:literal,)? [$($expect:literal),*]) => {
              #[test]
              fn $test_name() {
                  let input = if false {unreachable!()} $(else if true { Value::from_str($input).unwrap() })? else { Value::Null };
                  let output = eval_expr($filter, input).expect("eval_expr() error");
                  let expect: Vec<_> = [$($expect),*].into_iter().map(|v|Value::from_str(v).unwrap()).collect();
                  assert_eq!(&output, &expect, "Output didn't match reference (right)");
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
        [obj_empty_key, r#"{a: 3, (empty): 3}"#, []]
        [obj_empty_val, "{a: 3, b: empty}", []]
        [or_short_ckt, "true or empty",["true"]]
        [and_short_ckt, "(1, false, 2) and (1,2)", ["true","true","false","true","true"]]

        [label_first, "label $out | 1 | ., break $out", ["1"]]
        [foreach_1, "foreach .[] as $item (0; . + $item; [$item, . * 2])", "[1,2,3]", ["[1,2]", "[2,6]","[3,12]"]]

        [tail_recursion, "def a($x): if $x > 0 then a($x-1) else empty end; a(3000)", []]

        // builtins
        [range, "range(1,2;3,4)", ["1","2","1","2","3","2","2","3"]]
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
        [include, r#"include "tests/test_include.jq"; func_b"#, "null", "2"]
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
    fn test_undef_break() {
        let filter = "label $b | try break $a catch . ";
        let err = eval_expr(filter, ().into()).unwrap_err();
        assert!(err
            .root_cause()
            .to_string()
            .contains("$*label-a is not defined"))
    }

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
        let ast = parse_program(filter, &mut test_src_reader())?;
        eval.visit(&ast)
    }

    #[test]
    fn test_error_propagation() {
        let filter = "true, error(true), false,error(false)";
        let scope = Arc::new(FuncScope::default());
        let var_scope = VarScope::new();
        let eval = ExprEval::new(scope, Value::Null, var_scope);
        let ast = parse_program(filter, &mut test_src_reader()).unwrap();
        let res = ast.accept(&eval).collect::<Vec<_>>();
        assert_eq!(res.len(), 2);
        assert!(res[0].is_ok());
        assert!(res[1].is_err());
    }
}
