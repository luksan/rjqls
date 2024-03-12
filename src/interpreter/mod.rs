use std::sync::Arc;

use anyhow::{bail, Result};
use smallvec::SmallVec;

use ast_eval::{ExprEval, VarScope};
pub use func_scope::FuncScope;

use crate::parser;
use crate::parser::{JqModule, OwnedFunc, parse_module};
use crate::parser::expr_ast::{Ast, Expr};
use crate::value::{ArcValue, Value};

pub mod ast_eval;
mod bind_var_pattern;
mod generator;

pub type Arity = usize;

mod func_scope {
    use std::borrow::Borrow;
    use std::collections::HashMap;
    use std::fmt::{Debug, Formatter};
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    use crate::interpreter::{Arity, FuncDefArgs, Function};
    use crate::parser::expr_ast::Expr;

    #[derive(Default)]
    pub struct FuncScope<'f> {
        funcs: HashMap<FuncMapKey, Arc<Function<'f>>>,
        parent: Option<Arc<FuncScope<'f>>>,
    }
    impl Clone for FuncScope<'_> {
        fn clone(&self) -> Self {
            let funcs = self.funcs.clone();
            let parent = self.parent.clone();
            Self { funcs, parent }
        }
    }
    impl Debug for FuncScope<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            writeln!(f, "== FuncScope ==")?;
            for (key, func) in self.funcs.iter() {
                writeln!(f, "{}/{}", key.0, func.arity())?;
            }
            if let Some(p) = self.parent.as_ref() {
                write!(f, "{p:?}")?;
            }
            Ok(())
        }
    }

    impl<'f> FuncScope<'f> {
        pub fn new_inner<'fi>(self: &Arc<Self>) -> FuncScope<'fi>
        where
            'f: 'fi,
        {
            FuncScope::<'fi> {
                parent: Some(self.clone()),
                ..Default::default()
            }
        }

        pub fn parent(&self) -> Option<&Arc<FuncScope<'f>>> {
            self.parent.as_ref()
        }

        pub fn push(&mut self, name: String, args: FuncDefArgs, filter: &'f Expr) {
            let func = Function::from_expr(args, filter);
            self.funcs
                .insert(FuncMapKey(name, func.arity()), Arc::new(func));
        }

        pub fn push_arc(&mut self, name: String, func: Arc<Function<'f>>) {
            self.funcs
                .insert(FuncMapKey(name, func.arity()), func.clone());
        }

        pub fn get_func(&self, name: &str, arity: Arity) -> Option<&Arc<Function<'f>>> {
            self.funcs
                .get(&(name, arity) as &dyn MapKeyT)
                .or_else(|| self.parent.as_ref().and_then(|p| p.get_func(name, arity)))
        }
    }

    #[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
    struct FuncMapKey(String, Arity);

    // https://stackoverflow.com/questions/45786717/how-to-implement-hashmap-with-two-keys/45795699#45795699
    trait MapKeyT {
        fn name(&self) -> &str;
        fn arity(&self) -> Arity;
    }

    impl MapKeyT for FuncMapKey {
        fn name(&self) -> &str {
            &self.0
        }

        fn arity(&self) -> Arity {
            self.1
        }
    }
    impl MapKeyT for (&str, Arity) {
        fn name(&self) -> &str {
            self.0
        }

        fn arity(&self) -> Arity {
            self.1
        }
    }

    impl Hash for dyn MapKeyT + '_ {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.name().hash(state);
            self.arity().hash(state);
        }
    }
    impl PartialEq for dyn MapKeyT + '_ {
        fn eq(&self, other: &Self) -> bool {
            self.name() == other.name() && self.arity() == other.arity()
        }
    }
    impl Eq for dyn MapKeyT + '_ {}

    impl<'a> Borrow<dyn MapKeyT + 'a> for FuncMapKey {
        fn borrow(&self) -> &(dyn MapKeyT + 'a) {
            self
        }
    }
}

#[derive(Debug)]
pub struct Function<'e> {
    args: FuncDefArgs,
    filter: &'e Expr,
}
pub type FuncDefArgs = SmallVec<[String; 5]>;
pub type FuncRet = Result<Value>;

impl<'e> Function<'e> {
    pub fn from_expr(args: FuncDefArgs, filter: &'e Expr) -> Function<'e> {
        Function { args, filter }
    }

    pub fn arity(&self) -> Arity {
        self.args.len()
    }

    pub fn filter(&self) -> &'e Expr {
        &self.filter
    }

    pub fn bind<'scope>(
        self: &Arc<Self>,
        name: String,
        func_scope: Arc<FuncScope<'scope>>,
        arguments: &'scope [Expr],
    ) -> Result<BoundFunc<'scope>>
    where
        'e: 'scope,
    {
        if self.arity() != arguments.len() {
            bail!("Function called with incorrect number of arguments")
        }
        let mut func_scope = func_scope.new_inner();
        for (name, arg) in self.args.iter().zip(arguments.iter()) {
            func_scope.push(name.clone(), Default::default(), arg);
        }
        func_scope.push_arc(name, self.clone()); // push ourselves to enable recursion
        Ok(BoundFunc {
            function: self.clone(),
            func_scope: Arc::new(func_scope),
        })
    }
}

#[derive(Debug)]
pub struct BoundFunc<'e> {
    function: Arc<Function<'e>>,
    func_scope: Arc<FuncScope<'e>>,
}

#[derive(Debug)]
pub struct AstInterpreter {
    builtins: Vec<OwnedFunc>,
    root_filter: Ast,
    variables: Arc<VarScope>,
}

impl AstInterpreter {
    pub fn new(code: &str) -> Result<Self> {
        let builtin = Self::load_builtins()?;
        let root_filter = parser::parse_program(code)?;
        let this = Self {
            builtins: builtin.functions,
            root_filter,
            variables: VarScope::new(),
        };
        Ok(this)
    }

    pub fn set_variable(&self, name: String, value: ArcValue) {
        self.variables.set_variable(name.as_str(), value);
    }

    pub fn eval_input(&mut self, input: Value) -> Result<Vec<Value>> {
        let var_scope = self.variables.clone();
        let mut func_scope = FuncScope::default();
        for f in self.builtins.iter() {
            func_scope.push(f.name.clone(), f.args.clone().into(), &f.filter);
        }
        let func_scope = Arc::new(func_scope);
        let eval = ExprEval::new(func_scope.clone(), input.clone(), var_scope);
        let v = self.root_filter.accept(&eval)?;

        v.collect()
    }

    fn load_builtins() -> Result<JqModule> {
        let code = include_str!("../builtins/builtin.jq");
        // let code = include_str!("../builtins/rjqls_builtins.jq");
        parse_module(&code) // TODO implement the complete Jq language
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use super::*;

    /// Parse a Value from JSON data
    fn jval(v: &str) -> Value {
        Value::from_str(v).unwrap()
    }

    #[test]
    fn test_interpret_fn() {
        let mut intr = AstInterpreter::new(
            r#"
       # def x(a; $b): . + a + $b + $b;
       # def foo(f): f|f;
        def addvalue($f): map(. + $f);

        [1,2,3] | addvalue(3)
        # 5|foo(.*2)
        "#,
        )
        .unwrap();

        let x = intr.eval_input(Value::from(1)).unwrap();
        assert_eq!(x[0], Value::from_str("[4.0, 5.0, 6.0]").unwrap())
    }

    mod test_eval {
        use super::*;

        macro_rules! check_value {
            ($test_name:ident, $prog:literal, $input:literal, [$($expect:literal),+]) => {
              #[test]
              fn $test_name() {
                  let mut i = AstInterpreter::new($prog).unwrap();
                  let input = Value::from_str($input).unwrap();
                  let output = i.eval_input(input).unwrap();
                  let expect: Vec<_> = [$($expect)+].into_iter().map(jval).collect();
                  assert_eq!(&output, &expect);
              }
            };
            ($test_name:ident, $prog:literal, [$($expect:literal),+]) => {
              #[test]
              fn $test_name() {
                  let mut i = AstInterpreter::new($prog).unwrap();
                  let input = ().into();
                  let output = i.eval_input(input).unwrap();
                  let expect: Vec<_> = [$($expect),+].into_iter().map(jval).collect();
                  assert_eq!(&output, &expect);
              }
            };
        }
        check_value!(func_prefix, ". | def x: 3; . | x", "null", ["3"]);
        check_value!(func_var_arg, r#"def f($a): $a+1; f(1)"#, ["2.0"]);
        check_value!(
            str_interp,
            r#""x\(1,2)y\(3,4)z" "#,
            ["\"x1y3z\"", "\"x2y3z\"", "\"x1y4z\"", "\"x2y4z\""]
        );

        // FIXME: causes stack overflow
        // check_value!(subs, r#"sub("\\s+"; "")"#, "\"   asd asd  \"", ["asd asd"]);
    }

    #[test]
    fn test_eval_dbg() {
        panic!("Eval will cause stack overflow.");
        /*
        let prog = r#"sub("\\s+"; "")"#;
        let input = jval("\"  asd asd   \"");
        let mut i = AstInterpreter::new(prog).unwrap();
        let v = i.eval_input(input).unwrap();
        assert_eq!(v[0], Value::from(3))
        */
    }
}
