use std::ops::Deref;
use std::sync::Arc;

use anyhow::{bail, Result};
use smallvec::SmallVec;

pub use func_scope::FuncScope;

use crate::parser;
use crate::parser::expr_ast::{Ast, Expr};
use crate::parser::{parse_module, JqModule};
use crate::value::Value;
use ast_eval::{ExprEval, ExprResult, VarScope};

pub mod ast_eval;
mod bind_var_pattern;

pub type Arity = usize;

mod func_scope {
    use std::borrow::Borrow;
    use std::collections::HashMap;
    use std::fmt::{Debug, Formatter};
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    use crate::interpreter::{Arity, Function};

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
            for (_key, func) in self.funcs.iter() {
                writeln!(f, "{}/{}", func.name, func.arity())?;
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

        pub fn push(&mut self, func: Function<'f>) {
            let name = func.name.clone();
            self.funcs
                .insert(FuncMapKey(name, func.arity()), Arc::new(func));
        }

        pub fn push_arc(&mut self, func: Arc<Function<'f>>) {
            self.funcs
                .insert(FuncMapKey(func.name.clone(), func.arity()), func.clone());
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
enum FCow<'e> {
    Owned(Ast),
    Borrowed(&'e Expr),
}

impl Deref for FCow<'_> {
    type Target = Expr;

    fn deref(&self) -> &Self::Target {
        match self {
            FCow::Owned(e) => e,
            FCow::Borrowed(b) => b,
        }
    }
}

#[derive(Debug)]
pub struct Function<'e> {
    name: String,
    args: FuncDefArgs,
    filter: FCow<'e>,
}
pub type FuncDefArgs = SmallVec<[String; 5]>;
pub type FuncRet = Result<Value>;
pub type FuncCallArgs<'e> = SmallVec<[&'e Expr; 5]>;

impl<'e> Function<'e> {
    pub fn new(name: String, args: FuncDefArgs, filter: Ast) -> Function<'static> {
        Function {
            name,
            args,
            filter: FCow::Owned(filter),
        }
    }

    pub fn arity(&self) -> Arity {
        self.args.len()
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn filter(&self) -> &Expr {
        &self.filter
    }

    pub fn bind<'scope>(
        self: &Arc<Self>,
        func_scope: Arc<FuncScope<'scope>>,
        arguments: FuncCallArgs<'scope>,
        arg_var_scope: Arc<VarScope>,
    ) -> Result<BoundFunc<'scope>>
    where
        'e: 'scope,
    {
        if self.arity() != arguments.len() {
            bail!("Function called with incorrect number of arguments")
        }
        Ok(BoundFunc {
            function: self.clone(),
            func_scope,
            arguments,
            arg_var_scope,
        })
    }
}

#[derive(Debug)]
pub struct BoundFunc<'e> {
    function: Arc<Function<'e>>,
    func_scope: Arc<FuncScope<'e>>,
    arguments: SmallVec<[&'e Expr; 5]>,
    arg_var_scope: Arc<VarScope>,
}

impl BoundFunc<'_> {
    pub fn apply(&self, input: &Value) -> ExprResult {
        let mut scope = self.func_scope.new_inner();
        let mut args = Vec::new();
        for (name, arg) in self
            .function
            .args
            .iter()
            .zip(self.arguments.iter().copied())
        {
            let func = Function {
                name: name.to_owned(),
                filter: FCow::Borrowed(arg),
                args: Default::default(),
            };
            args.push(func);
        }
        for func in args.into_iter() {
            scope.push(func)
        }
        scope.push_arc(self.function.clone()); // push ourselves to enable recursion
        let eval = ExprEval::new(Arc::new(scope), input.clone(), self.arg_var_scope.clone());
        self.function.filter.accept(&eval)
    }
}

#[derive(Debug)]
pub struct AstInterpreter {
    func_scope: Arc<FuncScope<'static>>,
    root_filter: Ast,
}

impl AstInterpreter {
    pub fn new(code: &str) -> Result<Self> {
        let builtin = Self::load_builtins()?;
        let root_filter = parser::parse_program(code)?;
        let this = Self {
            func_scope: Arc::new(builtin.functions),
            root_filter,
        };
        Ok(this)
    }

    pub fn eval_input(&mut self, input: Value) -> Result<Vec<Value>> {
        let var_scope = VarScope::new();
        let eval = ExprEval::new(self.func_scope.clone(), input.clone(), var_scope);
        let v = self.root_filter.accept(&eval)?;

        v.collect()
    }

    fn load_builtins() -> Result<JqModule> {
        // let code = std::fs::read_to_string("src/builtins/builtin.jq")?;
        let code = include_str!("../builtins/rjqls_builtins.jq");
        parse_module(&code) // TODO implement the complete Jq language
    }
}

#[cfg(test)]
mod test {
    use serde_json::to_value;

    use super::*;

    /// Parse a Value from JSON data
    fn jval(v: &str) -> Value {
        serde_json::from_str(v).unwrap()
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

        let x = intr.eval_input(to_value(1).unwrap()).unwrap();
        assert_eq!(x[0], to_value([4.0, 5.0, 6.0]).unwrap())
    }

    mod test_eval {
        use super::*;

        macro_rules! check_value {
            ($test_name:ident, $prog:literal, $input:literal, [$($expect:literal),+]) => {
              #[test]
              fn $test_name() {
                  let mut i = AstInterpreter::new($prog).unwrap();
                  let input = serde_json::from_str($input).unwrap();
                  let output = i.eval_input(input).unwrap();
                  let expect: Vec<_> = [$($expect)+].into_iter().map(jval).collect();
                  assert_eq!(&output, &expect);
              }
            };
            ($test_name:ident, $prog:literal, [$($expect:literal),+]) => {
              #[test]
              fn $test_name() {
                  let mut i = AstInterpreter::new($prog).unwrap();
                  let input = Value::Null;
                  let output = i.eval_input(input).unwrap();
                  let expect: Vec<_> = [$($expect),+].into_iter().map(jval).collect();
                  assert_eq!(&output, &expect);
              }
            };
        }
        check_value!(func_prefix, ". | def x: 3; . | x", "null", ["3"]);
        check_value!(
            str_interp,
            r#""x\(1,2)y\(3,4)z" "#,
            ["\"x1y3z\"", "\"x2y3z\"", "\"x1y4z\"", "\"x2y4z\""]
        );
    }

    #[test]
    fn test_eval() {
        let prog = ".[] | select(.==3)";
        let input = jval("[1,2,3]");
        let mut i = AstInterpreter::new(prog).unwrap();
        let v = i.eval_input(input).unwrap();
        assert_eq!(v[0], to_value(3).unwrap())
    }
}
