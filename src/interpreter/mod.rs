use std::sync::{Arc, Weak};

use anyhow::Result;
use smallvec::SmallVec;

use ast_eval::{ExprEval, VarScope};
pub use func_scope::FuncScope;

use crate::parser;
use crate::parser::expr_ast::{Ast, AstNode, FuncDef};
use crate::parser::parse_module;
use crate::src_reader::{SrcRead, SrcReader};
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
    use crate::interpreter::ast_eval::VarScope;
    use crate::parser::expr_ast::{AstNode, FuncDef};

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
            if self.parent.is_none() {
                return writeln!(f, "-- root scope --");
            }
            writeln!(f, "== FuncScope ==")?;
            for (key, func) in self.funcs.iter() {
                writeln!(f, "{}/{} => {}", key.0, func.arity(), func.filter)?;
            }
            if let Some(p) = self.parent.as_ref() {
                write!(f, "{p:?}")?;
            }
            Ok(())
        }
    }

    impl<'f> FuncScope<'f> {
        fn new_inner<'fi>(self: &Arc<Self>) -> FuncScope<'fi>
        where
            'f: 'fi,
        {
            FuncScope::<'fi> {
                parent: Some(self.clone()),
                ..Default::default()
            }
        }

        #[must_use]
        pub fn push_inner<'i>(
            self: &Arc<Self>,
            name: String,
            args: FuncDefArgs,
            filter: &'i AstNode,
            def_scope: Option<&Arc<Self>>,
            var_scope: &Arc<VarScope<'i>>,
        ) -> Arc<FuncScope<'i>>
        where
            'f: 'i,
        {
            let mut inner = self.new_inner();
            let func = Function {
                args,
                filter,
                def_scope: def_scope.map(Arc::downgrade),
                var_scope: var_scope.clone(),
            };
            inner
                .funcs
                .insert(FuncMapKey(name, func.arity()), Arc::new(func));
            Arc::new(inner)
        }

        #[must_use]
        pub fn push_func_def(
            self: &Arc<Self>,
            func_def: &'f FuncDef,
            def_scope: Option<&Arc<Self>>,
            var_scope: &Arc<VarScope<'f>>,
        ) -> Arc<Self> {
            self.push_inner(
                func_def.name.clone(),
                func_def.args.clone().into(),
                &func_def.body,
                def_scope,
                var_scope,
            )
        }

        pub fn get_func<'a>(
            self: &'a Arc<Self>,
            name: &str,
            arity: Arity,
        ) -> Option<(&'a Arc<Function<'f>>, Arc<Self>)> {
            self.funcs
                .get(&(name, arity) as &dyn MapKeyT)
                .map(|func| {
                    (
                        func,
                        func.def_scope
                            .as_ref()
                            .map(|weak| weak.upgrade().unwrap())
                            .unwrap_or_else(|| self.clone()),
                    )
                })
                .or_else(move || self.parent.as_ref().and_then(|p| p.get_func(name, arity)))
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
    filter: &'e AstNode,
    def_scope: Option<Weak<FuncScope<'e>>>,
    var_scope: Arc<VarScope<'e>>,
}

pub type FuncDefArgs = SmallVec<[String; 5]>;
pub type FuncRet = Result<Value>;

impl<'e> Function<'e> {
    pub fn arity(&self) -> Arity {
        self.args.len()
    }

    pub fn filter(&self) -> &'e AstNode {
        self.filter
    }

    pub fn bind<'scope>(
        self: &Arc<Self>,
        func_scope: &Arc<FuncScope<'scope>>,
        arguments: &'scope [AstNode],
        arg_scope: &Arc<FuncScope<'scope>>,
        var_scope: &Arc<VarScope<'scope>>,
    ) -> BoundFunc<'scope>
    where
        'e: 'scope,
    {
        assert_eq!(
            self.arity(),
            arguments.len(),
            "bind() called with incorrect number of arguments"
        );
        let mut func_scope = func_scope.clone();
        for (name, arg) in self.args.iter().zip(arguments.iter()) {
            func_scope = func_scope.push_inner(
                name.clone(),
                Default::default(),
                arg,
                Some(arg_scope),
                var_scope,
            );
        }
        BoundFunc {
            function: self.clone(),
            func_scope,
        }
    }
}

#[derive(Debug)]
pub struct BoundFunc<'e> {
    function: Arc<Function<'e>>,
    func_scope: Arc<FuncScope<'e>>,
}

#[derive(Debug)]
pub struct AstInterpreter {
    builtins: Vec<FuncDef>,
    root_filter: Ast,
    variables: Arc<VarScope<'static>>,
    src_reader: SrcReader,
}

impl AstInterpreter {
    pub fn new(code: &str) -> Result<Self> {
        let mut src_reader = SrcReader::new();
        let (builtin_src, src_id) = src_reader.builtins();
        let builtin = parse_module(builtin_src.as_ref(), src_id, &mut src_reader)?;
        let root_filter = parser::parse_program(code, &mut src_reader)?;
        let this = Self {
            builtins: builtin.functions,
            root_filter,
            variables: VarScope::new(),
            src_reader,
        };
        Ok(this)
    }

    pub fn set_variable(&mut self, name: String, value: ArcValue) {
        // TODO: this is only used for cmdline variables, so leaking is not a huge deal.
        self.variables = self.variables.set_variable(name.leak(), value);
    }

    pub fn eval_input(&mut self, input: Value) -> Result<Vec<Value>> {
        let var_scope = self.variables.clone();
        let func_scope = self.build_func_scope();
        let eval = ExprEval::new(func_scope.clone(), input.clone(), var_scope);
        eval.visit(&self.root_filter)
    }

    fn build_func_scope(&self) -> Arc<FuncScope> {
        let mut func_scope = Arc::new(FuncScope::default());
        for f in self.builtins.iter() {
            func_scope = func_scope.push_inner(
                f.name.clone(),
                f.args.clone().into(),
                &f.body,
                None,
                &VarScope::new(),
            );
        }
        func_scope
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
        assert_eq!(x[0], Value::from_str("[4, 5, 6]").unwrap())
    }

    mod test_eval {
        use super::*;

        macro_rules! check_value {
            ($([$test_name:ident, $prog:literal, $($input:literal,)? [$($expect:literal),+]])+) => {
              $(
              #[test]
              fn $test_name() {
                  let mut i = AstInterpreter::new($prog).unwrap();
                  let input = if false {unreachable!()}
                      $(else if true { Value::from_str($input).unwrap() })?
                        else { Value::Null };
                  let output = i.eval_input(input).unwrap();
                  let expect: Vec<_> = [$($expect),+].into_iter().map(jval).collect();
                  assert_eq!(&output, &expect);
              })+
            };
        }
        check_value!(
            [func_prefix, ". | def x: 3; . | x", "null", ["3"]]
            [isempty, "isempty(1)", ["false"]]
            [isempty_2, "isempty(empty)", ["true"]]
            [func_var_arg, r#"def f($a): $a+1; f(1)"#, ["2"]]
            [str_interp,r#""x\(1,2)y\(3,4)z\("a"+"b")" "#, ["\"x1y3zab\"", "\"x2y3zab\"", "\"x1y4zab\"", "\"x2y4zab\""]]
            [subs,r#"sub("\\s+"; "")"#, "\"   asd asd \"", ["\"asd asd \""]]
        );
    }

    #[test]
    fn test_eval_dbg() {
        /*
        let prog = r#"sub("\\s+"; "")"#;
        let input = jval("\"  asd asd   \"");
        let mut i = AstInterpreter::new(prog).unwrap();
        let v = i.eval_input(input).unwrap();
        assert_eq!(v[0], Value::from(3))
        */
    }
}
