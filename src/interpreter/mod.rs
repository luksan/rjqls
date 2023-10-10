use std::ops::Deref;
use std::sync::Arc;

use anyhow::{bail, Result};
use serde_json::Value;
use smallvec::SmallVec;

pub use func_scope::FuncScope;

use crate::parser;
use crate::parser::expr_ast::{Ast, Expr};
use crate::parser::{parse_module, JqModule, Stmt};
use ast_eval::{ExprEval, ExprResult, VarScope};

pub mod ast_eval;
mod bind_var_pattern;

pub type Arity = usize;

mod func_scope {
    use std::borrow::Borrow;
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    use crate::interpreter::{Arity, Function};

    #[derive(Debug, Default)]
    pub struct FuncScope<'p, 'f> {
        owned: HashMap<FuncMapKey, Arc<Function<'static>>>,
        borrowed: HashMap<FuncMapKey, &'f Function<'f>>,
        parent: Option<&'p FuncScope<'p, 'p>>,
    }

    impl<'p, 'f> FuncScope<'p, 'f> {
        pub fn new_inner<'s, 'fi>(&'s self) -> FuncScope<'s, 'fi>
        where
            's: 'p,
            'f: 'fi,
        {
            Self {
                parent: Some(self),
                ..Default::default()
            }
        }

        pub fn push(&mut self, func: Function<'static>) {
            let name = func.name.clone();
            self.owned
                .insert(FuncMapKey(name, func.arity()), Arc::new(func));
        }

        pub fn push_ref(&mut self, func: &'f Function) {
            self.borrowed
                .insert(FuncMapKey(func.name.clone(), func.arity()), func.clone());
        }

        pub fn get_func_ref(&self, name: &str, arity: Arity) -> Option<&Function> {
            self.borrowed
                .get(&(name, arity) as &dyn MapKeyT)
                .copied()
                .or_else(|| {
                    self.owned
                        .get(&(name, arity) as &dyn MapKeyT)
                        .map(|arc| &**arc)
                        .or_else(|| self.parent.and_then(|p| p.get_func_ref(name, arity)))
                })
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

    pub fn filter(&self) -> &Expr {
        &self.filter
    }

    pub fn bind<'scope>(
        &'scope self,
        func_scope: &'scope FuncScope,
        arguments: FuncCallArgs<'scope>,
        arg_var_scope: Arc<VarScope>,
    ) -> Result<Generator<'scope>> {
        if self.arity() != arguments.len() {
            bail!("Function called with incorrect number of arguments")
        }
        Ok(Generator {
            function: self,
            func_scope,
            arguments,
            arg_var_scope,
        })
    }
}

#[derive(Debug)]
pub struct Generator<'e> {
    function: &'e Function<'e>,
    func_scope: &'e FuncScope<'e, 'e>,
    arguments: SmallVec<[&'e Expr; 5]>,
    arg_var_scope: Arc<VarScope>,
}

impl Generator<'_> {
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
        for func in args.iter() {
            scope.push_ref(func)
        }
        scope.push_ref(self.function); // push ourselves to enable recursion
        let eval = ExprEval::new(&scope, input.clone(), self.arg_var_scope.clone());
        self.function.filter.accept(&eval)
    }
}

#[derive(Debug)]
pub struct AstInterpreter {
    func_scope: FuncScope<'static, 'static>,
    root_filters: Vec<Ast>,
}

impl AstInterpreter {
    pub fn new(code: &str) -> Result<Self> {
        let builtin = Self::load_builtins()?;
        let mut this = Self {
            func_scope: builtin.functions,
            root_filters: Default::default(),
        };
        let stmts = parser::parse_program(code)?;
        for stmt in stmts {
            match stmt {
                Stmt::DefineFunc(f) => {
                    this.func_scope.push(f);
                }
                Stmt::RootFilter(f) => {
                    this.root_filters.push(f);
                }
            }
        }
        Ok(this)
    }

    pub fn eval_input(&mut self, input: Value) -> Result<Vec<Value>> {
        let mut ret = Vec::new();
        for flt in self.root_filters.iter() {
            let var_scope = VarScope::new();
            let eval = ExprEval::new(&self.func_scope, input.clone(), var_scope);
            let v = flt.accept(&eval)?;
            ret.extend(v);
        }
        Ok(ret)
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

    #[test]
    fn test_eval() {
        let prog = ".[] | select(.==3)";
        let input: Value = serde_json::from_str("[1,2,3]").unwrap();
        let mut i = AstInterpreter::new(prog).unwrap();
        let v = i.eval_input(input).unwrap();
        assert_eq!(v[0], to_value(3).unwrap())
    }
}
