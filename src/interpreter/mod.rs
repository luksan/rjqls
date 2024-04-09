use std::sync::{Arc, Weak};

use anyhow::Result;

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
    use std::ops::{Deref, DerefMut};
    use std::ptr::NonNull;
    use std::sync::{Arc, RwLock, RwLockReadGuard, TryLockError};

    use crate::interpreter::{Arity, Function};
    use crate::interpreter::ast_eval::VarScope;
    use crate::parser::expr_ast::{AstNode, FuncDef};

    type FuncMap<'f> = HashMap<FuncMapKey<'f>, Option<Arc<Function<'f>>>>;

    /// A concurrent HashMap covariant over FuncMap<'f>
    #[derive(Debug)]
    struct LockedMap<'f> {
        lock: RwLock<()>,
        map_ptr: NonNull<FuncMap<'f>>, // covariant over 'f
    }

    impl Drop for LockedMap<'_> {
        fn drop(&mut self) {
            let _ = unsafe { Box::from_raw(self.map_ptr.as_ptr()) };
        }
    }

    unsafe impl Sync for LockedMap<'_> {}
    unsafe impl Send for LockedMap<'_> {}

    impl<'f> LockedMap<'f> {
        fn empty() -> Self {
            let map = Box::new(FuncMap::new());
            Self {
                lock: RwLock::new(()),
                map_ptr: Box::leak(map).into(),
            }
        }

        fn new(name: &'f str, func: Function<'f>) -> Self {
            let mut map = Box::new(FuncMap::with_capacity(1));
            map.insert(FuncMapKey(name, func.arity()), Some(Arc::new(func)));
            Self {
                lock: RwLock::new(()),
                map_ptr: Box::leak(map).into(),
            }
        }

        fn get<'a>(&'a self, key: &FuncMapKey<'a>) -> Option<Option<Arc<Function<'f>>>> {
            let lock = self.lock.read().unwrap();
            let func = unsafe { self.map_ptr.as_ref() }.get(key).cloned();
            drop(lock);
            func
        }

        #[allow(unused)]
        fn insert(&self, name: &'f str, func: Function<'f>) {
            let lock = self.lock.write().unwrap();
            unsafe { &mut *self.map_ptr.as_ptr() }
                .insert(FuncMapKey(name, func.arity()), Some(Arc::new(func)));
            drop(lock);
        }

        fn try_insert(&self, key: FuncMapKey<'f>, func: Option<&Arc<Function<'f>>>) {
            match self.lock.try_write() {
                Ok(guard) => {
                    unsafe { &mut *self.map_ptr.as_ptr() }.insert(key, func.cloned());
                    drop(guard);
                }
                Err(TryLockError::WouldBlock) => {}
                _ => panic!("Poisoned RW lock"),
            }
        }

        pub fn iter(&self) -> MapIter<'f, '_> {
            let lock = self.lock.read().unwrap();
            let iter = unsafe { &*self.map_ptr.as_ptr() }.iter();
            MapIter(iter, lock)
        }
    }

    type MapIterator<'f, 'm> =
        std::collections::hash_map::Iter<'m, FuncMapKey<'f>, Option<Arc<Function<'f>>>>;
    #[allow(dead_code)] // warns about the lock never being used
                        // members are dropped in order, so iter goes before lock guard
    struct MapIter<'f, 'm>(MapIterator<'f, 'm>, RwLockReadGuard<'m, ()>);

    impl<'f, 'm> Deref for MapIter<'f, 'm> {
        type Target = MapIterator<'f, 'm>;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    impl<'f, 'm> DerefMut for MapIter<'f, 'm> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }

    pub struct FuncScope<'f> {
        defines: Option<FuncMapKey<'f>>,
        funcs: LockedMap<'f>,
        parent: Option<Arc<FuncScope<'f>>>,
    }

    impl Default for FuncScope<'_> {
        fn default() -> Self {
            Self {
                defines: None,
                funcs: LockedMap::empty(),
                parent: None,
            }
        }
    }

    impl Debug for FuncScope<'_> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            if let Some(key) = &self.defines {
                let func = self.funcs.get(key).unwrap().unwrap();
                writeln!(f, "{}/{} => {}", key.0, key.1, func.filter)?;
            }
            let mut iter = self.funcs.iter();
            if iter.len() > 1 {
                // Print the cached entries and stop recursing
                writeln!(f, "cached in this scope")?;
                for (key, func) in &mut *iter {
                    if Some(key) == self.defines.as_ref() {
                        // already printed above
                        continue;
                    }
                    if let Some(func) = func {
                        writeln!(f, "{}/{} => {}", key.0, key.1, func.filter)?;
                    } else {
                        writeln!(f, "{}/{} not present", key.0, key.1)?;
                    }
                }
                writeln!(f, "--end of FuncScope dbg output--")?;
                return Ok(());
            }
            if let Some(p) = self.parent.as_ref() {
                write!(f, "{p:?}")
            } else {
                writeln!(f, "-- end of root scope --")
            }
        }
    }

    impl<'f> FuncScope<'f> {
        pub fn new(func_def: &'f FuncDef, var_scope: &Arc<VarScope<'f>>) -> Arc<Self> {
            let name = &func_def.name;
            let args = Some(&func_def.args);
            let filter = &func_def.body;
            Arc::new_cyclic(|weak| {
                let func = Function {
                    args,
                    filter,
                    def_scope: weak.clone(),
                    var_scope: var_scope.clone(),
                };
                Self {
                    defines: Some(FuncMapKey(name, func.arity())),
                    funcs: LockedMap::new(name, func),
                    parent: None,
                }
            })
        }

        fn new_inner<'fi>(
            self: &Arc<Self>,
            name: &'fi str,
            mut func: Function<'fi>,
            self_scope: bool,
        ) -> Arc<FuncScope<'fi>>
        where
            'f: 'fi,
        {
            Arc::new_cyclic(|weak| {
                if self_scope {
                    func.def_scope = weak.clone();
                }
                FuncScope::<'fi> {
                    defines: Some(FuncMapKey(name, func.arity())),
                    funcs: LockedMap::new(name, func),
                    parent: Some(self.clone()),
                }
            })
        }

        #[must_use]
        pub fn push_func_arg<'i>(
            self: &Arc<Self>,
            name: &'i str,
            filter: &'i AstNode,
            def_scope: &Arc<FuncScope<'i>>,
            var_scope: &Arc<VarScope<'i>>,
        ) -> Arc<FuncScope<'i>>
        where
            'f: 'i,
        {
            let func = Function {
                args: None,
                filter,
                def_scope: Arc::downgrade(def_scope),
                var_scope: var_scope.clone(),
            };
            self.new_inner(name, func, false)
        }

        #[must_use]
        pub fn push_func_def(
            self: &Arc<Self>,
            func_def: &'f FuncDef,
            var_scope: &Arc<VarScope<'f>>,
        ) -> Arc<Self> {
            let name = &func_def.name;
            let args = Some(&func_def.args);
            let filter = &func_def.body;
            let func = Function {
                args,
                filter,
                def_scope: Arc::downgrade(self), // this will be replaced with the new scope in new_inner()
                var_scope: var_scope.clone(),
            };
            self.new_inner(name, func, true)
        }

        #[inline]
        fn get_func_local(
            self: &Arc<Self>,
            key: &FuncMapKey,
        ) -> Option<Option<(Arc<Function<'f>>, Arc<Self>)>> {
            Some(
                self.funcs
                    .get(key)?
                    .map(|func| (func.clone(), func.def_scope.upgrade().unwrap())),
            )
        }

        fn get_func_no_caching(
            self: &Arc<Self>,
            key: &FuncMapKey<'_>,
        ) -> Option<(Arc<Function<'f>>, Arc<Self>)> {
            if let Some(f) = self.get_func_local(key) {
                return f;
            }
            self.parent
                .as_ref()
                .and_then(|p| p.get_func_no_caching(key))
        }

        pub fn get_func<'a>(
            self: &Arc<Self>,
            name: &'a str,
            arity: Arity,
        ) -> Option<(Arc<Function<'f>>, Arc<Self>)> {
            let key = FuncMapKey(name, arity);
            if let Some(ret) = self.get_func_local(&key) {
                return ret;
            }
            let ret = self
                .parent
                .as_ref()
                .and_then(|p| p.get_func_no_caching(&key));

            // insert result into the cache
            self.funcs.try_insert(key, ret.as_ref().map(|x| &x.0));

            ret
        }
    }

    #[derive(Debug, Copy, Clone, Default, Eq, PartialEq, Hash)]
    struct FuncMapKey<'f>(&'f str, Arity);

    // https://stackoverflow.com/questions/45786717/how-to-implement-hashmap-with-two-keys/45795699#45795699
    trait MapKeyT {
        fn name(&self) -> &str;
        fn arity(&self) -> Arity;
    }

    impl MapKeyT for FuncMapKey<'_> {
        fn name(&self) -> &str {
            self.0
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

    impl<'a> Borrow<dyn MapKeyT + 'a> for FuncMapKey<'a> {
        fn borrow(&self) -> &(dyn MapKeyT + 'a) {
            self
        }
    }
}

#[derive(Debug)]
pub struct Function<'e> {
    args: FuncDefArgs<'e>,
    filter: &'e AstNode,
    def_scope: Weak<FuncScope<'e>>,
    var_scope: Arc<VarScope<'e>>,
}

pub type FuncDefArgs<'e> = Option<&'e Vec<String>>;
pub type FuncRet = Result<Value>;

impl<'e> Function<'e> {
    pub fn arity(&self) -> Arity {
        self.args.map(|x| x.len()).unwrap_or(0)
    }

    pub fn filter(&self) -> &'e AstNode {
        self.filter
    }

    pub fn bind<'scope>(
        self: Arc<Self>,
        mut func_scope: Arc<FuncScope<'scope>>,
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
        if let Some(args) = self.args {
            for (name, arg) in args.iter().zip(arguments.iter()) {
                func_scope = func_scope.push_func_arg(name, arg, arg_scope, var_scope);
            }
        }
        BoundFunc {
            function: self,
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
    #[allow(unused)]
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
        let mut builtins = self.builtins.iter();
        let var_scope = VarScope::new();
        let mut func_scope = FuncScope::new(builtins.next().unwrap(), &var_scope);
        for f in builtins {
            func_scope = func_scope.push_func_def(f, &var_scope);
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
