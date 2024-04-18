use std::collections::VecDeque;
use std::convert::Infallible;
use std::fmt::{Debug, Formatter};
use std::ops::FromResidual;

use anyhow::Result;

use crate::interpreter::ast_eval::{EvalError, ExprEval};
use crate::parser::expr_ast::{AstNode, BreakLabel};
use crate::value::Value;

pub struct Generator<'e> {
    chain: VecDeque<GeneratorItem<'e>>,
}

pub enum GeneratorItem<'e> {
    Iter(BoxResValIter<'e>),
    Once(Option<ResVal>),
    Accept(Option<Box<Acceptor<'e>>>),
}

impl<'e> From<GeneratorItem<'e>> for Generator<'e> {
    fn from(value: GeneratorItem<'e>) -> Self {
        Self {
            chain: VecDeque::from([value]),
        }
    }
}

pub type ResVal = Result<Value, EvalError>;
type BoxResValIter<'e> = Box<dyn Iterator<Item = ResVal> + 'e>;

impl Default for Generator<'_> {
    fn default() -> Self {
        Self {
            chain: Default::default(),
        }
    }
}

impl<'e> Generator<'e> {
    pub fn empty() -> Generator<'static> {
        Generator::default()
    }

    pub fn from_iter(i: impl IntoIterator<Item = ResVal> + 'e) -> Generator<'e> {
        GeneratorItem::Iter(Box::new(i.into_iter())).into()
    }

    pub fn from_resval(v: ResVal) -> Self {
        GeneratorItem::Once(Some(v)).into()
    }

    pub fn from_accept(eval: ExprEval<'e>, ast: &'e AstNode) -> Self {
        GeneratorItem::Accept(Some(Box::new(Acceptor { eval, ast }))).into()
    }

    #[must_use]
    pub fn chain_gen(mut self, mut next: Self) -> Self {
        self.chain.append(&mut next.chain);
        self
    }

    #[must_use]
    pub fn chain_break(self, next: Self, label: BreakLabel) -> Self {
        self.chain_gen(Self::from_iter(next.take_while(
            move |res| !matches!(res, Err(EvalError::Break(lbl)) if &label == lbl),
        )))
    }

    pub fn map_gen(self, mut f: impl FnMut(Value) -> ResVal + 'e) -> Self {
        Self::from_iter(self.map(move |resval| if let Ok(val) = resval { f(val) } else { resval }))
    }

    pub fn restrict<F, FE, E>(self, mut f: F, mut err: FE) -> Self
    where
        F: FnMut(&Value) -> bool + 'e,
        FE: FnMut(Value) -> E + 'e,
        E: Into<EvalError>,
    {
        Self::from_iter(self.map(move |resval| match resval {
            Ok(val) => {
                if !f(&val) {
                    Err(err(val).into())
                } else {
                    Ok(val)
                }
            }
            err => err,
        }))
    }
}

impl Debug for Generator<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Generator {{..}}")
    }
}

impl Iterator for Generator<'_> {
    type Item = ResVal;

    fn next(&mut self) -> Option<Self::Item> {
        let ret = loop {
            let val = match self.chain.front_mut()? {
                GeneratorItem::Iter(src) => {
                    if let Some(v) = src.next() {
                        break v;
                    }
                    None
                }
                GeneratorItem::Once(val) => val.take(),
                GeneratorItem::Accept(a) => {
                    let mut next = a.take().unwrap().into_iter();
                    self.chain.pop_front();
                    next.chain.append(&mut self.chain);
                    *self = next;
                    continue;
                }
            };
            self.chain.pop_front();
            if let Some(val) = val {
                break val;
            }
        };
        if ret.is_err() {
            // stop iterating on error
            *self = Self::empty();
        }
        Some(ret)
    }
}

impl<'e, E: Into<EvalError>> FromResidual<Result<Infallible, E>> for Generator<'e> {
    fn from_residual(residual: Result<Infallible, E>) -> Self {
        match residual {
            Err(err) => Err::<Value, EvalError>(err.into()).into(),
            _ => unreachable!(),
        }
    }
}

impl<T> FromResidual<Option<T>> for Generator<'_> {
    fn from_residual(_residual: Option<T>) -> Self {
        Generator::empty()
    }
}

pub struct Acceptor<'e> {
    eval: ExprEval<'e>,
    ast: &'e AstNode,
}

impl<'e> IntoIterator for Acceptor<'e> {
    type Item = ResVal;
    type IntoIter = Generator<'e>;

    fn into_iter(self) -> Self::IntoIter {
        self.ast.accept(&self.eval).into()
    }
}

impl<'e> From<Result<Generator<'e>, EvalError>> for Generator<'e> {
    fn from(gen: Result<Generator<'e>, EvalError>) -> Self {
        gen.unwrap_or_else(|err| Generator::from_resval(Err(err)))
    }
}

impl From<Value> for Generator<'_> {
    fn from(value: Value) -> Self {
        Generator::from_resval(Ok(value))
    }
}

impl From<Vec<ResVal>> for Generator<'_> {
    fn from(value: Vec<ResVal>) -> Self {
        Generator::from_iter(value)
    }
}

impl From<EvalError> for Generator<'_> {
    fn from(value: EvalError) -> Self {
        Self::from_resval(Err(value))
    }
}

impl From<anyhow::Error> for Generator<'_> {
    fn from(value: anyhow::Error) -> Self {
        EvalError::Anyhow(value).into()
    }
}

impl<E: Into<EvalError>> From<Result<Value, E>> for Generator<'_> {
    fn from(value: Result<Value, E>) -> Self {
        match value {
            Ok(val) => val.into(),
            Err(e) => Generator::from(e.into()),
        }
    }
}

/// Collects generator output into a Vec and then loops the result
///
/// Returns None when the cycle restarts. Don't use if the generator has side effects
#[derive(Debug)]
pub struct GenCycle<'e> {
    gen: Generator<'e>,
    values: Vec<Value>,
    pos: usize,
}

impl<'e> GenCycle<'e> {
    pub fn new(gen: Generator<'e>) -> Self {
        Self {
            gen,
            values: vec![],
            pos: 0,
        }
    }
}

impl<'e> Iterator for GenCycle<'e> {
    type Item = ResVal;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.gen.next() {
            match &next {
                Ok(v) => {
                    self.values.push(v.clone());
                    self.pos += 1;
                }
                Err(_) => {
                    // Fuse on error
                    self.values = Vec::new();
                }
            }
            Some(next)
        } else if self.pos >= self.values.len() {
            self.pos = 0;
            None
        } else {
            let ret = self.values[self.pos].clone();
            self.pos += 1;
            Some(Ok(ret))
        }
    }
}

pub struct CrossProd<'e, const N: usize> {
    gens: [BoxResValIter<'e>; N],
    func: Box<dyn FnMut(&[Value; N]) -> Option<Result<Generator<'e>, EvalError>>>,
    values: [Value; N],
    update_pos: usize,
    curr: Generator<'e>,
    ended: bool,
}

impl<'e, const N: usize> CrossProd<'e, N> {
    pub fn new(
        gens: [BoxResValIter<'e>; N],
        func: impl FnMut(&[Value; N]) -> Option<Result<Generator<'e>, EvalError>> + 'static,
    ) -> Self {
        const NULL: Value = Value::Null;
        Self {
            gens,
            func: Box::new(func),
            values: [NULL; N],
            update_pos: 0,
            curr: Generator::empty(),
            ended: false,
        }
    }
}

impl<'e, const N: usize> Iterator for CrossProd<'e, N> {
    type Item = ResVal;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }
        if let Some(v) = self.curr.next() {
            return Some(v);
        }

        let mut pos = N - 1; // the rightmost slot is the innermost one
        let mut retried_pos = N; // the latest pos that returned None
        loop {
            match self.gens[pos].next() {
                Some(Ok(val)) => self.values[pos] = val,
                Some(Err(err)) => {
                    self.ended = true;
                    return Some(Err(err));
                }
                None if pos == 0 || pos == retried_pos => {
                    self.ended = true;
                    return None;
                }
                None => {
                    retried_pos = pos;
                    self.update_pos = pos - 1; // we cycled this pos -> the next outer needs an update
                    continue; // try to get another val
                }
            }
            if pos == self.update_pos {
                break;
            }
            pos -= 1;
        }
        self.update_pos = N - 1; // always start with updating only the rightmost slot

        match (self.func)(&self.values) {
            Some(Ok(gen)) => {
                self.curr = gen;
                self.next()
            }
            Some(Err(err)) => {
                self.ended = true;
                Some(Err(err))
            }
            None => {
                self.ended = true;
                None
            }
        }
    }
}

/// A generator for generators
pub struct GenGen<'e, G> {
    gens: G,
    func: Box<dyn FnMut(&mut G) -> Option<Result<Generator<'e>, EvalError>>>,
    curr: Generator<'e>,
    fused: bool,
}

impl<'e, G> GenGen<'e, G> {
    #[allow(dead_code)]
    pub fn new(
        gens: G,
        func: impl FnMut(&mut G) -> Option<Result<Generator<'e>, EvalError>> + 'static,
    ) -> Self {
        Self {
            gens,
            func: Box::new(func),
            curr: Generator::empty(),
            fused: false,
        }
    }
}

impl<'e, G> Iterator for GenGen<'e, G> {
    type Item = ResVal;

    fn next(&mut self) -> Option<Self::Item> {
        if self.fused {
            return None;
        }
        if let Some(n) = self.curr.next() {
            return Some(n);
        }

        match (self.func)(&mut self.gens) {
            Some(Ok(gen)) => self.curr = gen,
            None => {
                self.fused;
                return None;
            }
            Some(Err(e)) => {
                self.fused = true;
                return Some(Err(e));
            }
        }
        self.next()
    }
}
