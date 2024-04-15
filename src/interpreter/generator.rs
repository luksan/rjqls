use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};
use std::iter;

use anyhow::Result;

use crate::interpreter::ast_eval::{EvalError, ExprEval};
use crate::parser::expr_ast::{AstNode, BreakLabel};
use crate::value::Value;

pub struct Generator<'e> {
    item: GeneratorItem<'e>,
    chain: VecDeque<GeneratorItem<'e>>,
}

pub enum GeneratorItem<'e> {
    Iter(BoxResValIter<'e>),
    Accept(Option<Box<Acceptor<'e>>>),
}

impl<'e> From<GeneratorItem<'e>> for Generator<'e> {
    fn from(value: GeneratorItem<'e>) -> Self {
        Self {
            item: value,
            chain: Default::default(),
        }
    }
}

pub type ResVal = Result<Value, EvalError>;
type BoxResValIter<'e> = Box<dyn Iterator<Item = ResVal> + 'e>;

impl Default for Generator<'_> {
    fn default() -> Self {
        Self {
            item: GeneratorItem::Iter(Box::new(iter::empty())),
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

    pub fn from_break(label: BreakLabel) -> Self {
        Self::from_iter(iter::once(Err(EvalError::Break(label))))
    }

    pub fn from_accept(eval: ExprEval<'e>, ast: &'e AstNode) -> Self {
        GeneratorItem::Accept(Some(Box::new(Acceptor { eval, ast }))).into()
    }

    #[must_use]
    pub fn chain_gen(mut self, mut next: Self) -> Self {
        self.chain.push_back(next.item);
        self.chain.append(&mut next.chain);
        self
    }

    #[must_use]
    pub fn chain_break(self, next: Self, label: BreakLabel) -> Self {
        self.chain_gen(Self::from_iter(next.take_while(
            move |res| !matches!(res, Err(EvalError::Break(lbl)) if &label == lbl),
        )))
    }

    #[must_use]
    pub fn chain_res(self, next: Result<Self, EvalError>) -> Self {
        let next = next.unwrap_or_else(|err| Self::from_iter(iter::once(Err(err))));
        self.chain_gen(next)
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
        loop {
            match &mut self.item {
                GeneratorItem::Iter(src) => {
                    if let Some(n) = src.next() {
                        if n.is_err() {
                            // stop iterating on error
                            *self = Self::empty();
                        }
                        return Some(n);
                    }
                    self.item = self.chain.pop_front()?;
                }
                GeneratorItem::Accept(a) => {
                    let mut next = a.take().unwrap().into_iter();
                    next.chain.append(&mut self.chain);
                    *self = next
                }
            }
        }
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
        gen.unwrap_or_else(|err| Generator::from_iter(iter::once(Err(err))))
    }
}

impl From<Value> for Generator<'_> {
    fn from(value: Value) -> Self {
        Generator::from_iter(iter::once(Ok(value)))
    }
}

impl From<ResVal> for Generator<'_> {
    fn from(value: ResVal) -> Self {
        Generator::from_iter(iter::once(value))
    }
}

impl From<Vec<ResVal>> for Generator<'_> {
    fn from(value: Vec<ResVal>) -> Self {
        Generator::from_iter(value)
    }
}

/// Collects generator output into a Vec and then loops the result
///
/// Returns None when the cycle restarts
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

/// A generator for generators
pub struct GenGen<'e, G> {
    gens: G,
    func: Box<dyn FnMut(&mut G) -> Option<Result<Generator<'e>, EvalError>>>,
    curr: Generator<'e>,
    fused: bool,
}

impl<'e, G> GenGen<'e, G> {
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
