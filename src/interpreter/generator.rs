use std::fmt::{Debug, Formatter};
use std::iter;

use anyhow::Result;

use crate::interpreter::ast_eval::EvalError;
use crate::parser::expr_ast::BreakLabel;
use crate::value::Value;

pub struct Generator<'e> {
    src: Box<dyn Iterator<Item = ResVal> + 'e>,
}
pub type ResVal = Result<Value, EvalError>;

impl Default for Generator<'_> {
    fn default() -> Self {
        Self {
            src: Box::new(iter::empty()),
        }
    }
}

impl<'e> Generator<'e> {
    pub fn from_iter(i: impl IntoIterator<Item = ResVal> + 'e) -> Generator<'e> {
        Generator {
            src: Box::new(i.into_iter()),
            ..Self::default()
        }
    }

    pub fn from_break(label: BreakLabel) -> Self {
        Self {
            src: Box::new(iter::once(Err(EvalError::Break(label)))),
            ..Self::default()
        }
    }

    pub fn empty() -> Generator<'static> {
        Generator::default()
    }

    #[must_use]
    pub fn chain_gen(self, next: impl IntoIterator<Item = ResVal> + 'e) -> Self {
        Self::from_iter(self.chain(next))
    }

    #[must_use]
    pub fn chain_break(self, next: Self, label: BreakLabel) -> Self {
        self.chain_gen(
            next.take_while(move |res| !matches!(res, Err(EvalError::Break(lbl)) if &label == lbl)),
        )
    }

    #[must_use]
    pub fn chain_res(self, next: Result<Self, EvalError>) -> Self {
        let next = next.unwrap_or_else(|err| Self::from_iter(iter::once(Err(err))));
        self.chain_gen(next)
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
        self.src.next()
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
