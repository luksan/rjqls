use std::iter;

use anyhow::{bail, Context, Result};
pub use serde_json::Value;
use serde_json::{to_value, Number};

use crate::ast_eval::{ExprResult, ExprValue};

pub trait ValueOps {
    fn add(&self, other: &Self) -> Result<Value>;
    fn sub(&self, other: &Self) -> Result<Value>;
    fn mul(&self, other: &Self) -> Result<Value>;
    fn div(&self, other: &Self) -> Result<Value>;

    fn is_truthy(&self) -> bool;
    fn index(&self, index: &Value) -> Result<Value>;
    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Value> + '_>>;

    fn length(&self) -> Result<Value>;

    fn to_expr_result(self) -> ExprResult;
}

impl ValueOps for Value {
    fn add(&self, other: &Self) -> Result<Value> {
        Ok(match (self, other) {
            (Value::Null, b) => b.clone(),
            (a, Value::Null) => a.clone(),
            (Value::Array(a), Value::Array(b)) => {
                Value::Array(a.iter().chain(b.iter()).cloned().collect())
            }

            (Value::Number(a), Value::Number(b)) => {
                to_value(a.as_f64().unwrap() + b.as_f64().unwrap())?
            }
            (Value::Object(a), Value::Object(b)) => {
                let mut sum = a.clone();
                sum.extend(b.iter().map(|(k, v)| (k.clone(), v.clone())));
                Value::Object(sum)
            }
            (a, b) => bail!("Can't add {a:?} and {b:?}"),
        })
    }

    fn sub(&self, other: &Self) -> Result<Value> {
        Ok(match (self, other) {
            (Value::Number(a), Value::Number(b)) => {
                to_value(a.as_f64().unwrap() - b.as_f64().unwrap())?
            }
            (a, b) => bail!("Can't subtract {b:?} from {a:?}"),
        })
    }
    fn mul(&self, other: &Self) -> Result<Value> {
        let (Some(a), Some(b)) = (self.as_f64(), other.as_f64()) else {
            bail!("Can't multiply {self} with {other}.");
        };
        to_value(a * b).context("To value failed")
    }
    fn div(&self, other: &Self) -> Result<Value> {
        let (Some(a), Some(b)) = (self.as_f64(), other.as_f64()) else {
            bail!("Can't divide {self} with {other}.");
        };
        to_value(a / b).context("To value failed")
    }

    fn is_truthy(&self) -> bool {
        match self {
            Value::Null => false,
            Value::Bool(b) => *b,
            _ => true,
        }
    }

    fn index(&self, index: &Value) -> Result<Value> {
        if let Value::Object(o) = self {
            let idx = index
                .as_str()
                .with_context(|| format!("Can't index object with {index}."))?;
            return Ok(o.get(idx).map(|v| v.clone()).unwrap_or(Value::Null));
        }
        let idx = index.as_u64().context("Index is not a number")? as usize;
        if let Value::Array(v) = self {
            return Ok(v.get(idx).map(|v| v.clone()).unwrap_or(Value::Null));
        }

        unimplemented!()
    }

    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Value> + '_>> {
        match self {
            Value::Array(v) => Ok(Box::new(v.iter())),
            Value::Object(o) => Ok(Box::new(o.iter().map(|(_k, v)| v))),
            _ => bail!("Can't iterate over {self:?}."),
        }
    }

    fn length(&self) -> Result<Value> {
        let len: usize = match self {
            Value::Null => 0,
            Value::Bool(_) => {
                bail!("Bool has no length.")
            }
            Value::Number(_) => return Ok(self.clone()),
            Value::String(s) => s.len(),
            Value::Array(a) => a.len(),
            Value::Object(o) => o.len(),
        };
        Ok(Value::Number(Number::from(len)))
    }

    fn to_expr_result(self) -> ExprResult {
        Ok(ExprValue::from_iter(iter::once(self)))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinOps {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    NotEq,
}

pub type Ast = Box<Expr>;

#[derive(Debug)]
pub enum Expr {
    Array(Vec<Expr>),
    BinOp(BinOps, Ast, Ast),
    Call(Ast, Option<Ast>),
    Comma(Ast, Ast),
    Dot,
    Ident(String),
    Index(Ast, Option<Ast>), // [2]
    Literal(Value),
    Object(Vec<Expr>),
    ObjectEntry { key: Ast, value: Ast },
    ObjMember(String), // select object member
    Pipe(Ast, Ast),
}

impl Expr {
    pub fn accept<R>(&self, visitor: &mut (impl ExprVisitor<R> + ?Sized)) -> R {
        match self {
            Expr::Array(r) => visitor.visit_array(r),
            Expr::BinOp(op, lhs, rhs) => visitor.visit_binop(*op, lhs, rhs),
            Expr::Call(name, args) => visitor.visit_call(name, args.as_ref().map(|ast| &**ast)),
            Expr::Comma(lhs, rhs) => visitor.visit_comma(lhs, rhs),
            Expr::Dot => visitor.visit_dot(),
            Expr::Ident(i) => visitor.visit_ident(i),
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx.as_ref().map(|ast| &**ast)),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::ObjectEntry { key, value } => visitor.visit_obj_entry(key, value),
            Expr::ObjMember(k) => visitor.visit_obj_member(k),
            Expr::Pipe(lhs, rhs) => visitor.visit_pipe(lhs, rhs),
        }
    }
}

#[allow(unused_variables)]
pub trait ExprVisitor<R> {
    fn default(&mut self) -> R;

    fn visit_array(&mut self, elements: &[Expr]) -> R {
        for e in elements {
            e.accept(self);
        }
        self.default()
    }

    fn visit_binop(&mut self, op: BinOps, lhs: &Ast, rhs: &Ast) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_call(&mut self, name: &Expr, args: Option<&Expr>) -> R {
        name.accept(self);
        args.map(|a| a.accept(self));
        self.default()
    }
    fn visit_comma(&mut self, lhs: &Expr, rhs: &Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_dot(&mut self) -> R {
        self.default()
    }
    fn visit_ident(&mut self, ident: &str) -> R {
        self.default()
    }
    fn visit_index(&mut self, expr: &Expr, idx: Option<&Expr>) -> R {
        expr.accept(self);
        idx.map(|idx| idx.accept(self));
        self.default()
    }
    fn visit_literal(&mut self, lit: &Value) -> R {
        self.default()
    }
    fn visit_object(&mut self, members: &[Expr]) -> R {
        for e in members {
            e.accept(self);
        }
        self.default()
    }
    fn visit_obj_entry(&mut self, key: &Expr, value: &Expr) -> R {
        key.accept(self);
        value.accept(self);
        self.default()
    }
    fn visit_obj_member(&mut self, key: &str) -> R {
        self.default()
    }
    fn visit_pipe(&mut self, lhs: &Expr, rhs: &Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
}
