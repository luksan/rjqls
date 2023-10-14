use anyhow::{bail, Context, Result};
pub use serde_json::{to_value, Number, Value};
use std::sync::Arc;

use crate::interpreter::ast_eval::ExprResult;

pub type ArcValue = Arc<Value>;

pub trait ValueOps {
    fn add(&self, other: &Self) -> Result<Value>;
    fn sub(&self, other: &Self) -> Result<Value>;
    fn mul(&self, other: &Self) -> Result<Value>;
    fn div(&self, other: &Self) -> Result<Value>;

    fn is_truthy(&self) -> bool;
    fn less_than(&self, other: &Self) -> Value;
    fn index(&self, index: &Value) -> Result<Value>;
    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Value> + '_>>;

    fn length(&self) -> Result<Value>;

    fn to_expr_result(self) -> ExprResult<'static>;
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

    fn less_than(&self, other: &Self) -> Value {
        Value::Bool(match (self, other) {
            (Value::Null, _) => false,
            _ => unimplemented!(),
        })
    }

    fn index(&self, index: &Value) -> Result<Value> {
        if let Value::Object(o) = self {
            let idx = index
                .as_str()
                .with_context(|| format!("Can't index object with {index}."))?;
            return Ok(o.get(idx).cloned().unwrap_or(Value::Null));
        }
        let idx = index.as_u64().context("Index is not a number")? as usize;
        if let Value::Array(v) = self {
            return Ok(v.get(idx).cloned().unwrap_or(Value::Null));
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

    fn to_expr_result(self) -> ExprResult<'static> {
        Ok(self.into())
    }
}
