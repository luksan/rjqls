use std::fmt::{Display, Formatter};
use std::sync::Arc;

use anyhow::{bail, Context, Result};
pub use serde_json::{Number, to_value, Value as JsonValue};


pub type Value = JsonValue;
pub trait ValueOps: Sized {
    fn add(&self, other: &Self) -> Result<Self>;
    fn sub(&self, other: &Self) -> Result<Self>;
    fn mul(&self, other: &Self) -> Result<Self>;
    fn div(&self, other: &Self) -> Result<Self>;

    fn is_truthy(&self) -> bool;
    fn less_than(&self, other: &Self) -> Self;
    fn index(&self, index: &Self) -> Result<Self>;
    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Self> + '_>>;

    fn length(&self) -> Result<Self>;
}

}

#[derive(Debug, Clone, PartialEq)]
pub struct ArcValue {
    inner: Arc<JsonValue>,
}

impl ArcValue {
    pub fn as_array(&self) -> Option<&[Self]> {
        unimplemented!()
    }
    pub fn as_str(&self) -> Option<&str> {
        unimplemented!()
    }
}

impl From<JsonValue> for ArcValue {
    fn from(value: JsonValue) -> Self {
        Self {
            inner: Arc::new(value),
        }
    }
}

impl From<f64> for ArcValue {
    fn from(value: f64) -> Self {
        JsonValue::from(value).into()
    }
}

impl Display for ArcValue {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        unimplemented!()
    }
}


impl ValueOps for JsonValue {
    fn add(&self, other: &Self) -> Result<Self> {
        Ok(match (self, other) {
            (Self::Null, b) => b.clone(),
            (a, Self::Null) => a.clone(),
            (Self::Array(a), Self::Array(b)) => {
                Self::Array(a.iter().chain(b.iter()).cloned().collect())
            }

            (Self::Number(a), Self::Number(b)) => {
                (a.as_f64().unwrap() + b.as_f64().unwrap()).into()
            }
            (Self::Object(a), Self::Object(b)) => {
                let mut sum = a.clone();
                sum.extend(b.iter().map(|(k, v)| (k.clone(), v.clone())));
                Self::Object(sum)
            }
            (a, b) => bail!("Can't add {a:?} and {b:?}"),
        })
    }

    fn sub(&self, other: &Self) -> Result<Self> {
        Ok(match (self, other) {
            (Self::Number(a), Self::Number(b)) => {
                (a.as_f64().unwrap() - b.as_f64().unwrap()).into()
            }
            (a, b) => bail!("Can't subtract {b:?} from {a:?}"),
        })
    }
    fn mul(&self, other: &Self) -> Result<Self> {
        let (Some(a), Some(b)) = (self.as_f64(), other.as_f64()) else {
            bail!("Can't multiply {self} with {other}.");
        };
        Ok((a * b).into())
    }
    fn div(&self, other: &Self) -> Result<Self> {
        let (Some(a), Some(b)) = (self.as_f64(), other.as_f64()) else {
            bail!("Can't divide {self} with {other}.");
        };
        Ok((a / b).into())
    }

    fn is_truthy(&self) -> bool {
        match self {
            Self::Null => false,
            Self::Bool(b) => *b,
            _ => true,
        }
    }

    fn less_than(&self, other: &Self) -> Self {
        Self::Bool(match (self, other) {
            (Self::Null, _) => false,
            _ => unimplemented!(),
        })
    }

    fn index(&self, index: &Self) -> Result<Self> {
        if let Self::Object(o) = self {
            let idx = index
                .as_str()
                .with_context(|| format!("Can't index object with {index}."))?;
            return Ok(o.get(idx).cloned().unwrap_or(Self::Null));
        }
        let idx = index.as_u64().context("Index is not a number")? as usize;
        if let Self::Array(v) = self {
            return Ok(v.get(idx).cloned().unwrap_or(Self::Null));
        }

        unimplemented!()
    }

    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Self> + '_>> {
        match self {
            Self::Array(v) => Ok(Box::new(v.iter())),
            Self::Object(o) => Ok(Box::new(o.iter().map(|(_k, v)| v))),
            _ => bail!("Can't iterate over {self:?}."),
        }
    }

    fn length(&self) -> Result<Self> {
        let len: usize = match self {
            Self::Null => 0,
            Self::Bool(_) => {
                bail!("Bool has no length.")
            }
            Self::Number(_) => return Ok(self.clone()),
            Self::String(s) => s.len(),
            Self::Array(a) => a.len(),
            Self::Object(o) => o.len(),
        };
        Ok(Self::Number(Number::from(len)))
    }
}
