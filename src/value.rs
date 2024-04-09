use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Deref, DerefMut};
use std::str::FromStr;
use std::sync::Arc;

use anyhow::{bail, Context, Result};
use indexmap::IndexMap;
use serde_json::Number as JsonNumber;
pub use serde_json::to_value as to_json_value;
pub use serde_json::Value as JsonValue;

pub type Value = ArcValue;
// pub type Map = JsonObj<String, JsonValue>;
pub type Map = ObjBuilder;

pub type ObjMap = IndexMap<String, ArcValue>;

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

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum ArcValue {
    Null,
    Bool(bool),
    Number(ArcNum),
    String(ArcStr),
    Array(ArcArray),
    Object(ArcObj),
}

#[derive(Clone, PartialEq, PartialOrd)]
pub struct ArcArray(Arc<Vec<ArcValue>>);

impl ArcArray {
    pub fn iter(&self) -> impl Iterator<Item = &ArcValue> {
        self.0.iter()
    }
}

impl Debug for ArcArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let x = &*self.0;
        write!(f, "{x:?}")
    }
}

impl Display for ArcArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self.0.iter() {
            if !first {
                write!(f, ",")?;
            }
            first = false;
            write!(f, "{v}")?
        }
        write!(f, "]")
    }
}

#[derive(Clone, PartialEq)]
pub struct ArcNum(JsonNumber);
impl<T: Into<JsonNumber>> From<T> for ArcNum {
    fn from(value: T) -> Self {
        Self(value.into())
    }
}

impl ArcNum {
    pub fn as_f64(&self) -> Option<f64> {
        self.0.as_f64()
    }

    pub fn as_bigint(&self) -> Option<i64> {
        self.0.as_i64()
    }
}

impl PartialOrd for ArcNum {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0
            .as_f64()
            .unwrap()
            .partial_cmp(&other.0.as_f64().unwrap())
    }
}

impl Debug for ArcNum {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let x = &self.0;
        write!(f, "{x}")
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub struct ArcObj(Arc<ObjMap>);

impl Display for ArcObj {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for (k, v) in self.0.iter() {
            if !first {
                write!(f, ",")?;
            }
            first = false;
            write!(f, "\"{k}\":{v}")?
        }
        write!(f, "}}")
    }
}

impl ArcObj {
    pub fn new() -> Self {
        Self(Default::default())
    }

    pub fn new_from(&self) -> ObjBuilder {
        let a = (*self.0).clone();
        ObjBuilder(ArcValue::Object(Self(Arc::new(a))))
    }

    pub fn get_mut_obj(&mut self) -> Option<&mut ObjMap> {
        Arc::get_mut(&mut self.0)
    }

    fn keys(&self) -> Vec<&str> {
        let mut keys = self.0.keys().map(|s| s.as_str()).collect::<Vec<_>>();
        keys.sort();
        keys
    }
}

impl PartialOrd for ArcObj {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let keys_a = self.keys();
        let keys_b = other.keys();
        let k = keys_a.partial_cmp(&keys_b);
        if k != Some(Ordering::Equal) {
            return k;
        };
        for key in keys_a {
            let x = self
                .0
                .get(key)
                .unwrap()
                .partial_cmp(other.0.get(key).unwrap());
            if x != Some(Ordering::Equal) {
                return x;
            }
        }
        Some(Ordering::Equal)
    }
}

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ObjBuilder(ArcValue);

impl ObjBuilder {
    pub fn new() -> Self {
        Self(ArcValue::Object(ArcObj::new()))
    }

    fn get_mut_map(&mut self) -> &mut ObjMap {
        let ArcValue::Object(ArcObj(ref mut obj)) = self.0 else {
            unreachable!()
        };
        Arc::get_mut(obj).unwrap()
    }

    pub fn insert(&mut self, key: String, value: ArcValue) {
        self.get_mut_map().insert(key, value);
    }
}

impl Deref for ObjBuilder {
    type Target = ObjMap;

    fn deref(&self) -> &Self::Target {
        let ArcValue::Object(ArcObj(ref obj)) = self.0 else {
            unreachable!()
        };
        obj
    }
}

impl DerefMut for ObjBuilder {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut_map()
    }
}

impl Default for ObjBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl From<ObjBuilder> for ArcValue {
    fn from(value: ObjBuilder) -> Self {
        value.0
    }
}

impl ArcObj {
    pub fn get(&self, key: impl AsRef<str>) -> Option<&ArcValue> {
        self.0.get(key.as_ref())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct ArcStr(Arc<String>);
impl Debug for ArcStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let x = &self.0;
        write!(f, "{x:?}")
    }
}

impl From<String> for ArcStr {
    fn from(value: String) -> Self {
        Self(Arc::new(value))
    }
}

impl From<ArcStr> for ArcValue {
    fn from(value: ArcStr) -> Self {
        Self::String(value)
    }
}

impl From<&ArcStr> for ArcValue {
    fn from(value: &ArcStr) -> Self {
        Self::String(value.clone())
    }
}

impl Deref for ArcStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0.as_str()
    }
}

impl ArcValue {
    pub fn as_array(&self) -> Option<&[Self]> {
        if let Self::Array(ArcArray(a)) = self {
            Some(a.as_slice())
        } else {
            None
        }
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Self::Number(num) = self {
            num.as_f64()
        } else {
            None
        }
    }

    pub fn as_bigint(&self) -> Option<i64> {
        if let Self::Number(num) = self {
            num.as_bigint()
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(ArcStr(s)) = self {
            Some(s.as_str())
        } else {
            None
        }
    }

    pub fn as_mut_obj(&mut self) -> Option<&mut ObjMap> {
        if let Self::Object(obj) = self {
            obj.get_mut_obj()
        } else {
            None
        }
    }
}

impl From<JsonValue> for ArcValue {
    fn from(value: JsonValue) -> Self {
        match value {
            JsonValue::Null => Self::Null,
            JsonValue::Bool(b) => Self::Bool(b),
            JsonValue::Number(n) => Self::Number(n.into()),
            JsonValue::String(s) => Self::String(s.into()),
            JsonValue::Array(a) => {
                let v = a.into_iter().map(|v| v.into()).collect();
                Self::Array(ArcArray(Arc::new(v)))
            }
            JsonValue::Object(o) => {
                let mut obj = ObjBuilder::new();
                for (k, v) in o.into_iter() {
                    obj.insert(k, v.into());
                }
                obj.into()
            }
        }
    }
}

impl From<f64> for ArcValue {
    fn from(value: f64) -> Self {
        JsonValue::from(value).into()
    }
}

impl From<usize> for ArcValue {
    fn from(value: usize) -> Self {
        JsonValue::from(value).into()
    }
}

impl From<i32> for ArcValue {
    fn from(value: i32) -> Self {
        Self::Number(ArcNum(value.into()))
    }
}

impl From<()> for ArcValue {
    fn from(_: ()) -> Self {
        Self::Null
    }
}

impl From<bool> for ArcValue {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

impl From<Vec<ArcValue>> for ArcValue {
    fn from(value: Vec<ArcValue>) -> Self {
        Self::Array(ArcArray(Arc::new(value)))
    }
}

impl From<&str> for ArcValue {
    fn from(value: &str) -> Self {
        value.to_owned().into()
    }
}

impl From<String> for ArcValue {
    fn from(value: String) -> Self {
        Self::String(ArcStr::from(value))
    }
}

impl FromStr for ArcValue {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        Ok(JsonValue::from_str(s).context("Invalid json value")?.into())
    }
}

impl Display for ArcValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ArcValue::Array(a) => write!(f, "{a}"),
            ArcValue::Bool(b) => write!(f, "{b:?}"),
            ArcValue::Number(n) => {
                write!(f, "{n:?}")
            }
            ArcValue::Null => write!(f, "null"),
            ArcValue::Object(o) => {
                write!(f, "{o}")
            }
            ArcValue::String(s) => {
                let s = s.0.as_str();
                write!(f, "\"{s}\"")
            }
        }
    }
}

impl ArcValue {
    pub fn slice(&self, start: &Self, end: &Self) -> Result<Self> {
        let start = start.as_bigint().context("Start index must be integer")? as usize;
        let end = end.as_bigint().context("end index must be integer")? as usize;
        match self {
            ArcValue::Array(a) => {
                let input = &a.0;
                let len = input.len();
                let start = start.min(len);
                let end = end.min(len);
                let new = Vec::from(&input[start..end]);
                Ok(Self::from(new))
            }
            ArcValue::String(s) => {
                let input = &s.0;
                let len = input.len();
                let start = start.min(len);
                let end = end.min(len);
                let new = input[start..end].to_owned(); // FIXME: slice at UTF boundaries
                Ok(Self::from(new))
            }
            _ => bail!("Only arrays and strings can be sliced."),
        }
    }
}

impl ValueOps for ArcValue {
    fn add(&self, other: &Self) -> Result<Self> {
        Ok(match (self, other) {
            (Self::Null, b) => b.clone(),
            (a, Self::Null) => a.clone(),
            (Self::Array(a), Self::Array(b)) => {
                a.iter().chain(b.iter()).cloned().collect::<Vec<_>>().into()
            }

            (Self::Number(a), Self::Number(b)) => {
                if let (Some(a), Some(b)) = (a.as_bigint(), b.as_bigint()) {
                    Self::Number((a + b).into())
                } else {
                    (a.0.as_f64().unwrap() + b.0.as_f64().unwrap()).into()
                }
            }
            (Self::Object(a), Self::Object(b)) => {
                let mut sum = a.new_from();
                sum.extend(b.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                sum.into()
            }
            (Self::String(a), Self::String(b)) => {
                let mut a = a.0.as_str().to_owned();
                a.push_str(b.0.as_str());
                Self::from(a)
            }
            (a, b) => bail!("Can't add {a:?} and {b:?}"),
        })
    }

    fn sub(&self, other: &Self) -> Result<Self> {
        Ok(match (self, other) {
            (Self::Number(a), Self::Number(b)) => {
                if let (Some(a), Some(b)) = (a.as_bigint(), b.as_bigint()) {
                    Self::Number((a - b).into())
                } else {
                    (a.0.as_f64().unwrap() - b.0.as_f64().unwrap()).into()
                }
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
        let idx = index.as_f64().context("Index is not a number")?;
        let idx: usize = if idx >= 0.0 {
            idx
        } else {
            self.length()?.as_f64().unwrap() + idx
        } as _;
        if let Self::Array(v) = self {
            return Ok(v.0.get(idx).cloned().unwrap_or(Self::Null));
        }

        bail!("Cant index {} with {}", self, index)
    }

    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Self> + '_>> {
        match self {
            Self::Array(v) => Ok(Box::new(v.iter())),
            Self::Object(o) => Ok(Box::new(o.0.iter().map(|(_k, v)| v))),
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
            Self::String(s) => s.0.len(),
            Self::Array(a) => a.0.len(),
            Self::Object(o) => o.0.len(),
        };
        Ok(len.into())
    }
}

#[cfg(test)]
mod value_tests {
    use super::*;

    #[test]
    fn test_index() {
        let arr = ArcValue::from_str("[1,2,3,4]").unwrap();
        let neg1: ArcValue = (-1.0f64).into();

        assert_eq!(arr.index(&0i32.into()).unwrap(), 1i32.into());
        assert_eq!(arr.index(&1i32.into()).unwrap(), 2i32.into());
        assert_eq!(arr.index(&neg1).unwrap(), 4i32.into());
    }
}
