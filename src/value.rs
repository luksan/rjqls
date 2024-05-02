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

    fn del(&self, index: &Self) -> Result<Self>;
    fn replace_field(self, index: &Self, f: impl FnOnce(Self) -> Result<Self>) -> Result<Self>;

    fn is_truthy(&self) -> bool;
    fn less_than(&self, other: &Self) -> Self;
    fn index(&self, index: &Self) -> Result<Self>;
    fn iterate(&self) -> Result<Box<dyn Iterator<Item = &Self> + '_>>;

    fn length(&self) -> Result<Self>;
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArcValue {
    Null,
    Bool(bool),
    Number(ArcNum),
    String(ArcStr),
    Array(ArcArray),
    Object(ArcObj),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ArcArray(Arc<Vec<ArcValue>>);

impl ArcArray {
    pub fn iter(&self) -> impl Iterator<Item = &ArcValue> {
        self.0.iter()
    }

    fn get_usize_idx(&self, idx: f64) -> Option<usize> {
        let idx: usize = if idx >= 0.0 {
            idx
        } else {
            self.0.len() as f64 + idx
        } as _;
        (idx < self.0.len()).then_some(idx)
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

#[derive(Clone)]
pub struct ArcNum(JsonNumber);

mod arc_num {
    use super::*;

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

    impl PartialEq for ArcNum {
        fn eq(&self, other: &Self) -> bool {
            if let (Some(a), Some(b)) = (self.as_bigint(), other.as_bigint()) {
                return a == b;
            }
            self.as_f64().unwrap().total_cmp(&other.as_f64().unwrap()) == Ordering::Equal
        }
    }

    impl Eq for ArcNum {}

    impl Ord for ArcNum {
        fn cmp(&self, other: &Self) -> Ordering {
            self.as_f64().unwrap().total_cmp(&other.as_f64().unwrap())
        }
    }

    impl PartialOrd for ArcNum {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Debug for ArcNum {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let x = &self.0;
            write!(f, "{x}")
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ArcObj(Arc<ObjMap>);

#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct ObjBuilder(ArcValue);

mod arc_obj {
    use super::*;

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

        pub fn get(&self, key: impl AsRef<str>) -> Option<&ArcValue> {
            self.0.get(key.as_ref())
        }

        pub fn get_mut_obj(&mut self) -> Option<&mut ObjMap> {
            Arc::get_mut(&mut self.0)
        }

        /// returns the keys as a sorted Vec
        fn keys(&self) -> Vec<&str> {
            let mut keys = self.0.keys().map(|s| s.as_str()).collect::<Vec<_>>();
            keys.sort();
            keys
        }
    }

    impl PartialOrd for ArcObj {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for ArcObj {
        fn cmp(&self, other: &Self) -> Ordering {
            // begin with comparing all sorted keys, then compare the values
            let keys_a = self.keys();
            let keys_b = other.keys();
            let k = keys_a.cmp(&keys_b);
            if k != Ordering::Equal {
                return k;
            };
            // compare the values in sorted key order
            for key in keys_a {
                let x = self.0.get(key).unwrap().cmp(other.0.get(key).unwrap());
                if x != Ordering::Equal {
                    return x;
                }
            }
            Ordering::Equal
        }
    }

    impl ObjBuilder {
        pub fn new() -> Self {
            Self(ArcValue::Object(ArcObj::new()))
        }

        fn get_mut_map(&mut self) -> &mut ObjMap {
            let ArcValue::Object(ArcObj(ref mut obj)) = self.0 else { unreachable!() };
            Arc::get_mut(obj).unwrap()
        }

        pub fn insert(&mut self, key: String, value: ArcValue) {
            self.get_mut_map().insert(key, value);
        }
    }

    impl Deref for ObjBuilder {
        type Target = ObjMap;

        fn deref(&self) -> &Self::Target {
            let ArcValue::Object(ArcObj(ref obj)) = self.0 else { unreachable!() };
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
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArcStr(Arc<String>);
mod arc_str {
    use super::*;

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
}

impl ArcValue {
    pub fn type_name(&self) -> &'static str {
        match self {
            ArcValue::Null => "null",
            ArcValue::Bool(_) => "bool",
            ArcValue::Number(_) => "number",
            ArcValue::String(_) => "string",
            ArcValue::Array(_) => "array",
            ArcValue::Object(_) => "object",
        }
    }

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

pub mod from_impls {
    use super::*;

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

    impl From<i64> for ArcValue {
        fn from(value: i64) -> Self {
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

    fn del(&self, index: &Self) -> Result<Self> {
        match self {
            ArcValue::Array(a) => {
                let Some(idx) = index.as_f64() else {
                    bail!("Cannot delete {} element of array", index.type_name())
                };
                let Some(idx) = a.get_usize_idx(idx) else {
                    return Ok(self.clone());
                };
                let mut new = (*a.0).clone();
                new.remove(idx);
                Ok(new.into())
            }
            ArcValue::Object(o) => {
                let Some(idx) = index.as_str() else {
                    bail!("Cannot delete {} field from object", index.type_name())
                };
                if !o.0.contains_key(idx) {
                    return Ok(self.clone());
                }
                let mut new = (*o.0).clone();
                new.shift_remove(idx);
                Ok(ArcValue::Object(ArcObj(Arc::new(new))))
            }
            _ => bail!("Can't delete fields from {}", self.type_name()),
        }
    }

    fn replace_field(self, index: &Self, f: impl FnOnce(Self) -> Result<Self>) -> Result<Self> {
        let slot_val = self.index(index)?;
        match self {
            ArcValue::Array(mut a) => {
                let slot_idx = a.get_usize_idx(index.as_f64().unwrap()).unwrap();
                let new_array = Arc::make_mut(&mut a.0);
                new_array[slot_idx] = f(slot_val)?;
                Ok(ArcValue::Array(a))
            }
            ArcValue::Object(mut o) => {
                let key = index.as_str().unwrap();
                let new_obj = Arc::make_mut(&mut o.0);
                new_obj[key] = f(slot_val)?;
                Ok(ArcValue::Object(o))
            }
            _ => unreachable!("Can't index or replace in this value kind"),
        }
    }

    fn index(&self, index: &Self) -> Result<Self> {
        let str_idx = index.as_str();
        let num_idx = index.as_f64();
        if str_idx.is_some() || num_idx.is_some() {
            match self {
                ArcValue::Null => return Ok(ArcValue::Null),
                ArcValue::Array(v) => {
                    let idx = num_idx.context("Index is not a number")?;
                    return Ok(v
                        .get_usize_idx(idx)
                        .map(|idx| v.0[idx].clone())
                        .unwrap_or(ArcValue::Null));
                }
                ArcValue::Object(o) => {
                    let idx =
                        str_idx.with_context(|| format!("Can't index object with {index}."))?;
                    return Ok(o.get(idx).cloned().unwrap_or(Self::Null));
                }
                _ => {}
            }
        }
        bail!(
            "Cant index {} with {} {}",
            self.type_name(),
            index.type_name(),
            index
        )
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
    use itertools::Itertools;

    use super::*;

    #[test]
    fn test_index() {
        let arr = ArcValue::from_str("[1,2,3,4]").unwrap();
        let neg1: ArcValue = (-1.0f64).into();

        assert_eq!(arr.index(&0i32.into()).unwrap(), 1i32.into());
        assert_eq!(arr.index(&1i32.into()).unwrap(), 2i32.into());
        assert_eq!(arr.index(&neg1).unwrap(), 4i32.into());
    }

    #[test]
    fn test_compare_eq() {
        let tests = [("12", "12.0", true)];
        for (a, b, eq) in tests {
            let a = ArcValue::from_str(a).unwrap();
            let b = ArcValue::from_str(b).unwrap();
            assert_eq!(a == b, eq)
        }
    }

    #[test]
    fn test_sort_order() {
        let strrep = [
            "null",
            "false",
            "true",
            "-1.1",
            "-1",
            "-0.1",
            "-0.0",
            "0.0",
            "0.1",
            "1.0",
            "1",
            "1.1",
            "\"a\"",
            "\"b\"",
            "[1,2]",
            "[1,2,3]",
            "[1,3]",
            "{\"a\":1}",
            "{\"a\":2}",
            "{\"b\":1}",
        ];
        let vals = strrep
            .iter()
            .map(|v| {
                ArcValue::from_str(v)
                    .with_context(|| format!("bad json '{v}'"))
                    .unwrap()
            })
            .collect_vec();
        let mut s = vals.clone();
        s.sort();
        for (&a, b) in strrep.iter().zip(s.iter().map(|v| v.to_string())) {
            assert_eq!(a, b)
        }
    }
}
