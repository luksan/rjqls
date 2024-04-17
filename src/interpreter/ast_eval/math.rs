use crate::bail;

use super::*;

pub(super) fn floor(input: &Value) -> EvalVisitorRet<'static> {
    if input.as_bigint().is_some() {
        input.clone().into()
    } else if let Some(f) = input.as_f64() {
        Value::from(f.floor() as i32).into()
    } else {
        bail!("{input:?} number required")
    }
}
