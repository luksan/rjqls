use crate::bail;

use super::*;

pub(super) fn floor(input: &Value) -> EvalVisitorRet<'static> {
    if input.as_bigint().is_some() {
        expr_val_from_value(input.clone())
    } else if let Some(f) = input.as_f64() {
        expr_val_from_value(Value::from(f.floor() as i32))
    } else {
        bail!("{input:?} number required")
    }
}
