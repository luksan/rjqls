use crate::parser::ast::Value;

// Parse incoming JSON data

pub struct ValueStream {}

impl ValueStream {
    pub fn next_value(&mut self) -> Option<Value> {
        unimplemented!()
    }
}
