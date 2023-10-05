use std::cell::RefCell;
use std::iter;

use anyhow::{bail, Result};
use serde_json::{Map, Value};

use crate::interpreter::ast_eval::{ExprValue, VarScope};
use crate::parser::ast::{Expr, ExprVisitor};
use crate::value::ValueOps;

pub struct BindVars<'v, 'r> {
    scope: &'r VarScope,
    val_iter: RefCell<ValIter<'v>>,
    current_obj: RefCell<Option<&'v Map<String, Value>>>,
    curr_obj_val: RefCell<&'v Value>,
}

type ValIter<'v> = Box<dyn Iterator<Item = &'v Value> + 'v>;

impl<'v, 'r> BindVars<'v, 'r> {
    pub fn bind(values: &'v Value, pattern: &Expr, scope: &'r VarScope) -> Result<()> {
        let this = Self {
            scope,
            val_iter: RefCell::new(Box::new(iter::once(values))),
            current_obj: Default::default(),
            curr_obj_val: RefCell::new(&Value::Null),
        };
        pattern.accept(&this)
    }

    fn expect_array(&self) -> Result<ValIter<'v>> {
        let array = self.val_iter.borrow_mut().next();
        if let Some(Value::Array(elems)) = array {
            Ok(self.val_iter.replace(Box::new(elems.iter())))
        } else {
            bail!("Expected array in value for binding.")
        }
    }

    fn expect_object(&self) -> Result<Option<&'v Map<String, Value>>> {
        let object = self.val_iter.borrow_mut().next();
        if let Some(Value::Object(map)) = object {
            Ok(self.current_obj.replace(Some(map)))
        } else {
            bail!("Expected object in value for binding.")
        }
    }

    fn expect_value(&self) -> ExprValue {
        self.val_iter
            .borrow_mut()
            .next()
            .unwrap_or(&Value::Null)
            .clone()
            .to_expr_result()
            .unwrap()
    }
}

type VisitorRet = Result<()>;

impl ExprVisitor<Result<()>> for BindVars<'_, '_> {
    fn default(&self) -> VisitorRet {
        bail!("Invalid variable binding pattern.");
    }

    fn visit_array(&self, elements: &[Expr]) -> VisitorRet {
        let prev_iter = self.expect_array()?;
        for e in elements {
            e.accept(self)?;
        }
        let _ = self.val_iter.replace(prev_iter);
        Ok(())
    }

    fn visit_ident(&self, ident: &str) -> Result<()> {
        let obj = self.current_obj.borrow();
        if obj.is_some() {
            self.curr_obj_val
                .replace(obj.map(|o| o.get(ident).unwrap_or(&Value::Null)).unwrap());
        } else {
            bail!("Unexpected identifier in binding pattern.")
        }
        Ok(())
    }

    fn visit_object(&self, members: &[Expr]) -> Result<()> {
        let prev_obj = self.expect_object()?;
        members.iter().try_for_each(|m| m.accept(self))?;
        self.current_obj.replace(prev_obj);
        Ok(())
    }

    fn visit_obj_entry(&self, key: &Expr, value: &Expr) -> Result<()> {
        key.accept(self)?;
        let v = self.curr_obj_val.replace(&Value::Null);
        let prev_iter = self.val_iter.replace(Box::new(iter::once(v)));
        value.accept(self)?;
        let _ = self.val_iter.replace(prev_iter);

        Ok(())
    }

    fn visit_variable(&self, name: &str) -> VisitorRet {
        self.scope.set_variable(name, self.expect_value());
        Ok(())
    }
}
