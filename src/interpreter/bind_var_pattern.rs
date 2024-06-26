use std::cell::RefCell;
use std::iter;
use std::sync::Arc;

use anyhow::{bail, Result};
use tracing::{instrument, trace};

use crate::interpreter::ast_eval::VarScope;
use crate::parser::expr_ast::{AstNode, ExprVisitor, ObjectEntry};
use crate::value::ArcObj;
use crate::value::Value;

pub struct BindVars<'v, 'r> {
    scope: RefCell<Arc<VarScope<'r>>>,
    val_iter: RefCell<ValIter<'v>>,
    current_obj: RefCell<Option<&'v ArcObj>>,
    curr_obj_val: RefCell<&'v Value>,
}

type ValIter<'v> = Box<dyn Iterator<Item = &'v Value> + 'v>;

impl<'v, 'r> BindVars<'v, 'r> {
    #[instrument(skip(scope))]
    pub fn bind(
        values: &'v Value,
        pattern: &'r AstNode,
        scope: &Arc<VarScope<'r>>,
    ) -> Result<Arc<VarScope<'r>>> {
        let this = Self {
            scope: scope.clone().into(),
            val_iter: RefCell::new(Box::new(iter::once(values))),
            current_obj: Default::default(),
            curr_obj_val: RefCell::new(&Value::Null),
        };
        pattern.accept(&this)?;
        Ok(this.scope.into_inner())
    }

    fn expect_array(&self) -> Result<ValIter<'v>> {
        let array = self.val_iter.borrow_mut().next();
        if let Some(Value::Array(elems)) = array {
            Ok(self.val_iter.replace(Box::new(elems.iter())))
        } else {
            bail!("Expected array in value for binding.")
        }
    }

    fn expect_object(&self) -> Result<Option<&'v ArcObj>> {
        let object = self.val_iter.borrow_mut().next();
        if let Some(Value::Object(map)) = object {
            Ok(self.current_obj.replace(Some(map)))
        } else {
            bail!("Expected object in value for binding.")
        }
    }

    fn expect_value(&self) -> Value {
        self.val_iter
            .borrow_mut()
            .next()
            .unwrap_or(&Value::Null)
            .clone()
    }
}

type VisitorRet = Result<()>;

impl<'r> ExprVisitor<'r, Result<()>> for BindVars<'_, 'r> {
    fn default(&self) -> VisitorRet {
        bail!("Invalid variable binding pattern.");
    }

    fn visit_array(&self, elements: &'r [AstNode]) -> VisitorRet {
        let prev_iter = self.expect_array()?;
        for e in elements {
            e.accept(self)?;
        }
        let _ = self.val_iter.replace(prev_iter);
        Ok(())
    }

    fn visit_ident(&self, ident: &'r str) -> VisitorRet {
        let obj = self.current_obj.borrow();
        if obj.is_some() {
            self.curr_obj_val
                .replace(obj.map(|o| o.get(ident).unwrap_or(&Value::Null)).unwrap());
        } else {
            bail!("Unexpected identifier in binding pattern.")
        }
        Ok(())
    }

    fn visit_object(&self, entries: &'r [ObjectEntry]) -> VisitorRet {
        let prev_obj = self.expect_object()?;
        for e in entries {
            e.key.accept(self)?;
            let v = self.curr_obj_val.replace(&Value::Null);
            let prev_iter = self.val_iter.replace(Box::new(iter::once(v)));
            e.value.accept(self)?;
            let _ = self.val_iter.replace(prev_iter);
        }
        self.current_obj.replace(prev_obj);
        Ok(())
    }

    fn visit_variable(&self, name: &'r str) -> VisitorRet {
        let value = self.expect_value();
        trace!("Binding '{name}' to {value:?}");
        let mut scope = self.scope.borrow_mut();
        *scope = scope.set_variable(name, value);
        Ok(())
    }
}
