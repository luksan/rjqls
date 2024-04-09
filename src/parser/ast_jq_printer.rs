#![allow(clippy::option_map_unit_fn)]

use std::cell::{Cell, RefCell};

use crate::parser::expr_ast::{
    Ast, AstNode, BinOps, BreakLabel, Expr, ExprVisitor, FuncDef, ObjectEntry,
};
use crate::value::Value;

pub struct ExprPrinter {
    r: RefCell<String>,
}

impl ExprPrinter {
    fn new() -> Self {
        Self {
            r: Default::default(),
        }
    }

    pub fn format(expr: &Expr) -> String {
        let this = Self::new();
        expr.accept(&this);
        this.r.take()
    }

    fn putc(&self, c: char) {
        self.r.borrow_mut().push(c);
    }

    fn puts(&self, s: &str) {
        self.r.borrow_mut().push_str(s);
    }
}

#[allow(clippy::unused_unit)]
impl ExprVisitor<'_, ()> for ExprPrinter {
    fn default(&self) -> () {
        todo!()
    }

    fn visit_alternative(&self, lhs: &AstNode, defaults: &AstNode) -> () {
        lhs.accept(self);
        self.puts("//");
        defaults.accept(self);
    }
    fn visit_array(&self, elements: &[AstNode]) -> () {
        self.putc('[');
        let mut it = elements.iter();
        if let Some(first) = it.next() {
            first.accept(self);
            for e in it {
                self.putc(',');
                e.accept(self);
            }
        }
        self.putc(']')
    }

    fn visit_bind_vars(&self, vals: &Ast, vars: &Ast, rhs: &Ast) -> () {
        vals.accept(self);
        self.puts(" as ");
        vars.accept(self);
        self.putc('|');
        rhs.accept(self);
    }

    fn visit_binop(&self, op: BinOps, lhs: &Ast, rhs: &Ast) -> () {
        lhs.accept(self);
        self.puts(&format!(" {op} "));
        rhs.accept(self);
    }

    fn visit_break(&self, name: &BreakLabel) -> () {
        self.puts("break $");
        self.puts(name.as_str());
    }

    fn visit_breakpoint(&self, expr: &'_ Ast) -> () {
        self.puts("§(");
        expr.accept(self);
        self.putc(')');
    }

    fn visit_call(&self, name: &str, args: &[AstNode]) -> () {
        self.puts(name);
        if !args.is_empty() {
            self.putc('(');
            args[0].accept(self);
            for arg in &args[1..] {
                self.puts("; ");
                arg.accept(self);
            }

            self.putc(')');
        }
    }

    fn visit_comma(&self, lhs: &AstNode, rhs: &AstNode) -> () {
        lhs.accept(self);
        self.putc(',');
        rhs.accept(self);
    }

    fn visit_func_scope(&self, funcs: &[FuncDef], rhs: &AstNode) {
        for FuncDef { name, args, body } in funcs {
            self.puts("def ");
            self.puts(name);
            if !args.is_empty() {
                self.putc('(');
                self.puts(args[0].as_str());
                args[1..].iter().for_each(|a| {
                    self.puts("; ");
                    self.puts(a.as_str());
                });
                self.putc(')');
            }
            self.puts(": ");
            body.accept(self);
            self.puts("; ");
        }
        rhs.accept(self)
    }

    fn visit_dot(&self) -> () {
        self.putc('.')
    }

    fn visit_ident(&self, ident: &str) -> () {
        self.puts(ident)
    }

    fn visit_if_else(&self, cond: &[AstNode], branches: &[AstNode]) -> () {
        self.puts("if ");
        cond[0].accept(self);
        self.puts(" then ");
        branches[0].accept(self);
        for (c, b) in cond[1..].iter().zip(branches[1..].iter()) {
            self.puts(" elif ");
            c.accept(self);
            self.puts(" then ");
            b.accept(self);
        }
        self.puts(" else ");
        branches.last().unwrap().accept(self);
        self.puts(" end");
    }

    fn visit_index(&self, expr: &AstNode, idx: Option<&AstNode>) -> () {
        if self.r.borrow().as_bytes().last() != Some(&b']') || !matches!(&**expr, Expr::Dot) {
            // don't emit redundant dots
            expr.accept(self);
        }
        if let Some(Expr::Ident(ident)) = idx.map(|e| &**e) {
            if !matches!(&**expr, Expr::Dot) {
                self.putc('.');
            }
            self.puts(ident);
        } else {
            self.putc('[');
            idx.map(|idx| idx.accept(self));
            self.putc(']');
        }
    }

    fn visit_literal(&self, lit: &Value) -> () {
        self.puts(&lit.to_string())
    }

    fn visit_object(&self, entries: &[ObjectEntry]) -> () {
        self.putc('{');
        let mut it = entries.iter();
        let put_entry = |e: &ObjectEntry| {
            e.key.accept(self);
            self.puts(": ");
            e.value.accept(self);
        };
        it.next().map(put_entry);
        it.for_each(|e| {
            self.putc(',');
            put_entry(e)
        });
        self.putc('}');
    }

    fn visit_labeled_pipe(&self, label: &BreakLabel, lhs: &AstNode, rhs: &AstNode) -> () {
        lhs.accept(self);
        assert_eq!(Some('.'), self.r.borrow_mut().pop()); // remove the Dot
        self.puts("label $");
        self.puts(label.as_str());
        self.putc('|');
        rhs.accept(self);
    }

    fn visit_pipe(&self, lhs: &AstNode, rhs: &AstNode) -> () {
        lhs.accept(self);
        if !matches!(&**lhs, Expr::Index(_, _)) || !ChainedIndexPipeRemover::check(rhs) {
            self.putc('|');
        }
        rhs.accept(self);
    }

    fn visit_foreach(
        &self,
        input: &'_ AstNode,
        var: &'_ str,
        init: &'_ AstNode,
        update: &'_ AstNode,
        extract: &'_ AstNode,
    ) -> () {
        self.puts("foreach");
        input.accept(self);
        self.puts(" as $");
        self.puts(var);
        self.putc('(');
        init.accept(self);
        self.putc(';');
        update.accept(self);
        self.putc(';');
        extract.accept(self);
        self.putc(')');
    }

    fn visit_reduce(&self, input: &AstNode, var: &str, init: &AstNode, update: &AstNode) -> () {
        self.puts("reduce ");
        input.accept(self);
        self.puts(" as $");
        self.puts(var);
        self.putc('(');
        init.accept(self);
        self.putc(';');
        update.accept(self);
        self.putc(')');
    }

    fn visit_scope(&self, inner: &AstNode) -> () {
        self.putc('(');
        inner.accept(self);
        self.putc(')');
    }

    fn visit_slice(
        &self,
        expr: &AstNode,
        start: Option<&'_ AstNode>,
        end: Option<&'_ AstNode>,
    ) -> () {
        expr.accept(self);
        self.putc('[');
        start.map(|s| s.accept(self));
        self.putc(':');
        end.map(|s| s.accept(self));
        self.putc(']');
    }

    fn visit_string_interp(&self, parts: &[AstNode]) -> () {
        self.putc('"');
        for part in parts {
            if let Expr::Literal(str_lit) = &**part {
                if let Some(s) = str_lit.as_str() {
                    self.puts(s);
                    continue;
                }
            }
            self.puts("\\(");
            part.accept(self);
            self.putc(')');
        }
        self.putc('"');
    }

    fn visit_try_catch(&self, try_expr: &'_ AstNode, catch_expr: Option<&'_ AstNode>) -> () {
        if matches!(&**try_expr, Expr::Index(_, _)) && catch_expr.is_none() {
            try_expr.accept(self);
            self.putc('?');
            return;
        }
        self.puts("try ");
        try_expr.accept(self);
        if let Some(catch_expr) = catch_expr {
            self.puts(" catch ");
            catch_expr.accept(self);
        }
    }

    fn visit_update_assign(&self, path: &'_ AstNode, assign: &'_ AstNode) -> () {
        path.accept(self);
        self.puts(" |= ");
        assign.accept(self);
    }

    fn visit_variable(&self, name: &str) -> () {
        self.putc('$');
        self.puts(name);
    }
}

struct ChainedIndexPipeRemover {
    is_chained_idx: Cell<bool>,
}

impl ChainedIndexPipeRemover {
    fn new() -> Self {
        Self {
            is_chained_idx: false.into(),
        }
    }

    fn check(expr: &AstNode) -> bool {
        let s = Self::new();
        expr.accept(&s);
        s.is_chained_idx.get()
    }
}

impl ExprVisitor<'_, ()> for ChainedIndexPipeRemover {
    fn default(&self) {
        self.is_chained_idx.set(false);
    }

    fn visit_dot(&self) {
        // dot found, we're done
    }

    fn visit_index(&self, expr: &AstNode, _idx: Option<&AstNode>) {
        self.is_chained_idx.set(true);
        expr.accept(self)
    }

    fn visit_try_catch(&self, try_expr: &AstNode, catch_expr: Option<&AstNode>) {
        if catch_expr.is_some() {
            // not a postfix try
            self.default();
            return;
        }
        try_expr.accept(self)
    }
}
