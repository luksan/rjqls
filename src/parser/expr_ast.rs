use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::str::FromStr;
use std::sync::Arc;

use anyhow::bail;
pub use serde_json::Value;
use tracing::{instrument, trace};

use crate::interpreter::Function;

#[derive(Debug, Copy, Clone)]
pub enum BinOps {
    Add,
    Sub,
    Mul,
    Div,

    Eq,
    NotEq,

    Less,
}

impl FromStr for BinOps {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            ">" => Self::Less,
            _ => bail!("Failed to parse '{s}' as a BinOp"),
        })
    }
}

impl BinOps {
    pub fn as_str(&self) -> &'static str {
        match self {
            BinOps::Add => "+",
            BinOps::Sub => "-",
            BinOps::Mul => "*",
            BinOps::Div => "/",
            BinOps::Eq => "==",
            BinOps::NotEq => "!=",
            BinOps::Less => "<",
        }
    }
}

impl Display for BinOps {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

pub type Ast = Box<Expr>;

#[derive(Debug)]
pub enum Expr {
    Array(Vec<Expr>),
    BindVars(Ast, Ast),
    BinOp(BinOps, Ast, Ast),
    Call(String, Vec<Expr>),
    Comma(Ast, Ast),
    DefineFunc(Arc<Function<'static>>, Ast),
    Dot,
    Ident(String),
    // the first vec is conditions, the second is true branches, with else as the last element
    IfElse(Vec<Expr>, Vec<Expr>),
    Index(Ast, Option<Ast>), // [2]
    Literal(Value),
    Object(Vec<Expr>),
    ObjectEntry { key: Ast, value: Ast },
    ObjMember(String), // select object member
    Pipe(Ast, Ast),
    Reduce(Ast, String, Ast, Ast), // inputs, variable name, init, update
    Scope(Ast),
    Variable(String),
    Label(String),
    Break(String),
}
impl Expr {
    #[instrument(name = "A", level = "trace", skip_all)]
    #[allow(unused_variables)] // FIXME remove
    pub fn accept<R>(&self, visitor: &(impl ExprVisitor<Ret = R> + ?Sized)) -> R {
        trace!("Visiting {self:?}");
        match self {
            Expr::Array(r) => visitor.visit_array(r),
            Expr::BindVars(vals, vars) => visitor.visit_bind_vars(vals, vars),
            Expr::BinOp(op, lhs, rhs) => visitor.visit_binop(*op, lhs, rhs),
            Expr::Break(name) => unimplemented!(),
            Expr::Call(name, args) => visitor.visit_call(name, args.as_slice()),
            Expr::Comma(lhs, rhs) => visitor.visit_comma(lhs, rhs),
            Expr::DefineFunc(func, rhs) => visitor.visit_define_function(func, rhs),
            Expr::Dot => visitor.visit_dot(),
            Expr::Ident(i) => visitor.visit_ident(i),
            Expr::IfElse(cond, branch) => visitor.visit_if_else(cond, branch),
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx.as_ref().map(|ast| &**ast)),
            Expr::Label(name) => unimplemented!(),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::ObjectEntry { key, value } => visitor.visit_obj_entry(key, value),
            Expr::ObjMember(k) => visitor.visit_obj_member(k),
            Expr::Pipe(lhs, rhs) => visitor.visit_pipe(lhs, rhs),
            Expr::Reduce(input, var, init, update) => unimplemented!(),
            Expr::Scope(s) => visitor.visit_scope(s),
            Expr::Variable(s) => visitor.visit_variable(s),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let prnt = ExprPrinter::format(self);
        write!(f, "{prnt}")
    }
}

#[allow(unused_variables)]
pub trait ExprVisitor {
    type Ret;

    fn default(&self) -> Self::Ret;

    fn visit_array(&self, elements: &[Expr]) -> Self::Ret {
        for e in elements {
            e.accept(self);
        }
        self.default()
    }

    fn visit_bind_vars(&self, vals: &Ast, vars: &Ast) -> Self::Ret {
        vals.accept(self);
        vars.accept(self);
        self.default()
    }

    fn visit_binop(&self, op: BinOps, lhs: &Ast, rhs: &Ast) -> Self::Ret {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_call(&self, name: &str, args: &[Expr]) -> Self::Ret {
        for a in args {
            a.accept(self);
        }
        self.default()
    }
    fn visit_comma(&self, lhs: &Expr, rhs: &Expr) -> Self::Ret {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_define_function(&self, func: &Arc<Function<'static>>, rhs: &Expr) -> Self::Ret {
        rhs.accept(self);
        self.default()
    }
    fn visit_dot(&self) -> Self::Ret {
        self.default()
    }
    fn visit_ident(&self, ident: &str) -> Self::Ret {
        self.default()
    }
    fn visit_if_else(&self, cond: &[Expr], branches: &[Expr]) -> Self::Ret {
        for x in cond.iter().chain(branches.iter()) {
            x.accept(self);
        }
        self.default()
    }
    fn visit_index(&self, expr: &Expr, idx: Option<&Expr>) -> Self::Ret {
        expr.accept(self);
        idx.map(|idx| idx.accept(self));
        self.default()
    }
    fn visit_literal(&self, lit: &Value) -> Self::Ret {
        self.default()
    }
    fn visit_object(&self, members: &[Expr]) -> Self::Ret {
        for e in members {
            e.accept(self);
        }
        self.default()
    }
    fn visit_obj_entry(&self, key: &Expr, value: &Expr) -> Self::Ret {
        key.accept(self);
        value.accept(self);
        self.default()
    }
    fn visit_obj_member(&self, key: &str) -> Self::Ret {
        self.default()
    }
    fn visit_pipe(&self, lhs: &Expr, rhs: &Expr) -> Self::Ret {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_scope(&self, inner: &Expr) -> Self::Ret {
        inner.accept(self);
        self.default()
    }
    fn visit_variable(&self, name: &str) -> Self::Ret {
        self.default()
    }
}

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

    pub fn print(expr: &Expr) {
        println!("{}", Self::format(expr))
    }

    fn putc(&self, c: char) {
        self.r.borrow_mut().push(c);
    }

    fn puts(&self, s: &str) {
        self.r.borrow_mut().push_str(s);
    }
}

#[allow(clippy::unused_unit)]
impl ExprVisitor for ExprPrinter {
    type Ret = ();
    fn default(&self) -> () {
        todo!()
    }

    fn visit_array(&self, elements: &[Expr]) -> () {
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

    fn visit_bind_vars(&self, vals: &Ast, vars: &Ast) -> () {
        vals.accept(self);
        self.puts("as");
        vars.accept(self);
    }

    fn visit_binop(&self, op: BinOps, lhs: &Ast, rhs: &Ast) -> () {
        lhs.accept(self);
        self.puts(&format!(" {op} "));
        rhs.accept(self);
    }

    fn visit_call(&self, name: &str, args: &[Expr]) -> () {
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

    fn visit_comma(&self, lhs: &Expr, rhs: &Expr) -> () {
        lhs.accept(self);
        self.putc(',');
        rhs.accept(self);
    }

    fn visit_define_function(&self, func: &Arc<Function<'static>>, rhs: &Expr) -> () {
        self.puts("def ");
        self.puts(func.name());
        self.puts(": ");
        func.filter().accept(self);
        self.puts("; ");
        rhs.accept(self)
    }

    fn visit_dot(&self) -> () {
        self.putc('.')
    }

    fn visit_ident(&self, ident: &str) -> () {
        self.puts(ident)
    }

    fn visit_if_else(&self, cond: &[Expr], branches: &[Expr]) -> () {
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

    fn visit_index(&self, expr: &Expr, idx: Option<&Expr>) -> () {
        expr.accept(self);
        if let Some(idx) = idx {
            idx.accept(self)
        } else {
            self.puts("[]")
        }
    }

    fn visit_literal(&self, lit: &Value) -> () {
        self.puts(&lit.to_string())
    }

    fn visit_object(&self, members: &[Expr]) -> () {
        self.putc('{');
        let mut it = members.iter();
        if let Some(first) = it.next() {
            first.accept(self);
            for e in it {
                self.putc(',');
                e.accept(self);
            }
        }
        self.putc('}');
    }

    fn visit_obj_entry(&self, key: &Expr, value: &Expr) -> () {
        key.accept(self);
        self.puts(": ");
        value.accept(self);
    }

    fn visit_obj_member(&self, key: &str) -> () {
        self.puts(key)
    }

    fn visit_pipe(&self, lhs: &Expr, rhs: &Expr) -> () {
        lhs.accept(self);
        self.putc('|');
        rhs.accept(self);
    }

    fn visit_scope(&self, inner: &Expr) -> () {
        self.putc('(');
        inner.accept(self);
        self.putc(')');
    }

    fn visit_variable(&self, name: &str) -> () {
        self.putc('$');
        self.puts(name);
    }
}
