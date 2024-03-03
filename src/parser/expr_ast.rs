use std::cell::{Cell, RefCell};
use std::fmt::{Display, Formatter};
use std::str::FromStr;

use anyhow::bail;
use tracing::{instrument, trace};

use crate::value::Value;

macro_rules! binop_str_map {

    ( $($str:literal => $op:ident),+$(,)? ) => {
        #[derive(Debug, Copy, Clone, PartialEq, Eq)]
        pub enum BinOps {
            $($op,)+
        }

        impl FromStr for BinOps {
            type Err = anyhow::Error;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                Ok(match s {
                    $($str => Self::$op,)+
                    _ => bail!("Failed to parse '{s}' as a BinOp"),
                })
            }
        }

        impl BinOps {
            pub fn as_str(&self) -> &'static str {
                match self {
                    $(Self::$op => $str),+
                }
            }
        }
    };
}

binop_str_map!("+" => Add, "-" => Sub, "*" => Mul, "/" => Div,
    "//" => Alt, "and" => And, "or" => Or,
    "==" => Eq, "!=" => NotEq, "<" => Less, ">" => Greater, "<=" => LessEq, ">=" =>  GreaterEq );

impl Display for BinOps {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

pub type Ast = Box<Expr>;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Array(Vec<Expr>),
    Assign(Ast, Ast),
    BindVars(Ast, Ast),
    BinOp(BinOps, Ast, Ast),
    Call(String, Vec<Expr>),
    Comma(Ast, Ast),
    DefineFunc {
        name: String,
        args: Vec<String>,
        body: Ast,
        rhs: Ast,
    },
    Dot,
    ForEach(Ast, String, Ast, Ast, Ast), // input exp, var name, init, update, extract
    Ident(String),
    // the first vec is conditions, the second is true branches, with else as the last element
    IfElse(Vec<Expr>, Vec<Expr>),
    Index(Ast, Option<Ast>), // [2]
    Literal(Value),
    Object(Vec<Expr>),
    ObjectEntry {
        key: Ast,
        value: Ast,
    },
    ObjMember(String), // select object member
    Pipe(Ast, Ast),
    Reduce(Ast, String, Ast, Ast), // inputs, variable name, init, update
    Scope(Ast),
    Slice(Ast, Option<Ast>, Option<Ast>),
    StringInterp(Vec<Expr>),
    TryCatch(Ast, Option<Ast>),
    UpdateAssign(Ast, Ast),
    Variable(String),
    Label(String),
    Break(String),
}
impl Expr {
    #[instrument(name = "A", level = "trace", skip_all)]
    #[allow(unused_variables)] // FIXME remove
    pub fn accept<'e, R>(&'e self, visitor: &(impl ExprVisitor<'e, R> + ?Sized)) -> R {
        trace!("Visiting {self:?}");
        match self {
            Expr::Array(r) => visitor.visit_array(r),
            Expr::Assign(lhs, rhs) => unimplemented!(),
            Expr::BindVars(vals, vars) => visitor.visit_bind_vars(vals, vars),
            Expr::BinOp(op, lhs, rhs) => visitor.visit_binop(*op, lhs, rhs),
            Expr::Break(name) => unimplemented!(),
            Expr::Call(name, args) => visitor.visit_call(name, args.as_slice()),
            Expr::Comma(lhs, rhs) => visitor.visit_comma(lhs, rhs),
            Expr::DefineFunc {
                name,
                args,
                body,
                rhs,
            } => visitor.visit_define_function(name, args, body, rhs),
            Expr::Dot => visitor.visit_dot(),
            Expr::ForEach(expr, var, init, update, extract) => unimplemented!(),
            Expr::Ident(i) => visitor.visit_ident(i),
            Expr::IfElse(cond, branch) => visitor.visit_if_else(cond, branch),
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx.as_deref()),
            Expr::Label(name) => unimplemented!(),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::ObjectEntry { key, value } => visitor.visit_obj_entry(key, value),
            Expr::ObjMember(k) => visitor.visit_obj_member(k),
            Expr::Pipe(lhs, rhs) => visitor.visit_pipe(lhs, rhs),
            Expr::Reduce(input, var, init, update) => {
                visitor.visit_reduce(input, var, init, update)
            }
            Expr::Scope(s) => visitor.visit_scope(s),
            Expr::Slice(expr, start, end) => {
                visitor.visit_slice(expr, start.as_deref(), end.as_deref())
            }
            Expr::StringInterp(parts) => visitor.visit_string_interp(parts.as_slice()),
            Expr::TryCatch(try_expr, catch_expr) => {
                visitor.visit_try_catch(try_expr, catch_expr.as_deref())
            }
            Expr::UpdateAssign(path, assign) => visitor.visit_update_assign(path, assign),
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
pub trait ExprVisitor<'e, R> {
    fn default(&self) -> R;

    fn visit_array(&self, elements: &'e [Expr]) -> R {
        for e in elements {
            e.accept(self);
        }
        self.default()
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast) -> R {
        vals.accept(self);
        vars.accept(self);
        self.default()
    }

    fn visit_binop(&self, op: BinOps, lhs: &'e Ast, rhs: &'e Ast) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_call(&self, name: &str, args: &'e [Expr]) -> R {
        for a in args {
            a.accept(self);
        }
        self.default()
    }
    fn visit_comma(&self, lhs: &'e Expr, rhs: &'e Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_define_function(
        &self,
        name: &'e str,
        args: &'e [String],
        body: &'e Expr,
        rhs: &'e Expr,
    ) -> R {
        rhs.accept(self);
        self.default()
    }
    fn visit_dot(&self) -> R {
        self.default()
    }
    fn visit_ident(&self, ident: &'e str) -> R {
        self.default()
    }
    fn visit_if_else(&self, cond: &'e [Expr], branches: &'e [Expr]) -> R {
        for x in cond.iter().chain(branches.iter()) {
            x.accept(self);
        }
        self.default()
    }
    fn visit_index(&self, expr: &'e Expr, idx: Option<&'e Expr>) -> R {
        expr.accept(self);
        idx.map(|idx| idx.accept(self));
        self.default()
    }
    fn visit_literal(&self, lit: &'e Value) -> R {
        self.default()
    }
    fn visit_object(&self, members: &'e [Expr]) -> R {
        for e in members {
            e.accept(self);
        }
        self.default()
    }
    fn visit_obj_entry(&self, key: &'e Expr, value: &'e Expr) -> R {
        key.accept(self);
        value.accept(self);
        self.default()
    }
    fn visit_obj_member(&self, key: &'e str) -> R {
        self.default()
    }
    fn visit_pipe(&self, lhs: &'e Expr, rhs: &'e Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_reduce(&self, input: &'e Expr, var: &'e str, init: &'e Expr, update: &'e Expr) -> R {
        input.accept(self);
        init.accept(self);
        update.accept(self);
        self.default()
    }
    fn visit_scope(&self, inner: &'e Expr) -> R {
        inner.accept(self);
        self.default()
    }
    fn visit_slice(&self, expr: &'e Expr, start: Option<&'e Expr>, end: Option<&'e Expr>) -> R {
        expr.accept(self);
        start.map(|s| s.accept(self));
        end.map(|s| s.accept(self));
        self.default()
    }
    fn visit_string_interp(&self, parts: &'e [Expr]) -> R {
        for p in parts {
            p.accept(self);
        }
        self.default()
    }
    fn visit_try_catch(&self, try_expr: &'e Expr, catch_expr: Option<&'e Expr>) -> R {
        try_expr.accept(self);
        if let Some(catch_expr) = catch_expr {
            catch_expr.accept(self);
        }
        self.default()
    }
    fn visit_update_assign(&self, path: &'e Expr, assign: &'e Expr) -> R {
        path.accept(self);
        assign.accept(self);
        self.default()
    }
    fn visit_variable(&self, name: &'e str) -> R {
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
impl ExprVisitor<'_, ()> for ExprPrinter {
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
        self.puts(" as ");
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

    fn visit_define_function(&self, name: &str, args: &[String], body: &Expr, rhs: &Expr) -> () {
        self.puts("def ");
        self.puts(name);
        if !args.is_empty() {
            self.putc('(');
            self.puts(args[0].as_str());
            args[1..].iter().for_each(|a| {
                self.puts(", ");
                self.puts(a.as_str());
            });
            self.putc(')');
        }
        self.puts(": ");
        body.accept(self);
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
        if self.r.borrow().as_bytes().last() != Some(&b']') || !matches!(expr, Expr::Dot) {
            // don't emit redundant dots
            expr.accept(self);
        }
        if let Some(Expr::Ident(ident)) = idx {
            if !matches!(expr, Expr::Dot) {
                self.putc('.');
            }
            self.puts(ident);
        } else {
            self.putc('[');
            idx.as_deref().map(|idx| idx.accept(self));
            self.putc(']');
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
        if !matches!(lhs, Expr::Index(_, _)) || !ChainedIndexPipeRemover::check(rhs) {
            self.putc('|');
        }
        rhs.accept(self);
    }

    fn visit_scope(&self, inner: &Expr) -> () {
        self.putc('(');
        inner.accept(self);
        self.putc(')');
    }

    fn visit_slice(&self, expr: &Expr, start: Option<&'_ Expr>, end: Option<&'_ Expr>) -> () {
        expr.accept(self);
        self.putc('[');
        start.map(|s| s.accept(self));
        self.putc(':');
        end.map(|s| s.accept(self));
        self.putc(']');
    }

    fn visit_string_interp(&self, parts: &[Expr]) -> () {
        self.putc('"');
        for part in parts {
            if let Expr::Literal(str_lit) = part {
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

    fn visit_try_catch(&self, try_expr: &'_ Expr, catch_expr: Option<&'_ Expr>) -> () {
        if matches!(try_expr, Expr::Index(_, _)) && catch_expr.is_none() {
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
            is_chained_idx: true.into(),
        }
    }

    fn check(expr: &Expr) -> bool {
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

    fn visit_index(&self, expr: &'_ Expr, _idx: Option<&'_ Expr>) {
        expr.accept(self)
    }

    fn visit_try_catch(&self, try_expr: &'_ Expr, catch_expr: Option<&'_ Expr>) {
        if catch_expr.is_some() {
            // not a postfix try
            self.default();
            return;
        }
        try_expr.accept(self)
    }
}
