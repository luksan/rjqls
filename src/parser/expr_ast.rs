use std::fmt::{Debug, Display, Formatter};
use std::ops::Deref;
use std::str::FromStr;

use anyhow::bail;
use pest::Span;
use tracing::{instrument, trace};

use crate::parser::ast_jq_printer::ExprPrinter;
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

pub type Ast = AstLoc;

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Default)]
pub struct SpanLoc {
    start: usize,
    len: usize,
}

impl From<Span<'_>> for SpanLoc {
    fn from(value: Span<'_>) -> Self {
        Self {
            start: value.start(),
            len: value.end() - value.start(),
        }
    }
}

pub struct AstLoc {
    pub expr: Box<Expr>,
    pub span: SpanLoc,
}

impl AstLoc {
    pub fn new(expr: Expr, span: Span<'_>) -> Self {
        Self {
            expr: Box::new(expr),
            span: span.into(),
        }
    }
}

impl Deref for AstLoc {
    type Target = Expr;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl Display for AstLoc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expr)
    }
}

impl Debug for AstLoc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.expr)
        } else {
            write!(f, "{:?}", self.expr)
        }
    }
}

impl PartialEq for AstLoc {
    fn eq(&self, other: &Self) -> bool {
        self.expr == other.expr
    }
}

pub type ExprArray = Vec<Ast>;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Alternative(Ast, Ast),
    Array(ExprArray),
    Assign(Ast, Ast),
    BindVars(Ast, Ast, Ast),
    BinOp(BinOps, Ast, Ast),
    Breakpoint(Ast),
    Call(String, ExprArray),
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
    IfElse(ExprArray, ExprArray),
    Index(Ast, Option<Ast>), // [2]
    Literal(Value),
    Object(Vec<ObjectEntry>),
    Pipe(Ast, Ast),
    Reduce(Ast, String, Ast, Ast), // inputs, variable name, init, update
    Scope(Ast),
    Slice(Ast, Option<Ast>, Option<Ast>),
    StringInterp(ExprArray),
    TryCatch(Ast, Option<Ast>),
    UpdateAssign(Ast, Ast),
    Variable(String),
    Label(String),
    Break(String),
}

#[derive(Debug, PartialEq)]
pub struct ObjectEntry {
    pub key: Ast,
    pub value: Ast,
}

impl Expr {
    #[instrument(name = "A", level = "trace", skip_all)]
    #[allow(unused_variables)] // FIXME remove
    pub fn accept<'e, R>(&'e self, visitor: &(impl ExprVisitor<'e, R> + ?Sized)) -> R {
        trace!("Visiting {self:?}");
        match self {
            Expr::Alternative(lhs, rhs) => visitor.visit_alternative(lhs, rhs),
            Expr::Array(r) => visitor.visit_array(r),
            Expr::Assign(lhs, rhs) => unimplemented!(),
            Expr::BindVars(vals, vars, rhs) => visitor.visit_bind_vars(vals, vars, rhs),
            Expr::BinOp(op, lhs, rhs) => visitor.visit_binop(*op, lhs, rhs),
            Expr::Break(name) => unimplemented!(),
            Expr::Breakpoint(ast) => visitor.visit_breakpoint(ast),
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
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx.as_ref()),
            Expr::Label(name) => unimplemented!(),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::Pipe(lhs, rhs) => visitor.visit_pipe(lhs, rhs),
            Expr::Reduce(input, var, init, update) => {
                visitor.visit_reduce(input, var, init, update)
            }
            Expr::Scope(s) => visitor.visit_scope(s),
            Expr::Slice(expr, start, end) => {
                visitor.visit_slice(expr, start.as_ref(), end.as_ref())
            }
            Expr::StringInterp(parts) => visitor.visit_string_interp(parts.as_slice()),
            Expr::TryCatch(try_expr, catch_expr) => {
                visitor.visit_try_catch(try_expr, catch_expr.as_ref())
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

pub type AstNode = AstLoc;

#[allow(unused_variables)]
pub trait ExprVisitor<'e, R> {
    fn default(&self) -> R;

    fn visit_alternative(&self, lhs: &'e AstNode, defaults: &'e AstNode) -> R {
        lhs.accept(self);
        defaults.accept(self);
        self.default()
    }
    fn visit_array(&self, elements: &'e [AstNode]) -> R {
        for e in elements {
            e.accept(self);
        }
        self.default()
    }

    fn visit_bind_vars(&self, vals: &'e Ast, vars: &'e Ast, rhs: &'e Ast) -> R {
        vals.accept(self);
        vars.accept(self);
        self.default()
    }

    fn visit_binop(&self, op: BinOps, lhs: &'e Ast, rhs: &'e Ast) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_breakpoint(&self, expr: &'e Ast) -> R {
        expr.accept(self);
        self.default()
    }
    fn visit_call(&self, name: &str, args: &'e [AstNode]) -> R {
        for a in args {
            a.accept(self);
        }
        self.default()
    }
    fn visit_comma(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_define_function(
        &self,
        name: &'e str,
        args: &'e [String],
        body: &'e AstNode,
        rhs: &'e AstNode,
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
    fn visit_if_else(&self, cond: &'e [AstNode], branches: &'e [AstNode]) -> R {
        for x in cond.iter().chain(branches.iter()) {
            x.accept(self);
        }
        self.default()
    }
    fn visit_index(&self, expr: &'e AstNode, idx: Option<&'e AstNode>) -> R {
        expr.accept(self);
        idx.map(|idx| idx.accept(self));
        self.default()
    }
    fn visit_literal(&self, lit: &'e Value) -> R {
        self.default()
    }
    fn visit_object(&self, entries: &'e [ObjectEntry]) -> R {
        for e in entries {
            e.key.accept(self);
            e.value.accept(self);
        }
        self.default()
    }
    fn visit_pipe(&self, lhs: &'e AstNode, rhs: &'e AstNode) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_reduce(
        &self,
        input: &'e AstNode,
        var: &'e str,
        init: &'e AstNode,
        update: &'e AstNode,
    ) -> R {
        input.accept(self);
        init.accept(self);
        update.accept(self);
        self.default()
    }
    fn visit_scope(&self, inner: &'e AstNode) -> R {
        inner.accept(self);
        self.default()
    }
    fn visit_slice(
        &self,
        expr: &'e AstNode,
        start: Option<&'e AstNode>,
        end: Option<&'e AstNode>,
    ) -> R {
        expr.accept(self);
        start.map(|s| s.accept(self));
        end.map(|s| s.accept(self));
        self.default()
    }
    fn visit_string_interp(&self, parts: &'e [AstNode]) -> R {
        for p in parts {
            p.accept(self);
        }
        self.default()
    }
    fn visit_try_catch(&self, try_expr: &'e AstNode, catch_expr: Option<&'e AstNode>) -> R {
        try_expr.accept(self);
        if let Some(catch_expr) = catch_expr {
            catch_expr.accept(self);
        }
        self.default()
    }
    fn visit_update_assign(&self, path: &'e AstNode, assign: &'e AstNode) -> R {
        path.accept(self);
        assign.accept(self);
        self.default()
    }
    fn visit_variable(&self, name: &'e str) -> R {
        self.default()
    }
}
