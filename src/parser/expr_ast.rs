use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::Deref;
use std::str::FromStr;
use std::sync::atomic::{AtomicU16, AtomicUsize, Ordering};

use anyhow::bail;
use paste::paste;
use pest::Span;
use tracing::{instrument, trace};

use crate::parser::ast_jq_printer::ExprPrinter;
use crate::value::{ArcStr, ObjBuilder, Value};

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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SrcId(u16);
static SRC_ID_CTR: AtomicU16 = AtomicU16::new(1);

impl SrcId {
    pub fn new() -> Self {
        Self(SRC_ID_CTR.fetch_add(1, Ordering::Relaxed))
    }
}

pub struct AstLoc {
    pub expr: Box<Expr>,
    pub span: SpanLoc,
    pub src_id: SrcId,
}

impl AstLoc {
    pub fn new(expr: Expr, span: Span<'_>, src_id: SrcId) -> Self {
        Self {
            expr: Box::new(expr),
            span: span.into(),
            src_id,
        }
    }

    pub fn prepend_funcs(self, funcs: Vec<FuncDef>) -> Self {
        if funcs.is_empty() {
            return self;
        }
        let span = funcs[0].body.span;
        let src_id = funcs[0].body.src_id;
        let expr = Expr::FuncScope(funcs, self);
        Self {
            expr: Box::new(expr),
            span,
            src_id,
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BreakLabel {
    name: ArcStr,
    id: usize,
}

static LABEL_ID_CTR: AtomicUsize = AtomicUsize::new(0);

impl BreakLabel {
    pub fn new(name: String) -> Self {
        Self {
            name: name.into(),
            id: LABEL_ID_CTR.fetch_add(1, Ordering::AcqRel),
        }
    }

    pub fn as_str(&self) -> &str {
        &self.name
    }
}

impl PartialEq<str> for BreakLabel {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl Debug for BreakLabel {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            f.debug_struct("BreakLabel")
                .field("name", &self.name)
                .field("id", &self.id)
                .finish()
        } else {
            write!(f, "\"{}\"", &*self.name)
        }
    }
}

impl Display for BreakLabel {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "$*label-{}", &*self.name)
    }
}

impl From<BreakLabel> for Value {
    fn from(value: BreakLabel) -> Self {
        let mut o = ObjBuilder::new();
        o.insert("__jq".to_string(), value.id.into());
        o.into()
    }
}

#[derive(Debug, PartialEq)]
pub struct FuncDef {
    pub name: String,
    pub args: Vec<String>,
    pub body: Ast,
}

macro_rules! tup_des {
    ($val:expr, $x:path, ) => {{
        let $x = $val else { unreachable!() };
        ()
    }};
    ($val:expr, $x:path, $a:ty) => {{
        let $x(a) = $val else { unreachable!() };
        a
    }};
    ($val:expr, $x:path, $a:ty, $b:ty) => {{
        let $x(a, b) = $val else { unreachable!() };
        (a, b)
    }};
    ($val:expr, $x:path, $a:ty, $b:ty, $c:ty) => {{
        let $x(a, b, c) = $val else { unreachable!() };
        (a, b, c)
    }};
    ($val:expr, $x:path, $a:ty, $b:ty, $c:ty, $d:ty) => {{
        let $x(a, b, c, d) = $val else { unreachable!() };
        (a, b, c, d)
    }};
    ($val:expr, $x:path, $a:ty, $b:ty, $c:ty, $d:ty, $e:ty) => {{
        let $x(a, b, c, d, e) = $val else { unreachable!() };
        (a, b, c, d, e)
    }};
}

#[derive(Copy, Clone)]
pub struct NodeRef<'e, K>(&'e AstLoc, PhantomData<K>);
impl<'e, K> NodeRef<'e, K> {
    pub fn as_expr(&self) -> &'e Expr {
        &*self.0.expr
    }
    pub fn as_ast(&self) -> &'e AstLoc {
        self.0
    }
}

pub trait NodeRefArg {
    type Ret;
    fn node_arg_ref(self) -> Self::Ret;
}

macro_rules! node_ref_arg_self {
    ($($typ:ty),+) => {
        $(
        impl<'e> NodeRefArg for &'e $typ {
            type Ret = &'e $typ;
            fn node_arg_ref(self) -> Self::Ret {
                self
            }
        }
        )+
    };
}
node_ref_arg_self!(AstLoc, BreakLabel, FuncDef, Value);

impl<'e> NodeRefArg for &'e String {
    type Ret = &'e str;
    fn node_arg_ref(self) -> Self::Ret {
        self.as_ref()
    }
}

impl<'e> NodeRefArg for &'e BinOps {
    type Ret = BinOps;
    fn node_arg_ref(self) -> Self::Ret {
        *self
    }
}

impl<'e, T> NodeRefArg for &'e Option<T> {
    type Ret = Option<&'e T>;
    fn node_arg_ref(self) -> Self::Ret {
        self.as_ref()
    }
}

impl<'e, T> NodeRefArg for &'e Vec<T> {
    type Ret = &'e [T];
    fn node_arg_ref(self) -> Self::Ret {
        self.as_slice()
    }
}

macro_rules! mk_expr_enum {
    ($($(#[$doc:meta])?$mem:ident$(($($param:ident : $t:ty),+$( as $always_empty:ident)?))?,)+) => {

        #[derive(Debug, PartialEq)]
        pub enum Expr {
            $(
                $(#[$doc])?
                $mem$(($($t),+))?,
            )+
        }
        $(paste!{
            pub struct $mem;
            impl<'e> NodeRef<'e, $mem> {
                #[allow(unused_parens)]
                $(#[$doc])?
                pub fn [<ref_ $mem:snake>](&self) -> ($($(&$t),+)?) {
                    tup_des!(&*self.0.expr, Expr::$mem, $($(&$t),+)?)
                }
            }
        })+

        impl AstLoc {
            /*
            pub fn accept<'e, R>(&'e self, visitor: &(impl ExprVisitor<'e, R>+ ?Sized)) -> R {
                match &*self.expr {
                    $(Expr::$mem$(($($param),+))? =>
                        paste! {
                            visitor.[<visit_ $mem:snake>](
                                $($($param.node_arg_ref()),+)?
                            )
                        }
                    ,)+
                }
            }
            */
            pub fn walk_ast<'e, R>(&'e self, walker: &(impl AstWalker<'e, R> + ?Sized)) -> R {
                match &*self.expr {
                    $(Expr::$mem$((..$($always_empty)?))? =>
                        paste! {
                            walker.[<visit_ $mem:snake>](NodeRef(&self, PhantomData))
                        }
                    ,)+
                }
            }

            pub fn walk_ast_refs<'e, R>(&'e self, walker: &(impl AstWalkerRef<'e, R> + ?Sized)) -> R {
                match &*self.expr {
                    $(Expr::$mem$(($($param),+))? =>
                        paste! {
                            walker.[<visit_ $mem:snake>](
                                NodeRef(&self, PhantomData)
                                $(,$($param.node_arg_ref()),+)?
                            )
                        }
                    ,)+
                }
            }
        }


        pub trait AstWalkerRef<'e, R> {
            fn default(&self, node: &'e Ast) -> R;
            $(paste!{
                #[allow(unused_variables)]
                fn [<visit_ $mem:snake>](&self, node: NodeRef<'e, $mem>
                  $(,$($param: <&'e $t as NodeRefArg>::Ret),+)?
                ) -> R {
                    self.default(node.as_ast())
                }
            })+
        }

        pub trait AstWalker<'e, R> {
            fn default(&self, node: &'e Ast) -> R;
            $(paste!{
                fn [<visit_ $mem:snake>](&self, node: NodeRef<'e, $mem>) -> R {
                    self.default(node.as_ast())
                }
            })+
        }
    };
}

mk_expr_enum! {
    Alternative(main: Ast, alt: Ast),
    Array(expr_arr: ExprArray),
    Assign(lhs: Ast, rhs: Ast),
    BindVars(vals: Ast, vars: Ast, rhs: Ast),
    BinOp(binop: BinOps, lhs: Ast, rhs: Ast),
    Break(break_label: BreakLabel),
    Breakpoint(inner_ast: Ast),
    Call(name: String, args: ExprArray),
    Comma(lhs: Ast, rhs: Ast),
    Dot,
    /// input exp, var name, init, update, extract
    ForEach(expr: Ast, var: String, init: Ast, update: Ast, extract: Ast),
    FuncScope(funcs: Vec<FuncDef>, rhs: Ast),
    Ident(ident: String),
    /// if (cond 0) then (true branch 1) else (false branch 2) end
    IfElse(cond: Ast, then: Ast, else_: Ast),
    /// (expr to index, index key)
    Index(expr: Ast, idx: Ast), // .[key] or .key
    Iterate(expr: Ast), // .[]
    Literal(lit: Value),
    Object(members: Vec<ObjectEntry>),
    /// (optional break label, lhs, rhs)
    Pipe(label: Option<BreakLabel>, lhs: Ast, rhs: Ast),
    /// inputs, variable name, init, update
    Reduce(input: Ast, var: String, init: Ast, update: Ast),
    Scope(s: Ast),
    Slice(expr: Ast, start: Option<Ast>, end: Option<Ast>),
    StringInterp(parts: ExprArray),
    TryCatch(try_expr: Ast, catch_expr: Option<Ast>),
    UpdateAssign(path: Ast, assign: Ast),
    Variable(s: String),
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
            Expr::Break(name) => visitor.visit_break(name),
            Expr::Breakpoint(ast) => visitor.visit_breakpoint(ast),
            Expr::Call(name, args) => visitor.visit_call(name, args.as_slice()),
            Expr::Comma(lhs, rhs) => visitor.visit_comma(lhs, rhs),
            Expr::FuncScope(funcs, rhs) => visitor.visit_func_scope(funcs, rhs),
            Expr::Dot => visitor.visit_dot(),
            Expr::ForEach(expr, var, init, update, extract) => {
                visitor.visit_foreach(expr, var, init, update, extract)
            }
            Expr::Ident(i) => visitor.visit_ident(i),
            Expr::IfElse(cond, then, else_) => visitor.visit_if_else(cond, then, else_),
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx),
            Expr::Iterate(expr) => visitor.visit_iterate(expr),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::Pipe(label, lhs, rhs) => visitor.visit_pipe(label.as_ref(), lhs, rhs),
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
    fn visit_break(&self, name: &'e BreakLabel) -> R {
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
    fn visit_func_scope(&self, funcs: &'e [FuncDef], rhs: &'e AstNode) -> R {
        rhs.accept(self);
        self.default()
    }
    fn visit_dot(&self) -> R {
        self.default()
    }
    fn visit_ident(&self, ident: &'e str) -> R {
        self.default()
    }
    fn visit_if_else(&self, cond: &'e AstNode, then: &'e AstNode, else_: &'e AstNode) -> R {
        cond.accept(self);
        then.accept(self);
        else_.accept(self);
        self.default()
    }
    fn visit_index(&self, expr: &'e AstNode, idx: &'e AstNode) -> R {
        expr.accept(self);
        idx.accept(self);
        self.default()
    }
    fn visit_iterate(&self, expr: &'e AstNode) -> R {
        expr.accept(self);
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
    fn visit_pipe(&self, label: Option<&'e BreakLabel>, lhs: &'e AstNode, rhs: &'e AstNode) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_foreach(
        &self,
        input: &'e AstNode,
        var: &'e str,
        init: &'e AstNode,
        update: &'e AstNode,
        extract: &'e AstNode,
    ) -> R {
        input.accept(self);
        init.accept(self);
        update.accept(self);
        extract.accept(self);
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
