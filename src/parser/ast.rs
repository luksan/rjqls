pub use serde_json::Value;

#[derive(Debug, Copy, Clone)]
pub enum BinOps {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    NotEq,
}

pub type Ast = Box<Expr>;

#[derive(Debug)]
pub enum Expr {
    Array(Vec<Expr>),
    BinOp(BinOps, Ast, Ast),
    Call(Ast, Option<Ast>),
    Comma(Ast, Ast),
    Dot,
    Ident(String),
    Index(Ast, Option<Ast>), // [2]
    Literal(Value),
    Object(Vec<Expr>),
    ObjectEntry { key: Ast, value: Ast },
    ObjMember(String), // select object member
    Pipe(Ast, Ast),
}

impl Expr {
    pub fn accept<R>(&self, visitor: &(impl ExprVisitor<R> + ?Sized)) -> R {
        match self {
            Expr::Array(r) => visitor.visit_array(r),
            Expr::BinOp(op, lhs, rhs) => visitor.visit_binop(*op, lhs, rhs),
            Expr::Call(name, args) => visitor.visit_call(name, args.as_ref().map(|ast| &**ast)),
            Expr::Comma(lhs, rhs) => visitor.visit_comma(lhs, rhs),
            Expr::Dot => visitor.visit_dot(),
            Expr::Ident(i) => visitor.visit_ident(i),
            Expr::Index(expr, idx) => visitor.visit_index(expr, idx.as_ref().map(|ast| &**ast)),
            Expr::Literal(lit) => visitor.visit_literal(lit),
            Expr::Object(members) => visitor.visit_object(members),
            Expr::ObjectEntry { key, value } => visitor.visit_obj_entry(key, value),
            Expr::ObjMember(k) => visitor.visit_obj_member(k),
            Expr::Pipe(lhs, rhs) => visitor.visit_pipe(lhs, rhs),
        }
    }
}

#[allow(unused_variables)]
pub trait ExprVisitor<R> {
    fn default(&self) -> R;

    fn visit_array(&self, elements: &[Expr]) -> R {
        for e in elements {
            e.accept(self);
        }
        self.default()
    }

    fn visit_binop(&self, op: BinOps, lhs: &Ast, rhs: &Ast) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_call(&self, name: &Expr, args: Option<&Expr>) -> R {
        name.accept(self);
        args.map(|a| a.accept(self));
        self.default()
    }
    fn visit_comma(&self, lhs: &Expr, rhs: &Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
    fn visit_dot(&self) -> R {
        self.default()
    }
    fn visit_ident(&self, ident: &str) -> R {
        self.default()
    }
    fn visit_index(&self, expr: &Expr, idx: Option<&Expr>) -> R {
        expr.accept(self);
        idx.map(|idx| idx.accept(self));
        self.default()
    }
    fn visit_literal(&self, lit: &Value) -> R {
        self.default()
    }
    fn visit_object(&self, members: &[Expr]) -> R {
        for e in members {
            e.accept(self);
        }
        self.default()
    }
    fn visit_obj_entry(&self, key: &Expr, value: &Expr) -> R {
        key.accept(self);
        value.accept(self);
        self.default()
    }
    fn visit_obj_member(&self, key: &str) -> R {
        self.default()
    }
    fn visit_pipe(&self, lhs: &Expr, rhs: &Expr) -> R {
        lhs.accept(self);
        rhs.accept(self);
        self.default()
    }
}
