use std::cell::RefCell;

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
    BindVars(Ast, Ast),
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
    Scope(Ast),
    Variable(String),
}

impl Expr {
    pub fn accept<R>(&self, visitor: &(impl ExprVisitor<R> + ?Sized)) -> R {
        match self {
            Expr::Array(r) => visitor.visit_array(r),
            Expr::BindVars(vals, vars) => visitor.visit_bind_vars(vals, vars),
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
            Expr::Scope(s) => visitor.visit_scope(s),
            Expr::Variable(s) => visitor.visit_variable(s),
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

    fn visit_bind_vars(&self, vals: &Ast, vars: &Ast) -> R {
        vals.accept(self);
        vars.accept(self);
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
    fn visit_scope(&self, inner: &Expr) -> R {
        inner.accept(self);
        self.default()
    }
    fn visit_variable(&self, name: &str) -> R {
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
    pub fn print(expr: &Expr) {
        let this = Self::new();
        expr.accept(&this);
        println!("{}", this.r.borrow())
    }

    fn putc(&self, c: char) {
        self.r.borrow_mut().push(c);
    }

    fn puts(&self, s: &str) {
        self.r.borrow_mut().push_str(s);
    }
}

#[allow(clippy::unused_unit)]
impl ExprVisitor<()> for ExprPrinter {
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
        self.puts(&format!("{op:?}"));
        rhs.accept(self);
    }

    fn visit_call(&self, name: &Expr, args: Option<&Expr>) -> () {
        name.accept(self);
        if let Some(args) = args {
            self.putc('(');
            args.accept(self);
            self.putc(')');
        }
    }

    fn visit_comma(&self, lhs: &Expr, rhs: &Expr) -> () {
        lhs.accept(self);
        self.putc(',');
        rhs.accept(self);
    }

    fn visit_dot(&self) -> () {
        self.putc('.')
    }

    fn visit_ident(&self, ident: &str) -> () {
        self.puts(ident)
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
