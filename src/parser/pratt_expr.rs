use std::cell::RefCell;

use anyhow::{Context, Result};
use pest::error::ErrorVariant;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};

use crate::parser::{PairExt, PRATT_PARSER, Rule};
use crate::parser::expr_ast::{Ast, BinOps, BreakLabel, Expr, ExprArray, ObjectEntry};
use crate::value::Value;

fn get_pratt_parser() -> &'static PrattParser<Rule> {
    PRATT_PARSER.get_or_init(build_pratt_parser)
}

fn build_pratt_parser() -> PrattParser<Rule> {
    PrattParser::new()
        .op(Op::prefix(Rule::func_def))
        .op(Op::infix(Rule::pipe, Assoc::Right) | Op::infix(Rule::labeled_pipe, Assoc::Right))
        .op(Op::infix(Rule::comma, Assoc::Left))
        .op(Op::infix(Rule::alt, Assoc::Right))
        .op(Op::infix(Rule::upd_assign, Assoc::Left)
            | Op::infix(Rule::assign, Assoc::Left)
            | Op::infix(Rule::arith_assign, Assoc::Left))
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left)
            | Op::infix(Rule::neq, Assoc::Left)
            | Op::infix(Rule::ord, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) // fmt
            | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left)
            | Op::infix(Rule::div, Assoc::Left)
            | Op::infix(Rule::mod_, Assoc::Left))
        .op(Op::postfix(Rule::as_)) // https://github.com/jqlang/jq/issues/2446
        .op(Op::infix(Rule::idx_chain_pipe, Assoc::Right)) // virtual pipe in index chain
        .op(Op::postfix(Rule::index) | Op::postfix(Rule::iterate) | Op::postfix(Rule::slice))
        .op(Op::postfix(Rule::try_postfix))
        .op(Op::prefix(Rule::dbg_brk_pre) | Op::postfix(Rule::dbg_brk_post))
}

pub type ParseError = pest::error::Error<Rule>;
pub type ParseResult = Result<Ast, ParseError>;

pub fn pratt_parser<'a>(pairs: impl Iterator<Item = Pair<'a, Rule>>) -> Result<Ast> {
    let parser = JqPrattParser::new();
    parser.pratt_parser(pairs).context("pratt parsing error")
}

pub fn parse_func_def(pair: Pair<'_, Rule>) -> Result<(String, Vec<String>, Ast)> {
    let parser = JqPrattParser::new();
    parser
        .parse_func_def(pair)
        .context("function parsing error")
}

fn parse_literal(pairs: Pair<Rule>) -> Value {
    let literal = pairs.into_inner().next().unwrap();
    literal.as_str().parse().unwrap()
}

fn parse_inner_str(pair: Pair<Rule>) -> ParseResult {
    let span = pair.as_span();
    let pairs = pair.into_inner();
    let mut ret = String::with_capacity(pairs.len());

    for p in pairs {
        match p.as_rule() {
            Rule::char => ret.push(p.as_str().chars().next().unwrap()),
            Rule::escape => ret.push(match p.as_str().strip_prefix('\\').unwrap() {
                "\"" => '"',
                "\\" => '\\',
                "/" => '/',
                "b" => '\u{8}',
                "f" => '\u{c}',
                "n" => '\n',
                "r" => '\r',
                "t" => '\t',
                codept => codept
                    .strip_prefix('u')
                    .and_then(|s| u32::from_str_radix(s, 16).ok())
                    .and_then(char::from_u32) // FIXME: this should probably be decode_utf16
                    .unwrap_or(char::REPLACEMENT_CHARACTER),
            }),
            _ => unreachable!(),
        }
    }
    Ok(Ast::new(Expr::Literal(ret.into()), span))
}

fn vec_from_commas(mut ast: Ast) -> ExprArray {
    let mut ret = Vec::new();
    while let Expr::Comma(l, r) = *ast.expr {
        ret.push(r);
        ast = l;
    }
    ret.push(ast);
    ret.reverse();
    ret
}

struct JqPrattParser {
    label_stack: RefCell<Vec<BreakLabel>>,
}

impl JqPrattParser {
    fn new() -> Self {
        Self {
            label_stack: vec![].into(),
        }
    }

    fn find_label<'p>(&self, mut pair: Pair<'p, Rule>) -> Result<BreakLabel, Pair<'p, Rule>> {
        while pair.as_rule() != Rule::ident {
            pair = pair
                .into_inner()
                .next()
                .expect("Label should be Rule::ident")
        }
        self.label_stack
            .borrow()
            .iter()
            .rfind(|&lbl| lbl == pair.as_str())
            .cloned()
            .ok_or(pair)
    }

    fn new_label(&self, mut pair: Pair<'_, Rule>) {
        while pair.as_rule() != Rule::ident {
            pair = pair
                .into_inner()
                .next()
                .expect("Label should be Rule::ident")
        }
        let lbl = BreakLabel::new(pair.as_str().to_string());
        self.label_stack.borrow_mut().push(lbl);
    }

    fn latest_label(&self) -> Option<BreakLabel> {
        self.label_stack.borrow().last().cloned()
    }

    fn parse_object(&self, pair: Pair<Rule>) -> Result<Vec<ObjectEntry>, ParseError> {
        let pairs = pair.into_inner();
        if pairs.len() == 0 {
            return Ok(vec![]);
        }
        let mut ret = Vec::with_capacity(pairs.len());
        for entry in pairs {
            assert_eq!(entry.as_rule(), Rule::obj_pair);
            let mut inner = entry.into_inner();
            let key = inner.next().unwrap();
            let value = inner.next().unwrap();
            ret.push(ObjectEntry {
                key: self.pratt_parser(key.into_inner())?,
                value: self.pratt_parser(value.into_inner())?,
            })
        }
        Ok(ret)
    }

    fn parse_if_expr(&self, pair: Pair<Rule>) -> Result<Expr, ParseError> {
        let full_span = pair.as_span();
        let mut pairs = pair.into_inner();
        let cond = self.pratt_parser(pairs.next().unwrap().into_inner())?;
        let if_true = self.pratt_parser(pairs.next().unwrap().into_inner())?;
        let mut cond = vec![cond];
        let mut branch = vec![if_true];
        let mut else_ = Ast::new(Expr::Dot, full_span);
        for p in pairs {
            match p.as_rule() {
                Rule::elif => {
                    let mut x = p.into_inner();
                    let c = self.pratt_parser(x.next().unwrap().into_inner())?;
                    let b = self.pratt_parser(x.next().unwrap().into_inner())?;
                    cond.push(c);
                    branch.push(b);
                }
                Rule::else_ => {
                    else_ = self.pratt_parser(p.into_inner())?;
                    break;
                }
                _ => unreachable!(),
            }
        }
        branch.push(else_);
        Ok(Expr::IfElse(cond, branch))
    }

    pub fn parse_func_def(&self, p: Pair<Rule>) -> Result<(String, Vec<String>, Ast), ParseError> {
        let mut pairs = p.into_inner();
        let name = pairs.next().unwrap().as_str().to_owned();
        let mut args = Vec::new();
        let mut bound_args = Vec::new();
        loop {
            let pair = pairs.next().unwrap();
            let span = pair.as_span();
            match pair.as_rule() {
                Rule::ident => {
                    let argument = pair.inner_string(0);
                    args.push(argument);
                }
                Rule::variable => {
                    let argument = pair.inner_string(1);
                    bound_args.push((argument.clone(), span));
                    args.push(argument);
                }
                Rule::pratt_expr => {
                    let mut filter = self.pratt_parser(pair.into_inner())?;
                    for (argument, span) in bound_args.into_iter().rev() {
                        filter = Ast::new(
                            Expr::BindVars(
                                Ast::new(Expr::Call(argument.clone(), Default::default()), span),
                                Ast::new(Expr::Variable(argument), span),
                                filter,
                            ),
                            span,
                        );
                    }
                    break Ok((name, args, filter));
                }
                node => unreachable!("Unexpected node in parse_func_def: {node:?}"),
            }
        }
    }

    fn parse_inner_expr(&self, pair: Pair<Rule>) -> ParseResult {
        let x = pair.into_inner();
        self.pratt_parser(x)
    }

    fn next_expr(&self, pairs: &mut Pairs<Rule>) -> ParseResult {
        self.pratt_parser(pairs.next().unwrap().into_inner())
    }

    fn pratt_parser<'a>(&self, pairs: impl Iterator<Item = Pair<'a, Rule>>) -> ParseResult {
        let pratt = get_pratt_parser();

        pratt
            .map_primary(|p| {
                let span = p.as_span();
                let ast = match p.as_rule() {
                    Rule::arr => {
                        let p = p.into_inner();
                        let arr = if p.len() > 0 {
                            vec_from_commas(self.pratt_parser(p)?)
                        } else {
                            vec![]
                        };
                        Expr::Array(arr)
                    }
                    Rule::break_ => Expr::Break(self.find_label(p).map_err(|pair| {
                        ParseError::new_from_span(
                            ErrorVariant::CustomError {
                                message: format!("$*label-{} is not defined", pair.as_str()),
                            },
                            span,
                        )
                    })?),
                    Rule::call => {
                        let mut x = p.into_inner();
                        let ident = x.next().unwrap().inner_string(0);
                        let mut params = Vec::new();
                        for param in x {
                            let param = self.parse_inner_expr(param)?;
                            params.push(param);
                        }
                        Expr::Call(ident, params)
                    }
                    Rule::dot_primary | Rule::idx_chain_dot => Expr::Dot,
                    Rule::pipe_label => {
                        self.new_label(p);
                        Expr::Dot
                    }
                    Rule::foreach => {
                        let full_span = p.as_span();
                        let p = &mut p.into_inner();
                        let expr = self.next_expr(p)?;
                        let var = p.next().unwrap().inner_string(1);
                        let init = self.next_expr(p)?;
                        let update = self.next_expr(p)?;
                        let extract = p
                            .next()
                            .map(|x| self.parse_inner_expr(x))
                            .transpose()?
                            .unwrap_or_else(|| Ast::new(Expr::Dot, full_span));
                        Expr::ForEach(expr, var, init, update, extract)
                    }
                    Rule::ident => Expr::Ident(p.inner_string(0)),
                    Rule::if_cond => self.parse_if_expr(p)?,
                    Rule::literal => Expr::Literal(parse_literal(p)),
                    Rule::obj => Expr::Object(self.parse_object(p)?),
                    Rule::pratt_expr => return self.pratt_parser(p.into_inner()),
                    Rule::primary_group => Expr::Scope(self.parse_inner_expr(p)?), // FIXME: remove Scope from AST
                    Rule::reduce => {
                        let x = &mut p.into_inner();
                        let input = self.next_expr(x)?;
                        let iter_var = x.next().unwrap().inner_string(1);
                        let init = self.next_expr(x)?;
                        let update = self.next_expr(x)?;
                        Expr::Reduce(input, iter_var, init, update)
                    }
                    Rule::string => {
                        let x = p.into_inner();
                        let mut parts = Vec::with_capacity(x.len());
                        for p in x {
                            match p.as_rule() {
                                Rule::inner_str => parts.push(parse_inner_str(p)?),
                                Rule::str_interp => parts.push(self.parse_inner_expr(p)?),
                                _ => unreachable!(),
                            }
                        }
                        if parts.is_empty() {
                            Expr::Literal("".into())
                        } else if parts.len() == 1 && matches!(&*parts[0], Expr::Literal(_)) {
                            *parts.pop().unwrap().expr
                        } else {
                            Expr::StringInterp(parts)
                        }
                    }
                    Rule::try_catch => {
                        let mut x = p.into_inner();
                        let try_expr = self.parse_inner_expr(x.next().unwrap())?;
                        let catch_expr = x
                            .next()
                            .map(|catch| self.parse_inner_expr(catch))
                            .transpose()?;
                        Expr::TryCatch(try_expr, catch_expr)
                    }
                    Rule::variable => Expr::Variable(p.inner_string(1)),
                    r => panic!("primary {r:?}"),
                };
                Ok(Ast::new(ast, span))
            })
            .map_infix(|lhs, op, rhs| {
                let lhs = lhs?;
                let rhs = rhs?;
                let span = op.as_span();
                let expr = match op.as_rule() {
                    Rule::add
                    | Rule::sub
                    | Rule::mul
                    | Rule::div
                    | Rule::and
                    | Rule::or
                    | Rule::ord
                    | Rule::eq
                    | Rule::neq => {
                        let binop: BinOps = op.as_str().parse().unwrap();
                        Expr::BinOp(binop, lhs, rhs)
                    }
                    Rule::alt => Expr::Alternative(lhs, rhs),
                    Rule::comma => Expr::Comma(lhs, rhs),
                    Rule::labeled_pipe => Expr::LabeledPipe(
                        self.latest_label().unwrap(), // the label was created in the previous token
                        lhs,
                        rhs,
                    ),
                    Rule::pipe | Rule::idx_chain_pipe => Expr::Pipe(lhs, rhs),
                    Rule::assign => Expr::Assign(lhs, rhs),
                    Rule::upd_assign => Expr::UpdateAssign(lhs, rhs),
                    Rule::arith_assign => {
                        let binop: BinOps =
                            op.into_inner().next().unwrap().as_str().parse().unwrap();
                        Expr::UpdateAssign(
                            lhs,
                            Ast::new(Expr::BinOp(binop, Ast::new(Expr::Dot, span), rhs), span),
                        )
                    }
                    r => {
                        panic!("Missing pratt infix rule {r:?}")
                    }
                };
                Ok(Ast::new(expr, span))
            })
            .map_prefix(|op, rhs| {
                let span = op.as_span();
                let rhs = rhs?;
                let ast = match op.as_rule() {
                    Rule::dbg_brk_pre => Expr::Breakpoint(rhs),
                    Rule::func_def => {
                        let (name, args, body) = self.parse_func_def(op)?;
                        Expr::DefineFunc {
                            name,
                            args,
                            body,
                            rhs,
                        }
                    }
                    r => panic!("Missing pratt prefix rule {r:?}"),
                };
                Ok(Ast::new(ast, span))
            })
            .map_postfix(|expr, op| {
                let span = op.as_span();
                let expr = expr?;
                let ast = match op.as_rule() {
                    Rule::as_ => {
                        let inner = &mut op.into_inner();
                        Expr::BindVars(expr, self.next_expr(inner)?, self.next_expr(inner)?)
                    }
                    Rule::dbg_brk_post => Expr::Breakpoint(expr),
                    Rule::index => Expr::Index(expr, Some(self.parse_inner_expr(op)?)),
                    Rule::iterate => Expr::Index(expr, None),
                    Rule::slice => {
                        let mut pairs = op.into_inner();
                        let a = pairs.next().unwrap();
                        let start = if a.as_rule() != Rule::colon {
                            pairs.next(); // consume colon
                            Some(self.parse_inner_expr(a)?)
                        } else {
                            None
                        };
                        let end = pairs.next().map(|x| self.parse_inner_expr(x)).transpose()?;
                        Expr::Slice(expr, start, end)
                    }
                    Rule::try_postfix => Expr::TryCatch(expr, None),
                    r => panic!("Missing pratt postfix rule {r:?}"),
                };
                Ok(Ast::new(ast, span))
            })
            .parse(pairs)
    }
}

#[cfg(test)]
#[allow(dead_code)]
mod test_parser {
    use std::iter;
    use std::panic::{catch_unwind, resume_unwind};

    use anyhow::Result;
    use pest::Parser;

    use crate::parser::JqGrammar;

    use super::*;

    // #[test]
    fn debugger() {
        let filter = ".a.b";
        let pairs = pratt_prog_token_pairs(filter).unwrap();
        print_pairs(pairs, 0);
        let _ast = parse_pratt_ast(filter).unwrap();
        println!("'{filter}' -> {_ast:?}");

        panic!("This testcase is only for debugging the parser.");
    }

    #[test]
    fn test_pratt() {
        let filters = [
            r#""str""#,
            ".obj1.obj2",
            r#"."key with space index""#,
            ". | length",
            ".obj[]",
            "2 == 3",
            "(.ingredients[] | select(.item == \"sugar\")|.amount.quantity)",
            "{(.key): .val}",
            "[1,2,3]",
            "1+.+3",
            "1+.--4",
            r#""hejsan" | length "#,
            ".[]",
            ".a[3]",
            ".[1,2,3]",
            ".a + .b",
            "as_",
        ];
        // let filters = [".a[]"];
        let mut filters: &mut dyn Iterator<Item = _> = &mut filters.iter().copied();
        let code;
        let mut code_iter;
        if false {
            code = std::fs::read_to_string("tests/shopping_list.jq").unwrap();
            code_iter = filters.chain(iter::once(code.as_str()));
            filters = &mut code_iter;
        }
        for f in filters {
            let _ast = parse_pratt_ast(f).unwrap();
            // println!("'{f}' -> {_ast:?}");
        }
    }

    fn print_pairs(pairs: Pairs<Rule>, level: usize) {
        for p in pairs {
            println!(
                "{x:indent$}{:?}, \"{}\"",
                p.as_rule(),
                p.as_str(),
                x = "",
                indent = level * 2
            );
            print_pairs(p.into_inner(), level + 1);
        }
    }

    mod fmt {
        use super::*;

        macro_rules! check_ast_fmt {
            ($([$test_name:ident, $filter:literal$(, $ast:literal)?]$(,)?)+) => {
                $(#[test]
                fn $test_name() {
                    if false {}
                 $( else if true { assert_ast_fmt($filter, $ast) } )?
                    else { assert_ast_fmt($filter, $filter) }
                })+
            }}

        check_ast_fmt![
            [add, "123e-3 + 3"]
            [array_empty, "[]"]
            [array_1, "[1]"]
            [array_2, "[1,2]"]
            [array_from_idx, "[.a,.b,.c[0]]"]
            [obj_empty, "{}"]
            [obj_a, "{a: 1}"]

            [idx_ident, ".a"]
            [idx_in_obj, "{a: .[-1]|.}"]
            [idx_in_arr, "[.[-1]|.]"]

            [chained_index_try, ".[1]?[2]?[3]"]
            [comma_idx_try, "1,2,.a[2]?", "1,2,.a.[2]?"]
            [idx_chained_ident, ".a.b.c"]
            [idx_chained_try_ident, ".a?.b?.c?"]
            [str_int, r#""x\(1 + 2)x""#]
            [func_in_func, "f1(def f2($a): 3; 2)", "f1(def f2(a): a as $a|3; 2)"]
            [nested_recurse,"def recurse(f): def r: .,(f|r); r; 1"],
            [nested_funcs,"def o(a): 1,def i1: a; a + i1; o(10)"],
            [slice, ".[4:-6]"],

            [label_1, "label $a|."]
            [label_2, "1 + label $a|break $a"]

            [alternate_op, "false//1"]
            [binop_and, "true and false"]
            [try1, "try 1"],
            [try_catch, "try 1 catch 2"],
            [try_postfix, "1?", "try 1"],
            [try_binding, ". + .[1][2]?"]
        ];

        fn assert_ast_fmt(filter: &str, ref_flt: &str) {
            let ast = match parse_pratt_ast(filter) {
                Ok(a) => a,
                Err(e) => panic!("{e:?}"),
            };
            let ast_jq_printed = format!("{ast}");
            if ast_jq_printed != ref_flt {
                println!("{ast:#?}");
            }
            assert_eq!(
                &ast_jq_printed, ref_flt,
                "AST fmt didn't match with reference (right)"
            );
            // Check that the AST str rep round-trips
            let ast2 = parse_pratt_ast(&ast_jq_printed).unwrap();
            // compare the normal Debug fmt instead of the ASTs directly, since the break label id's will differ
            assert_eq!(
                format!("{ast2:?}"),
                format!("{ast:?}"),
                "AST fmt didn't round-trip"
            );
        }
    }

    mod ast_checks {
        use super::*;

        macro_rules! check_ast {
            ($([$test_name:ident, $filter:literal, $ast:literal]$(,)?)+) => {
                $(#[test]
                fn $test_name() {
                    assert_ast($filter, $ast);
                })+
            }}

        check_ast![
            [dot, ".", "Dot"]
            [empty_string, "\"\"", "Literal(String(\"\"))"]
            [array, "[1,2]", "Array([Literal(Number(1)), Literal(Number(2))])"]

            [brk_pre, "1+§2*4", "BinOp(Add, Literal(Number(1)), BinOp(Mul, Breakpoint(Literal(Number(2))), Literal(Number(4))))"]
            [brk_post, "1+2*4?§", "BinOp(Add, Literal(Number(1)), BinOp(Mul, Literal(Number(2)), Breakpoint(TryCatch(Literal(Number(4)), None))))"]

            [def_func_vars, "def func($a;$b;c):.;.", r#"DefineFunc { name: "func", args: ["a", "b", "c"], body: BindVars(Call("a", []), Variable("a"), BindVars(Call("b", []), Variable("b"), Dot)), rhs: Dot }"#]
            [def_scope, ". + (def f:.;f) | f", r#"Pipe(BinOp(Add, Dot, Scope(DefineFunc { name: "f", args: [], body: Dot, rhs: Call("f", []) })), Call("f", []))"# ]
            [def_scope2, ". + def f:.;f | f", r#"BinOp(Add, Dot, DefineFunc { name: "f", args: [], body: Dot, rhs: Pipe(Call("f", []), Call("f", [])) })"# ]

            [comma_pipe_idx, ".a, .b[0]?", r#"Comma(Index(Dot, Some(Ident("a"))), Pipe(Index(Dot, Some(Ident("b"))), TryCatch(Index(Dot, Some(Literal(Number(0)))), None)))"#]
            [iter, ".[]", "Index(Dot, None)"]
            [idx_item, ".a", r#"Index(Dot, Some(Ident("a")))"#],
            [idx_string, r#"."a""#, r#"Index(Dot, Some(Literal(String("a"))))"#]
            [idx_brkt_string, r#".["a"]"#, r#"Index(Dot, Some(Literal(String("a"))))"#]
            [idx_brkt_ident, ".[a]", r#"Index(Dot, Some(Call("a", [])))"#]
            [idx_int, ".[1]", "Index(Dot, Some(Literal(Number(1))))"]
            [idx_var_ident, "$a.b", r#"Index(Variable("a"), Some(Ident("b")))"#]
            [idx_var_brkt, "$a.[1]", r#"Index(Variable("a"), Some(Literal(Number(1))))"#]
            [idx_chain, ".[1][2]", "Index(Index(Dot, Some(Literal(Number(1)))), Some(Literal(Number(2))))"]
            [idx_chain_dot, r#".[1].[2]"#, "Index(Index(Dot, Some(Literal(Number(1)))), Some(Literal(Number(2))))"]
            [idx_chain_dot_str, r#"."a"."b""#, r#"Index(Index(Dot, Some(Literal(String("a")))), Some(Literal(String("b"))))"#]
            [idx_chain_str_brkt, r#"."a"[1]"#, r#"Index(Index(Dot, Some(Literal(String("a")))), Some(Literal(Number(1))))"#]
            [idx_chain_try, ".[1][2]?[3]", "Pipe(Index(Dot, Some(Literal(Number(1)))), Index(TryCatch(Index(Dot, Some(Literal(Number(2)))), None), Some(Literal(Number(3)))))"]
            [idx_dot_infix,".a.b",r#"Index(Index(Dot, Some(Ident("a"))), Some(Ident("b")))"#]

            [idx_precedence_1, ". * .[0]?", "BinOp(Mul, Dot, TryCatch(Index(Dot, Some(Literal(Number(0)))), None))"]
            [slice, ".[1:2]", "Slice(Dot, Some(Literal(Number(1))), Some(Literal(Number(2))))"]
            [slice_start, ".[1:]", "Slice(Dot, Some(Literal(Number(1))), None)"]
            [slice_end, ".[:1]", "Slice(Dot, None, Some(Literal(Number(1))))"]

            [label_1, "label $a | .", r#"LabeledPipe("a", Dot, Dot)"#]
            [label_2, "1 + label $a | break $a", r#"LabeledPipe("a", BinOp(Add, Literal(Number(1)), Dot), Break("a"))"#]

            [ua_add, ".x += 1", r#"UpdateAssign(Index(Dot, Some(Ident("x"))), BinOp(Add, Dot, Literal(Number(1))))"#]

            [numeric_add,"123e-3 + 3","BinOp(Add, Literal(Number(123e-3)), Literal(Number(3)))"]
            [plain_call, "length", "Call(\"length\", [])"]
            [object_construction, r#"{a: 4, b: "5", "c": 6}"#, r#"Object([ObjectEntry { key: Ident("a"), value: Literal(Number(4)) }, ObjectEntry { key: Ident("b"), value: Literal(String("5")) }, ObjectEntry { key: Literal(String("c")), value: Literal(Number(6)) }])"#]
            [variable, "3+$a", "BinOp(Add, Literal(Number(3)), Variable(\"a\"))"]
            [var_binding, "3 as $a | .", "BindVars(Literal(Number(3)), Variable(\"a\"), Dot)"]
            [var_bind_prio, "3 as $a| $a | def f:.; $a", r#"BindVars(Literal(Number(3)), Variable("a"), Pipe(Variable("a"), DefineFunc { name: "f", args: [], body: Dot, rhs: Variable("a") }))"#]
            [pattern_match, "[1,2,{a: 3}] as [$a,$b,{a:$c}] | .", r#"BindVars(Array([Literal(Number(1)), Literal(Number(2)), Object([ObjectEntry { key: Ident("a"), value: Literal(Number(3)) }])]), Array([Variable("a"), Variable("b"), Object([ObjectEntry { key: Ident("a"), value: Variable("c") }])]), Dot)"#]
            [var_scope, "(3 as $a | $a) | $a", r#"Pipe(Scope(BindVars(Literal(Number(3)), Variable("a"), Variable("a"))), Variable("a"))"#]
            [call_with_args, "sub(1;2;3)", r#"Call("sub", [Literal(Number(1)), Literal(Number(2)), Literal(Number(3))])"#]
            [call_func_arg, "f(def y: 3; .)", r#"Call("f", [DefineFunc { name: "y", args: [], body: Literal(Number(3)), rhs: Dot }])"#]
            [if_else, "if . then 3 elif 3<4 then 4 else 1 end", "IfElse([Dot, BinOp(Less, Literal(Number(3)), Literal(Number(4)))], [Literal(Number(3)), Literal(Number(4)), Literal(Number(1))])"]
            [reduce, "reduce .[] as $i (0; . + $i)", r#"Reduce(Index(Dot, None), "i", Literal(Number(0)), BinOp(Add, Dot, Variable("i")))"#]
            [foreach, "foreach .[] as $i (0; .+$i; .*2)", r#"ForEach(Index(Dot, None), "i", Literal(Number(0)), BinOp(Add, Dot, Variable("i")), BinOp(Mul, Dot, Literal(Number(2))))"#]
            [foreach2, "foreach .[] as $i (0; .+$i)", r#"ForEach(Index(Dot, None), "i", Literal(Number(0)), BinOp(Add, Dot, Variable("i")), Dot)"#]
            [string_int, r#" "hej \(1+2)" "#, r#"StringInterp([Literal(String("hej ")), BinOp(Add, Literal(Number(1)), Literal(Number(2)))])"#]

            [string_escape, r#""-\n\t\u00c4-""#, "Literal(String(\"-\\n\\tÄ-\"))"]

            [nested_func, "def a(s): def b: . + s; b + 1; a(0)", r#"DefineFunc { name: "a", args: ["s"], body: DefineFunc { name: "b", args: [], body: BinOp(Add, Dot, Call("s", [])), rhs: BinOp(Add, Call("b", []), Literal(Number(1))) }, rhs: Call("a", [Literal(Number(0))]) }"#]
        ];
    }

    #[test]
    fn assert_syntax_error() {
        let tests = [
            ".[a].", ".[1].1", ".[][", ".[].[", ".[]..", ".a + = 1", ".[:]",
        ];
        for flt in tests {
            let _err = JqGrammar::parse(Rule::pratt_prog, flt).unwrap_err();
            // println!("{_err:?}")
        }
    }
    fn assert_ast(filter: &str, ref_ast: &str) {
        let ast = parse_pratt_ast(filter).unwrap();
        let str_rep = format!("{ast:?}");
        if str_rep != ref_ast {
            println!("{filter}");
            println!("{ast:#?}");
        }
        assert_eq!(
            &str_rep, ref_ast,
            "Parsed AST doesn't match with reference (right)."
        );
    }

    fn parse_pratt_ast(filter: &str) -> Result<Ast> {
        let pairs = pratt_prog_token_pairs(filter)?;
        let x = pairs.clone();
        match catch_unwind(|| pratt_parser(pairs)) {
            Ok(a) => return a,
            Err(panic_) => {
                println!("{filter}");
                println!("{x:#?}");
                resume_unwind(panic_)
            }
        };
    }

    fn pratt_prog_token_pairs(filter: &str) -> Result<Pairs<Rule>> {
        let mut res = JqGrammar::parse(Rule::pratt_prog, filter)?;
        let pratt_prog = res.next().unwrap();
        let pratt_expr = pratt_prog.into_inner().next().unwrap();
        Ok(pratt_expr.into_inner())
    }

    #[test]
    fn parse_tests() {
        let code = std::fs::read_to_string("tests/shopping_list.jq").unwrap();
        let res = JqGrammar::parse(Rule::pratt_prog, &code);
        let Ok(_pairs) = res else {
            let err = res.unwrap_err();
            panic!("{err}");
        };
    }

    #[test]
    fn parse_number() {
        let pairs = JqGrammar::parse(Rule::pratt_prog, "1.3e-19").unwrap();
        for _t in pairs.flatten().tokens() {
            // println!("{_t:?}");
        }
    }

    #[test]
    fn parse_array() {
        let res = JqGrammar::parse(Rule::pratt_prog, "[1,2,3]");

        let Ok(pairs) = res else {
            panic!("{:?}", dbg!(res))
        };
        for _t in pairs.flatten().tokens() {
            //     println!("{_t:?}");
        }
    }
}
