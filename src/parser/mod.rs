use std::sync::OnceLock;

use anyhow::Context;
use anyhow::Result;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;

use crate::parser::ast::{Ast, BinOps, Expr, Value};

pub mod ast;

#[derive(pest_derive::Parser, Debug)]
#[grammar = "parser/jq.pest"]
pub struct JqGrammar;

static PRATT_PARSER: OnceLock<PrattParser<Rule>> = OnceLock::new();

pub fn parse_filter(filter: &str) -> Result<Ast> {
    let mut pairs = JqGrammar::parse(Rule::pratt_prog, filter).context("Parse error")?;
    let mut pairs = pairs.next().unwrap().into_inner();
    let pairs = pairs.next().unwrap().into_inner();
    Ok(pratt_parser(pairs))
}

fn get_pratt_parser() -> &'static PrattParser<Rule> {
    PRATT_PARSER.get_or_init(build_pratt_parser)
}

fn build_pratt_parser() -> PrattParser<Rule> {
    PrattParser::new()
        .op(Op::infix(Rule::colon, Assoc::Left))
        .op(
            Op::infix(Rule::pipe, Assoc::Left) | // pipe and comma have the same precedence
            Op::infix(Rule::comma, Assoc::Left),
        )
        .op(Op::infix(Rule::as_, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left) | // fmt
            Op::infix(Rule::neq, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) // fmt
            | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::div, Assoc::Left))
        .op(Op::postfix(Rule::arr_idx)
            | Op::postfix(Rule::iterate)
            | Op::postfix(Rule::string_idx)
            | Op::postfix(Rule::ident_idx))
}

fn parse_literal(pairs: Pair<Rule>) -> Value {
    let literal = pairs.into_inner().next().unwrap();
    match literal.as_rule() {
        Rule::number => Value::Number(str::parse(literal.as_str()).unwrap()),
        Rule::string => Value::String(literal.into_inner().as_str().to_owned()),
        Rule::bool => Value::Bool(literal.as_str() == "true"),
        Rule::null => Value::Null,
        _ => unreachable!(),
    }
}

fn pratt_parse_object(pairs: Pairs<Rule>) -> Ast {
    let pratt = get_pratt_parser();
    pratt
        .map_primary(|p| match p.as_rule() {
            Rule::obj_pair => {
                let mut inner = p.into_inner();
                let key = inner.next().unwrap();
                let _colon = inner.next();
                let value = inner.next().unwrap();
                Ast::new(Expr::ObjectEntry {
                    key: pratt_parser(key.into_inner()),
                    value: pratt_parser(value.into_inner()),
                })
            }
            p => panic!("{p:?}"),
        })
        .map_infix(|lhs, op, rhs| {
            let expr = match op.as_rule() {
                Rule::comma => Expr::Comma(lhs, rhs),
                p => panic!("Incorrect obj infix operator {p:?}"),
            };
            Ast::new(expr)
        })
        .parse(pairs)
}

fn vec_from_commas(mut ast: Ast) -> Vec<Expr> {
    let mut ret = Vec::new();
    while let Expr::Comma(l, r) = *ast {
        ret.push(*r);
        ast = l;
    }
    ret.push(*ast);
    ret.reverse();
    ret
}

pub fn pratt_parser(pairs: Pairs<Rule>) -> Ast {
    let pratt = get_pratt_parser();

    pratt
        .map_primary(|p| {
            Ast::new(match p.as_rule() {
                Rule::arr => Expr::Array(vec_from_commas(pratt_parser(p.into_inner()))),
                Rule::call => {
                    let mut x = p.into_inner();
                    let ident = Expr::Ident(x.next().unwrap().as_str().to_string());
                    let params = pratt_parser(x.next().unwrap().into_inner());

                    Expr::Call(Ast::new(ident), Some(params))
                }
                Rule::dot_primary => Expr::Dot,
                Rule::ident => Expr::Ident(p.as_str().to_string()),
                Rule::ident_primary => {
                    let mut x = p.into_inner();
                    let ident = Expr::Ident(x.next().unwrap().as_str().to_string());
                    Expr::Call(Ast::new(ident), None)
                }
                Rule::literal => Expr::Literal(parse_literal(p)),
                Rule::obj => Expr::Object(vec_from_commas(pratt_parse_object(p.into_inner()))),
                Rule::pratt_expr => return pratt_parser(p.into_inner()),
                Rule::string => Expr::Literal(Value::String(p.as_str().to_string())),
                Rule::var_primary => {
                    Expr::Variable(
                        p.into_inner() // variable
                            .next()
                            .unwrap()
                            .into_inner() // ident
                            .next()
                            .unwrap()
                            .as_str()
                            .to_owned(),
                    )
                }
                r => panic!("primary {r:?}"),
            })
        })
        .map_infix(|lhs, op, rhs| {
            let expr = match op.as_rule() {
                Rule::add => Expr::BinOp(BinOps::Add, lhs, rhs),
                Rule::sub => Expr::BinOp(BinOps::Sub, lhs, rhs),
                Rule::mul => Expr::BinOp(BinOps::Mul, lhs, rhs),
                Rule::div => Expr::BinOp(BinOps::Div, lhs, rhs),

                Rule::as_ => Expr::BindVars(lhs, rhs),
                Rule::comma => Expr::Comma(lhs, rhs),
                Rule::eq => Expr::BinOp(BinOps::Eq, lhs, rhs),
                Rule::neq => Expr::BinOp(BinOps::NotEq, lhs, rhs),
                Rule::pipe => Expr::Pipe(lhs, rhs),
                r => {
                    panic!("Missing pratt infix rule {r:?}")
                }
            };
            Ast::new(expr)
        })
        .map_prefix(|_op, _expr| {
            panic!("No prefix rules yet.");
            /*
            Ast::new(match op.as_rule() {
                r => panic!("Missing pratt prefix rule {r:?}"),
            })
             */
        })
        .map_postfix(|expr, op| {
            Ast::new(match op.as_rule() {
                Rule::arr_idx => Expr::Index(expr, Some(pratt_parser(op.into_inner()))),
                Rule::iterate => Expr::Index(expr, None),
                Rule::ident_idx => Expr::Index(expr, Some(pratt_parser(op.into_inner()))),
                Rule::string_idx => Expr::Index(
                    expr,
                    Some(Ast::new(Expr::Literal(Value::String(
                        op.into_inner()
                            .next()
                            .unwrap()
                            .into_inner()
                            .as_str()
                            .to_owned(),
                    )))),
                ),
                r => panic!("Missing pratt postfix rule {r:?}"),
            })
        })
        .parse(pairs)
}

#[cfg(test)]
#[allow(dead_code)]
mod test_parser {
    use std::iter;
    use std::panic::{catch_unwind, resume_unwind};

    use pest::Parser;

    use super::*;

    // #[test]
    fn debugger() {
        let filter = ".a.b";
        let pairs = parse_pratt(filter).unwrap();
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
            [dot_obj_idx, ".a", "Index(Dot, Some(Ident(\"a\")))"]
            [dot_infix,".a.b",r#"Pipe(Index(Dot, Some(Ident("a"))), Index(Dot, Some(Ident("b"))))"#]
            [numeric_add,"123e-3 + 3","BinOp(Add, Literal(Number(123e-3)), Literal(Number(3)))"]
            [plain_call, "length", "Call(Ident(\"length\"), None)"]
            [object_construction, r#"{a: 4, b: "5", "c": 6}"#, r#"Object([ObjectEntry { key: Ident("a"), value: Literal(Number(4)) }, ObjectEntry { key: Ident("b"), value: Literal(String("5")) }, ObjectEntry { key: Literal(String("\"c\"")), value: Literal(Number(6)) }])"#]
            [variable, "3+$a", "BinOp(Add, Literal(Number(3)), Variable(\"a\"))"]
            [var_binding, "3 as $a", "BindVars(Literal(Number(3)), Variable(\"a\"))"]
            [pattern_match, "[1,2,{a: 3}] as [$a,$b,{a:$c}]", r#"BindVars(Array([Literal(Number(1)), Literal(Number(2)), Object([ObjectEntry { key: Ident("a"), value: Literal(Number(3)) }])]), Array([Variable("a"), Variable("b"), Object([ObjectEntry { key: Ident("a"), value: Variable("c") }])]))"#]
        ];
    }

    fn assert_ast(filter: &str, ref_ast: &str) {
        let ast = parse_pratt_ast(filter).unwrap();
        let str_rep = format!("{ast:?}");
        assert_eq!(&str_rep, ref_ast);
    }

    fn parse_pratt_ast(filter: &str) -> Result<Ast> {
        let pairs = parse_pratt(filter).unwrap();
        let x = pairs.clone();
        match catch_unwind(|| pratt_parser(pairs)) {
            Ok(a) => return Ok(a),
            Err(panic_) => {
                println!("{filter}");
                println!("{x:#?}");
                resume_unwind(panic_)
            }
        };
    }

    fn parse_pratt(filter: &str) -> Result<Pairs<Rule>> {
        let res = JqGrammar::parse(Rule::pratt_prog, filter);
        let Err(err) = res else {
            let pratt_prog = res.unwrap().next().unwrap();
            let pratt_expr = pratt_prog.into_inner().next().unwrap();
            return Ok(pratt_expr.into_inner());
        };
        panic!("failed to parse {filter} -> {:?}", dbg!(err))
    }

    #[test]
    fn parse_tests() {
        let code = std::fs::read_to_string("tests/shopping_list.jq").unwrap();
        let res = JqGrammar::parse(Rule::program, &code);
        let Ok(_pairs) = res else {
            let err = res.unwrap_err();
            panic!("{err}");
        };
    }

    #[test]
    fn parse_number() {
        let pairs = JqGrammar::parse(Rule::program, "1.3e-19").unwrap();
        for _t in pairs.flatten().tokens() {
            // println!("{_t:?}");
        }
    }

    #[test]
    fn parse_array() {
        let res = JqGrammar::parse(Rule::program, "[1,2,3]");

        let Ok(pairs) = res else {
            panic!("{:?}", dbg!(res))
        };
        for _t in pairs.flatten().tokens() {
            //     println!("{_t:?}");
        }
    }
}
