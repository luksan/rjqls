use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};

use crate::parser::{PairExt, PRATT_PARSER, Rule};
use crate::parser::expr_ast::{Ast, BinOps, Expr};
use crate::value::Value;

fn get_pratt_parser() -> &'static PrattParser<Rule> {
    PRATT_PARSER.get_or_init(build_pratt_parser)
}

fn build_pratt_parser() -> PrattParser<Rule> {
    PrattParser::new()
        .op(Op::infix(Rule::colon, Assoc::Left))
        .op(
            Op::infix(Rule::pipe, Assoc::Left)  // pipe and comma have the same precedence
            | Op::infix(Rule::comma, Assoc::Left)
            | Op::infix(Rule::idx_chain_pipe, Assoc::Left), // virtual pipe in index chain
        )
        .op(Op::infix(Rule::alt, Assoc::Right))
        .op(Op::infix(Rule::upd_assign, Assoc::Left)
            | Op::infix(Rule::assign, Assoc::Left)
            | Op::infix(Rule::arith_assign, Assoc::Left))
        .op(Op::prefix(Rule::func_def))
        .op(Op::infix(Rule::or, Assoc::Left))
        .op(Op::infix(Rule::and, Assoc::Left))
        .op(Op::infix(Rule::eq, Assoc::Left)
            | Op::infix(Rule::neq, Assoc::Left)
            | Op::infix(Rule::ord, Assoc::Left))
        .op(Op::infix(Rule::add, Assoc::Left) // fmt
            | Op::infix(Rule::sub, Assoc::Left))
        .op(Op::infix(Rule::as_, Assoc::Left)) // https://github.com/jqlang/jq/issues/2446
        .op(Op::infix(Rule::mul, Assoc::Left)
            | Op::infix(Rule::div, Assoc::Left)
            | Op::infix(Rule::mod_, Assoc::Left))
        .op(Op::postfix(Rule::index) | Op::postfix(Rule::iterate) | Op::postfix(Rule::slice))
        .op(Op::postfix(Rule::try_postfix))
}

fn parse_literal(pairs: Pair<Rule>) -> Value {
    let literal = pairs.into_inner().next().unwrap();
    match literal.as_rule() {
        Rule::number => Value::Number(str::parse(literal.as_str()).unwrap()),
        Rule::bool => Value::Bool(literal.as_str() == "true"),
        Rule::null => Value::Null,
        _ => unreachable!(),
    }
}

fn parse_object(pair: Pair<Rule>) -> Vec<Expr> {
    let pratt = get_pratt_parser();
    let pairs = pair.into_inner();
    if pairs.len() == 0 {
        return vec![];
    }
    let commas = pratt
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
        .parse(pairs);
    vec_from_commas(commas)
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

fn parse_if_expr(pair: Pair<Rule>) -> Expr {
    let mut pairs = pair.into_inner();
    let cond = pratt_parser(pairs.next().unwrap().into_inner());
    let if_true = pratt_parser(pairs.next().unwrap().into_inner());
    let mut cond = vec![*cond];
    let mut branch = vec![*if_true];
    let mut else_ = Expr::Dot;
    for p in pairs {
        match p.as_rule() {
            Rule::elif => {
                let mut x = p.into_inner();
                let c = pratt_parser(x.next().unwrap().into_inner());
                let b = pratt_parser(x.next().unwrap().into_inner());
                cond.push(*c);
                branch.push(*b);
            }
            Rule::else_ => {
                else_ = *pratt_parser(p.into_inner());
                break;
            }
            _ => unreachable!(),
        }
    }
    branch.push(else_);
    Expr::IfElse(cond, branch)
}

pub fn parse_func_def(p: Pair<Rule>) -> (String, Vec<String>, Ast) {
    let mut pairs = p.into_inner();
    let name = pairs.next().unwrap().as_str().to_owned();
    let mut args = Vec::new();
    let mut bound_args = Vec::new();
    loop {
        let pair = pairs.next().unwrap();
        match pair.as_rule() {
            Rule::ident => {
                let argument = pair.inner_string(0);
                args.push(argument);
            }
            Rule::variable => {
                let argument = pair.inner_string(1);
                bound_args.push(Ast::new(Expr::BindVars(
                    Ast::new(Expr::Call(argument.clone(), Default::default())),
                    Ast::new(Expr::Variable(argument.clone())),
                )));
                args.push(argument);
            }
            Rule::pratt_expr => {
                let mut filter = pratt_parser(pair.into_inner());
                for binding in bound_args {
                    filter = Ast::new(Expr::Pipe(binding, filter))
                }
                break (name, args.into(), filter);
            }
            node => unreachable!("Unexpected node in parse_func_def: {node:?}"),
        }
    }
}

pub fn pratt_parser(pairs: Pairs<Rule>) -> Ast {
    let pratt = get_pratt_parser();

    fn parse_inner_expr(pair: Pair<Rule>) -> Ast {
        let x = pair.into_inner();
        pratt_parser(x)
    }
    fn next_expr(pairs: &mut Pairs<Rule>) -> Ast {
        pratt_parser(pairs.next().unwrap().into_inner())
    }

    pratt
        .map_primary(|p| {
            Ast::new(match p.as_rule() {
                Rule::arr => {
                    let p = p.into_inner();
                    let arr = if p.len() > 0 {
                        vec_from_commas(pratt_parser(p))
                    } else {
                        vec![]
                    };
                    Expr::Array(arr)
                }
                Rule::break_ => Expr::Break(p.inner_string(2)),
                Rule::call => {
                    let mut x = p.into_inner();
                    let ident = x.next().unwrap().inner_string(0);
                    let mut params = Vec::new();
                    for param in x {
                        let param = parse_inner_expr(param);
                        params.push(*param);
                    }
                    Expr::Call(ident, params)
                }
                Rule::dot_primary | Rule::idx_chain_dot => Expr::Dot,
                Rule::ident => Expr::Ident(p.inner_string(0)),
                Rule::ident_primary => Expr::Call(p.inner_string(1), Default::default()),
                Rule::if_cond => parse_if_expr(p),
                Rule::label => Expr::Label(p.inner_string(2)),
                Rule::literal => Expr::Literal(parse_literal(p)),
                Rule::obj => Expr::Object(parse_object(p)),
                Rule::pratt_expr => return pratt_parser(p.into_inner()),
                Rule::primary_group => Expr::Scope(parse_inner_expr(p)),
                Rule::reduce => {
                    let x = &mut p.into_inner();
                    let input = next_expr(x);
                    let iter_var = x.next().unwrap().inner_string(1);
                    let init = next_expr(x);
                    let update = next_expr(x);
                    Expr::Reduce(input, iter_var, init, update)
                }
                Rule::string => {
                    let mut x = p.into_inner();
                    match x.len() {
                        0 => Expr::Literal(Value::String("".to_owned())),
                        1 => {
                            let s = x.next().unwrap();
                            Expr::Literal(Value::String(s.inner_string(0)))
                        }
                        len => {
                            let mut parts = Vec::with_capacity(len);
                            for p in x {
                                match p.as_rule() {
                                    Rule::inner_str => parts
                                        .push(Expr::Literal(Value::String(p.as_str().to_owned()))),
                                    Rule::str_interp => parts.push(*parse_inner_expr(p)),
                                    _ => unreachable!(),
                                }
                            }
                            Expr::StringInterp(parts)
                        }
                    }
                }
                Rule::try_catch => {
                    let mut x = p.into_inner();
                    let try_expr = parse_inner_expr(x.next().unwrap());
                    let catch_expr = x.next().map(|catch| parse_inner_expr(catch));
                    Expr::TryCatch(try_expr, catch_expr)
                }
                Rule::var_primary => Expr::Variable(p.inner_string(2)),
                r => panic!("primary {r:?}"),
            })
        })
        .map_infix(|lhs, op, rhs| {
            let expr = match op.as_rule() {
                Rule::add
                | Rule::sub
                | Rule::mul
                | Rule::div
                | Rule::alt
                | Rule::and
                | Rule::or
                | Rule::ord
                | Rule::eq
                | Rule::neq => {
                    let binop: BinOps = op.as_str().parse().unwrap();
                    Expr::BinOp(binop, lhs, rhs)
                }
                Rule::as_ => Expr::BindVars(lhs, rhs),
                Rule::comma => Expr::Comma(lhs, rhs),
                Rule::pipe | Rule::idx_chain_pipe => Expr::Pipe(lhs, rhs),
                Rule::upd_assign => Expr::UpdateAssign(lhs, rhs),
                Rule::arith_assign => {
                    let binop: BinOps = op.into_inner().next().unwrap().as_str().parse().unwrap();
                    Expr::UpdateAssign(lhs, Expr::BinOp(binop, Expr::Dot.into(), rhs).into())
                }
                r => {
                    panic!("Missing pratt infix rule {r:?}")
                }
            };
            Ast::new(expr)
        })
        .map_prefix(|op, rhs| {
            Ast::new(match op.as_rule() {
                Rule::func_def => {
                    let (name, args, body) = parse_func_def(op);
                    Expr::DefineFunc {
                        name,
                        args,
                        body,
                        rhs,
                    }
                }
                r => panic!("Missing pratt prefix rule {r:?}"),
            })
        })
        .map_postfix(|expr, op| {
            Ast::new(match op.as_rule() {
                Rule::index => Expr::Index(expr, Some(parse_inner_expr(op))),
                Rule::iterate => Expr::Index(expr, None),
                Rule::slice => {
                    let mut pairs = op.into_inner();
                    let a = pairs.next().unwrap();
                    let start = (a.as_rule() != Rule::colon).then(|| {
                        pairs.next(); // consume colon
                        parse_inner_expr(a)
                    });
                    let end = pairs.next().map(parse_inner_expr);
                    Expr::Slice(expr, start, end)
                }
                Rule::try_postfix => Expr::TryCatch(expr, None),
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

    use anyhow::Result;
    use pest::Parser;

    use crate::parser::JqGrammar;

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
            [obj_empty, "{}"]
            [obj_a, "{a: 1}"]

            [chained_index_try, ".[1][2]?[3]", ".[1]|.[2]?[3]"]
            [str_int, r#""x\(1 + 2)x""#]
            [func_in_func, "f1(def f2($a): 3; 2)", "f1(def f2(a): a as $a|3; 2)"]
            [nested_recurse,"def recurse(f): def r: .,(f|r); r; 1"],
            [nested_funcs,"def o(a): 1,def i1: a; a + i1; o(10)"],
            [slice, ".[4:-6]"],

            [binop_alt, "false // 1"]
            [binop_and, "true and false"]
            [try1, "try 1"],
            [try_catch, "try 1 catch 2"],
            [try_postfix, "1?", "try 1"],
            [try_binding, ". + .[1][2]?", ". + .[1]|.[2]?"]
        ];

        fn assert_ast_fmt(filter: &str, ref_ast: &str) {
            let ast = parse_pratt_ast(filter).unwrap();
            let str_rep = format!("{ast}");
            assert_eq!(
                &str_rep, ref_ast,
                "AST fmt didn't match with reference (right)"
            );
            // Check that the AST str rep round-trips
            let ast = parse_pratt_ast(&str_rep).unwrap();
            let str_rep = format!("{ast}");
            assert_eq!(&str_rep, ref_ast, "AST fmt didn't round-trip");
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

            [iter, ".[]", "Index(Dot, None)"]
            [idx_item, ".a", r#"Index(Dot, Some(Ident("a")))"#],
            [idx_string, r#"."a""#, r#"Index(Dot, Some(Literal(String("a"))))"#]
            [idx_brkt_string, r#".["a"]"#, r#"Index(Dot, Some(Literal(String("a"))))"#]
            [idx_brkt_ident, ".[a]", r#"Index(Dot, Some(Call("a", [])))"#]
            [idx_int, ".[1]", "Index(Dot, Some(Literal(Number(1))))"]
            [idx_var_ident, "$a.b", r#"Index(Variable("a"), Some(Ident("b")))"#]
            [idx_var_brkt, "$a.[1]", r#"Index(Variable("a"), Some(Literal(Number(1))))"#]
            [idx_chain, ".[1][2]", "Pipe(Index(Dot, Some(Literal(Number(1)))), Index(Dot, Some(Literal(Number(2)))))"]
            [idx_chain_dot, r#".[1].[2]"#, "Pipe(Index(Dot, Some(Literal(Number(1)))), Index(Dot, Some(Literal(Number(2)))))"]
            [idx_chain_dot_str, r#"."a"."b""#, r#"Pipe(Index(Dot, Some(Literal(String("a")))), Index(Dot, Some(Literal(String("b")))))"#]
            [idx_chain_str_brkt, r#"."a"[1]"#, r#"Pipe(Index(Dot, Some(Literal(String("a")))), Index(Dot, Some(Literal(Number(1)))))"#]
            [idx_chain_try, ".[1][2]?[3]", "Pipe(Index(Dot, Some(Literal(Number(1)))), Index(TryCatch(Index(Dot, Some(Literal(Number(2)))), None), Some(Literal(Number(3)))))"]
            [idx_dot_infix,".a.b",r#"Pipe(Index(Dot, Some(Ident("a"))), Index(Dot, Some(Ident("b"))))"#]
            [slice, ".[1:2]", "Slice(Dot, Some(Literal(Number(1))), Some(Literal(Number(2))))"]
            [slice_start, ".[1:]", "Slice(Dot, Some(Literal(Number(1))), None)"]
            [slice_end, ".[:1]", "Slice(Dot, None, Some(Literal(Number(1))))"]

            [ua_add, ".x += 1", r#"UpdateAssign(Index(Dot, Some(Ident("x"))), BinOp(Add, Dot, Literal(Number(1))))"#]

            [numeric_add,"123e-3 + 3","BinOp(Add, Literal(Number(123e-3)), Literal(Number(3)))"]
            [plain_call, "length", "Call(\"length\", [])"]
            [object_construction, r#"{a: 4, b: "5", "c": 6}"#, r#"Object([ObjectEntry { key: Ident("a"), value: Literal(Number(4)) }, ObjectEntry { key: Ident("b"), value: Literal(String("5")) }, ObjectEntry { key: Literal(String("c")), value: Literal(Number(6)) }])"#]
            [variable, "3+$a", "BinOp(Add, Literal(Number(3)), Variable(\"a\"))"]
            [var_binding, "3 as $a", "BindVars(Literal(Number(3)), Variable(\"a\"))"]
            [pattern_match, "[1,2,{a: 3}] as [$a,$b,{a:$c}]", r#"BindVars(Array([Literal(Number(1)), Literal(Number(2)), Object([ObjectEntry { key: Ident("a"), value: Literal(Number(3)) }])]), Array([Variable("a"), Variable("b"), Object([ObjectEntry { key: Ident("a"), value: Variable("c") }])]))"#]
            [var_scope, "(3 as $a | $a) | $a", r#"Pipe(Scope(Pipe(BindVars(Literal(Number(3)), Variable("a")), Variable("a"))), Variable("a"))"#]
            [call_with_args, "sub(1;2;3)", r#"Call("sub", [Literal(Number(1)), Literal(Number(2)), Literal(Number(3))])"#]
            [call_func_arg, "f(def y: 3; .)", r#"Call("f", [DefineFunc { name: "y", args: [], body: Literal(Number(3)), rhs: Dot }])"#]
            [if_else, "if . then 3 elif 3<4 then 4 else 1 end", "IfElse([Dot, BinOp(Less, Literal(Number(3)), Literal(Number(4)))], [Literal(Number(3)), Literal(Number(4)), Literal(Number(1))])"]
            [reduce, "reduce .[] as $i (0; . + $i)", r#"Reduce(Index(Dot, None), "i", Literal(Number(0)), BinOp(Add, Dot, Variable("i")))"#]
            [string_int, r#" "hej \(1+2)" "#, r#"StringInterp([Literal(String("hej ")), BinOp(Add, Literal(Number(1)), Literal(Number(2)))])"#]
        ];
    }

    #[test]
    fn assert_syntax_error() {
        let tests = [
            ".[a].", ".[1].1", ".[][", ".[].[", ".[]..", ".a + = 1", ".[:]",
        ];
        for flt in tests {
            let _err = JqGrammar::parse(Rule::pratt_prog, flt).unwrap_err();
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
