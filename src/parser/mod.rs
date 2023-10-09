use std::sync::OnceLock;

use anyhow::Context;
use anyhow::Result;
use pest::iterators::Pair;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use smallvec::SmallVec;

use crate::parser::expr_ast::Ast;
use crate::parser::pratt_expr::pratt_parser;

pub mod expr_ast;
pub mod pratt_expr;

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

trait PairExt {
    fn inner_string(self, level: usize) -> String;
}
impl PairExt for Pair<'_, Rule> {
    fn inner_string(self, level: usize) -> String {
        let mut p = self;
        for _ in 0..level {
            p = p.into_inner().next().unwrap();
        }
        p.as_str().to_owned()
    }
}

#[derive(Debug)]
pub enum Stmt {
    DefineFunc {
        name: String,
        args: SmallVec<[(String, FuncArgType); 5]>,
        filter: Ast,
    },
    RootFilter(Ast),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FuncArgType {
    Callback,
    ValueBinding,
}

pub fn parse_program(prog: &str) -> Result<Vec<Stmt>> {
    let mut program_pairs = JqGrammar::parse(Rule::program, prog)?;
    let prog = program_pairs.next().unwrap().into_inner();

    let mut stmts = Vec::new();
    for p in prog {
        let s = match p.as_rule() {
            Rule::func_def => {
                let mut pairs = p.into_inner();
                let name = pairs.next().unwrap().as_str().to_owned();
                let mut args = SmallVec::new();
                loop {
                    let pair = pairs.next().unwrap();
                    match pair.as_rule() {
                        Rule::ident => {
                            let argument = pair.inner_string(0);
                            args.push((argument, FuncArgType::Callback))
                        }
                        Rule::variable => {
                            let argument = pair.inner_string(1);
                            args.push((argument, FuncArgType::ValueBinding))
                        }
                        Rule::pratt_expr => {
                            let filter = pratt_parser(pair.into_inner());
                            break Stmt::DefineFunc { name, args, filter };
                        }
                        _ => unreachable!(),
                    }
                }
            }
            Rule::pratt_expr => {
                let expr = pratt_parser(p.into_inner());
                Stmt::RootFilter(expr)
            }
            Rule::EOI => break,
            _ => unreachable!("Unexpected rule {:?} when parsing program", p.as_rule()),
        };
        stmts.push(s);
    }
    Ok(stmts)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_program() {
        let prog = "def x(a; b; $c): 1; .";
        let stmts = parse_program(prog).unwrap();
        for _x in stmts {
            // println!("{_x:?}")
        }
    }

    #[test]
    fn parse_func_def() -> Result<()> {
        let funcs = ["def x: 3;", "def x(a): . ;"];
        for func in funcs.iter() {
            let _res = JqGrammar::parse(Rule::func_def, func)?;
        }
        Ok(())
    }

    #[test]
    fn parse_tests() {
        let code = std::fs::read_to_string("tests/log-line-parser.jq").unwrap();
        let res = JqGrammar::parse(Rule::program, &code);
        let Ok(_pairs) = res else {
            let err = res.unwrap_err();
            panic!("{err}");
        };
    }
}
