use std::sync::OnceLock;

use anyhow::Context;
use anyhow::Result;
use pest::iterators::Pair;
use pest::pratt_parser::PrattParser;
use pest::Parser;

use crate::parser::expr_ast::Ast;
use crate::parser::pratt_expr::{parse_func_def, pratt_parser};

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

pub fn parse_program(prog: &str) -> Result<Ast> {
    let mut program_pairs = JqGrammar::parse(Rule::pratt_prog, prog)?;
    let prog = program_pairs
        .next()
        .unwrap()
        .into_inner()
        .next()
        .unwrap()
        .into_inner();
    let ast = pratt_parser(prog);
    Ok(ast)
}

pub struct JqModule {
    pub(crate) functions: Vec<OwnedFunc>,
}
#[derive(Debug)]
pub struct OwnedFunc {
    pub name: String,
    pub args: Vec<String>,
    pub filter: Ast,
}

pub fn parse_module(code: &str) -> Result<JqModule> {
    let mut pairs = JqGrammar::parse(Rule::jq_module, code)?;
    let mut functions = Vec::new();
    for p in pairs.next().unwrap().into_inner() {
        match p.as_rule() {
            Rule::func_def => {
                let (name, args, filter) = parse_func_def(p);
                functions.push(OwnedFunc { name, args, filter });
            }
            Rule::EOI => break,
            _ => unreachable!("Missing rule '{p:?}' in module parser"),
        }
    }
    Ok(JqModule { functions })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_func_def() -> Result<()> {
        let funcs = ["def x: 3;", "def x(a): . ;"];
        for func in funcs.iter() {
            let _res = JqGrammar::parse(Rule::func_def, func)?;
        }
        Ok(())
    }

    #[test]
    fn parse_builtins() {
        let code = std::fs::read_to_string("src/builtins/builtin.jq").unwrap();
        parse_module(&code).unwrap();
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
