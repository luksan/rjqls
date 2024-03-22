use std::path::Path;
use std::sync::OnceLock;

use anyhow::Context;
use anyhow::Result;
use pest::iterators::Pair;
use pest::Parser;
use pest::pratt_parser::PrattParser;

use crate::parser::expr_ast::Ast;
use crate::parser::pratt_expr::{parse_func_def, pratt_parser};

mod ast_jq_printer;
pub mod expr_ast;
pub mod pratt_expr;

#[derive(pest_derive::Parser, Debug)]
#[grammar = "parser/jq.pest"]
struct JqGrammar;

static PRATT_PARSER: OnceLock<PrattParser<Rule>> = OnceLock::new();

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

pub fn read_module_text(rel_path_str: impl AsRef<Path>) -> Result<String> {
    let mut path = rel_path_str.as_ref().to_owned();
    path.set_extension("jq");
    // TODO: implement search paths

    std::fs::read_to_string(&path).with_context(|| format!("Failed to read file {path:?}"))
}

pub fn parse_program(prog: &str) -> Result<Ast> {
    let mut program_pairs = JqGrammar::parse(Rule::program, prog)?;

    let mut includes = vec![];
    while matches!(
        program_pairs.peek().map(|p| p.as_rule()),
        Some(Rule::include_directive)
    ) {
        // TODO: recursive includes and other directives mixed in
        let mut include = program_pairs.next().unwrap().into_inner();
        let path = include.next().unwrap().as_str();
        let _metadata = include.next();
        let src = read_module_text(path)?;
        includes.push(src);
    }
    let main_prog_tokens = program_pairs.next().unwrap().into_inner();

    let token_iters: Vec<_> = includes
        .iter()
        .map(|src| JqGrammar::parse(Rule::included_src, src))
        .collect::<Result<_, _>>()?;

    let ast = pratt_parser(token_iters.into_iter().flatten().chain(main_prog_tokens));
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
    fn test_include() {
        parse_program(r#"include "tests/test_include.jq"; ."#).unwrap();
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
    fn parse_builtins() {
        let code = std::fs::read_to_string("src/builtins/builtin.jq").unwrap();
        parse_module(&code).unwrap();
    }

    #[test]
    fn parse_tests() {
        let code = std::fs::read_to_string("tests/log-line-parser.jq").unwrap();
        let res = JqGrammar::parse(Rule::jq_module, &code);
        let Ok(_pairs) = res else {
            let err = res.unwrap_err();
            panic!("{err}");
        };
    }
}
