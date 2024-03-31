use std::path::Path;
use std::sync::OnceLock;

use anyhow::Context;
use anyhow::Result;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::PrattParser;
use pest::Parser;

use crate::parser::expr_ast::{Ast, SrcId};
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

    let includes = include_and_import(&mut program_pairs)?;
    let main_prog_tokens = program_pairs.next().unwrap().into_inner();

    // Prepend included functions to the ast
    let mut main = pratt_parser(main_prog_tokens, SrcId::new())?;
    for f in includes.into_iter().rev() {
        main = main.prepend_func(f.name, f.args, f.filter)
    }
    Ok(main)
}

fn include_and_import(pairs: &mut Pairs<Rule>) -> Result<Vec<OwnedFunc>> {
    let mut includes = vec![];
    while matches!(
        pairs.peek().map(|p| p.as_rule()),
        Some(Rule::include_directive)
    ) {
        // TODO: module directive
        let mut include = pairs.next().unwrap().into_inner();
        let path = include.next().unwrap().as_str();
        let _metadata = include.next();
        let src = read_module_text(path)?;
        let mut x = parse_module(&src, SrcId::new())?;
        includes.append(&mut x.functions);
    }
    Ok(includes)
}

pub struct JqModule {
    pub(crate) functions: Vec<OwnedFunc>,
}

/// This is used to own the Ast for builtins and other included functions
/// that are not present in the main AST
#[derive(Debug)]
pub struct OwnedFunc {
    pub name: String,
    pub args: Vec<String>,
    pub filter: Ast,
}

pub fn parse_module(code: &str, src_id: SrcId) -> Result<JqModule> {
    let mut pairs = JqGrammar::parse(Rule::jq_module, code)?;
    let mut functions = include_and_import(&mut pairs)?;
    for p in pairs.next().unwrap().into_inner() {
        match p.as_rule() {
            Rule::func_def => {
                let (name, args, filter) = parse_func_def(p, src_id)?;
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
        parse_module(&code, SrcId::new()).unwrap();
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
