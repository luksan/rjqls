use std::sync::OnceLock;

use anyhow::{bail, Result};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest::pratt_parser::PrattParser;

use crate::parser::expr_ast::{Ast, SrcId};
use crate::parser::pratt_expr::{parse_func_def, pratt_parser};
use crate::src_reader::SrcRead;

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

pub fn parse_program(prog: &str, src_reader: &mut dyn SrcRead) -> Result<Ast> {
    let mut program_pairs = JqGrammar::parse(Rule::program, prog)?;

    let includes = include_and_import(&mut program_pairs, src_reader)?;
    let main_prog_tokens = program_pairs.next().unwrap().into_inner();

    // Prepend included functions to the ast
    let mut main = pratt_parser(main_prog_tokens, SrcId::new())?;
    for f in includes.into_iter().rev() {
        main = main.prepend_func(f.name, f.args, f.filter)
    }
    Ok(main)
}

fn include_and_import(
    pairs: &mut Pairs<Rule>,
    src_reader: &mut dyn SrcRead,
) -> Result<Vec<OwnedFunc>> {
    let mut includes = vec![];
    while matches!(
        pairs.peek().map(|p| p.as_rule()),
        Some(Rule::include_directive)
    ) {
        // TODO: module directive
        let mut include = pairs.next().unwrap().into_inner();
        let path = include.next().unwrap().as_str();
        let _metadata = include.next();
        let (src, src_id) = src_reader.read_jq(&path)?;
        let mut x = parse_module(&src, src_id, src_reader)?;
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

pub fn parse_module(code: &str, src_id: SrcId, src_reader: &mut dyn SrcRead) -> Result<JqModule> {
    let mut pairs = JqGrammar::parse(Rule::jq_module, code)?;
    let mut functions = include_and_import(&mut pairs, src_reader)?;
    for p in pairs {
        match p.as_rule() {
            Rule::func_def => {
                let (name, args, filter) = parse_func_def(p, src_id)?;
                functions.push(OwnedFunc { name, args, filter });
            }
            Rule::pratt_expr => {
                bail!("library should only have function definitions, not a main expression")
            }
            Rule::EOI => break,
            _ => unreachable!("Missing rule '{p:?}' in module parser"),
        }
    }
    Ok(JqModule { functions })
}

#[cfg(test)]
mod test {
    use crate::src_reader::test_src_reader;

    use super::*;

    #[test]
    fn test_include() {
        parse_program(
            r#"include "tests/test_include.jq"; ."#,
            &mut test_src_reader(),
        )
        .unwrap();
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
        parse_module(&code, SrcId::new(), &mut test_src_reader()).unwrap();
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
