use std::sync::OnceLock;

use anyhow::{bail, Context, Result};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest::pratt_parser::PrattParser;

use crate::interpreter::ast_eval::{ExprEval, VarScope};
use crate::parser::expr_ast::{Ast, FuncDef, SrcId};
use crate::parser::pratt_expr::{parse_func_def, pratt_parser};
use crate::src_reader::SrcRead;
use crate::value::ValueOps;

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
    let main_prog_src_id = SrcId::new();

    let includes = include_and_import(&mut program_pairs, src_reader, main_prog_src_id)?;
    let main_prog_tokens = program_pairs.next().unwrap().into_inner();

    // Prepend included functions to the ast
    let mut main = pratt_parser(main_prog_tokens, main_prog_src_id)?;
    main = main.prepend_funcs(includes);

    Ok(main)
}

fn include_and_import(
    pairs: &mut Pairs<Rule>,
    src_reader: &mut dyn SrcRead,
    curr_src_id: SrcId,
) -> Result<Vec<FuncDef>> {
    let mut includes = vec![];
    while matches!(
        pairs.peek().map(|p| p.as_rule()),
        Some(Rule::include_directive)
    ) {
        // TODO: module directive
        let mut include = pairs.next().unwrap().into_inner();
        let path = include.next().unwrap().as_str();
        let mut meta = None;
        if let Some(meta_pair) = include.next() {
            let ast = pratt_parser(meta_pair.into_inner(), curr_src_id)?;
            let mut vals = ExprEval::const_eval(&ast, Default::default(), VarScope::new())
                .context("Include metadata must be a constant expr")??;
            meta = (vals.len() > 0).then(|| vals.swap_remove(0));
        }
        let _search = meta.map(|val| val.index(&"search".into()).ok()).flatten();
        // TODO; attach metadata to module to be queried by "modulemeta"
        let (src, src_id) = src_reader.read_jq(&path)?;
        let mut x = parse_module(&src, src_id, src_reader)?;
        includes.append(&mut x.functions);
    }
    Ok(includes)
}

pub struct JqModule {
    pub(crate) functions: Vec<FuncDef>,
}

pub fn parse_module(code: &str, src_id: SrcId, src_reader: &mut dyn SrcRead) -> Result<JqModule> {
    let mut pairs = JqGrammar::parse(Rule::jq_module, code)?;
    let mut functions = include_and_import(&mut pairs, src_reader, src_id)?;
    for p in pairs {
        match p.as_rule() {
            Rule::func_def => functions.push(parse_func_def(p, src_id)?),
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
