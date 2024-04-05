use std::borrow::Cow;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};

use crate::parser::expr_ast::SrcId;
use crate::value::Value;

pub trait SrcRead {
    fn builtins(&self) -> (Cow<'static, str>, SrcId);

    fn read_jq(&mut self, relpath: &dyn AsRef<Path>) -> Result<(Cow<'static, str>, SrcId)> {
        let path = relpath.as_ref().with_extension("jq");
        self.read_src(path)
    }

    fn read_json(&mut self, _relpath: &dyn AsRef<Path>) -> Result<Value> {
        unimplemented!()
    }

    fn read_src(&mut self, relpath: PathBuf) -> Result<(Cow<'static, str>, SrcId)>;
    fn src_from_id(&self, src_id: SrcId) -> Option<Cow<'static, str>>;
}

#[cfg(test)]
pub fn test_src_reader() -> SrcReader {
    let mut r = SrcReader::new();
    r.search_path.push(".".into());
    r
}

#[derive(Debug, Clone)]
pub struct SrcReader {
    builtin_id: SrcId,
    src_id_map: Vec<(PathBuf, SrcId)>,
    search_path: Vec<PathBuf>,
}

impl SrcReader {
    pub fn new() -> Self {
        Self {
            builtin_id: SrcId::new(),
            src_id_map: vec![],
            search_path: vec![".".into()],
        }
    }
}

impl SrcRead for SrcReader {
    fn builtins(&self) -> (Cow<'static, str>, SrcId) {
        let code = include_str!("builtins/builtin.jq");
        (code.into(), self.builtin_id)
    }

    fn read_src(&mut self, relpath: PathBuf) -> Result<(Cow<'static, str>, SrcId)> {
        if relpath.is_absolute() {
            bail!("Only relative imports are allowed")
        }
        for p in self.search_path.iter() {
            let path = p.join(&relpath);
            if matches!(path.try_exists(), Ok(true)) {
                let src = std::fs::read_to_string(&path)
                    .with_context(|| format!("Failed to read file {path:?}"))?;
                let src_id = SrcId::new();
                self.src_id_map.push((path, src_id));

                return Ok((src.into(), src_id));
            }
        }
        bail!("File {relpath:?} not found in {:?}", self.search_path)
    }

    fn src_from_id(&self, src_id: SrcId) -> Option<Cow<'static, str>> {
        if src_id == self.builtin_id {
            return Some(self.builtins().0);
        }
        let path = &self.src_id_map.iter().find(|(_, id)| id == &src_id)?.0;
        Some(std::fs::read_to_string(path).ok()?.into())
    }
}
