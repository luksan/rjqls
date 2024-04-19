use std::borrow::Cow;
use std::io::Read;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use cap_std::ambient_authority;
use cap_std::fs::{Dir, File};

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
    fn src_from_id(&mut self, src_id: SrcId) -> Option<Cow<'static, str>>;
}

#[cfg(test)]
pub fn test_src_reader() -> SrcReader {
    SrcReader::new()
}

#[derive(Debug)]
pub struct SrcReader {
    builtin_id: SrcId,
    src_id_map: Vec<(File, SrcId)>,
    search_path: Vec<Dir>,
}

impl SrcReader {
    pub fn new() -> Self {
        Self {
            builtin_id: SrcId::new(),
            src_id_map: vec![],
            search_path: vec![Dir::open_ambient_dir(".", ambient_authority()).unwrap()],
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
            if let Ok(mut file) = p.open(&relpath) {
                let mut src = String::new();
                file.read_to_string(&mut src)
                    .with_context(|| format!("Failed to read file {file:?}"))?;
                let src_id = SrcId::new();
                self.src_id_map.push((file, src_id));
                return Ok((src.into(), src_id));
            }
        }
        bail!("File {relpath:?} not found in {:?}", self.search_path)
    }

    fn src_from_id(&mut self, src_id: SrcId) -> Option<Cow<'static, str>> {
        if src_id == self.builtin_id {
            return Some(self.builtins().0);
        }
        let file = &mut self.src_id_map.iter_mut().find(|(_, id)| id == &src_id)?.0;
        let mut s = String::new();
        file.read_to_string(&mut s).ok()?;
        Some(s.into())
    }
}
