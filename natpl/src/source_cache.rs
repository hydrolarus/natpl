use std::{collections::HashMap, path::PathBuf};

use ariadne::{Cache, Source};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SourceId {
    File(usize),
    Virtual(usize),
}

#[derive(Default)]
pub struct SourceCache {
    file_paths: Vec<std::path::PathBuf>,
    virtuals: Vec<String>,

    sources: HashMap<SourceId, Source>,
}

pub type Span = (SourceId, std::ops::Range<usize>);

impl SourceCache {
    pub fn add_virtual(&mut self, name: impl Into<String>, source: String) -> SourceId {
        let new_id = self.virtuals.len();
        self.virtuals.push(name.into());

        let id = SourceId::Virtual(new_id);

        self.sources.insert(id, Source::from(source));
        id
    }

    pub fn add_file(&mut self, path: impl Into<PathBuf>) -> Result<SourceId, std::io::Error> {
        let path = path.into();

        let source = std::fs::read_to_string(&path)?;

        let new_id = self.file_paths.len();
        self.file_paths.push(path);

        let id = SourceId::File(new_id);

        self.sources.insert(id, Source::from(source));
        Ok(id)
    }
}

impl Cache<SourceId> for SourceCache {
    fn fetch(&mut self, id: &SourceId) -> Result<&Source, Box<dyn std::fmt::Debug + '_>> {
        match self.sources.get(id) {
            Some(source) => Ok(source),
            None => Err(Box::new(format!("No source with SourceId {:?}", id))),
        }
    }

    fn display<'a>(&self, id: &'a SourceId) -> Option<Box<dyn std::fmt::Display + 'a>> {
        match id {
            SourceId::File(id) => Some(Box::new(self.file_paths.get(*id)?.display().to_string())),
            SourceId::Virtual(id) => Some(Box::new(self.virtuals.get(*id)?.clone())),
        }
    }
}
