use super::Artifact;
use crate::Error;
use std::convert::TryFrom;
use std::fs;
use std::path::{Path, PathBuf};

/// `modelator`'s artifact representing a TLA+ config file containing the TLA+
/// model `CONSTANT`s and `INIT` and `NEXT` predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaConfigFile {
    path: PathBuf,
    content: String,
}

impl TlaConfigFile {
    pub(crate) fn new<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let path = path.as_ref().to_path_buf();
        crate::util::check_file_existence(&path)?;
        let content: String = fs::read_to_string(&path)?;
        Ok(Self { path, content })
    }

    /// Returns the path to the TLA+ config file.
    pub fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Returns the content of the TLA+ config file.
    pub fn content(&self) -> &str {
        &self.content
    }
}

impl std::fmt::Display for TlaConfigFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::util::absolute_path(&self.path))
    }
}

impl Artifact for TlaConfigFile {
    fn as_string(&self) -> &str {
        todo!()
    }
    fn try_write_to_file(&self, _path: &Path) -> Result<(), Error> {
        todo!()
    }
}