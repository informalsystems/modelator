use super::{Artifact, ArtifactCreator};
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

    /// Returns a base filename <>.cfg
    pub fn filename(&self) -> String {
        // TODO:  this with value derived from internal repr
        let res = self.path.as_path().file_name();
        if res.is_none() {
            panic!("TODO: tla config file should not fail to provide filename")
        }
        return res.unwrap().to_str().unwrap().to_owned();
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

impl ArtifactCreator for TlaConfigFile {
    /// Create a new instance from a file content string.
    fn from_string(s: &str) -> Result<Self, Error> {
        Ok(TlaConfigFile {
            path: PathBuf::new(),
            content: s.to_string(),
        })
    }
}

impl Artifact for TlaConfigFile {
    /// Returns a string representation.
    fn as_string(&self) -> &str {
        // TODO: will use explicit data to generate a repr
        &self.content
    }
}
