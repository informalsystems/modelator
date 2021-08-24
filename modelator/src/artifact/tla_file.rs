use super::Artifact;
use crate::Error;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};

/// `modelator`'s artifact representing a TLA+ file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaFile {
    path: PathBuf,
}

impl TlaFile {
    pub(crate) fn new<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let path = path.as_ref().to_path_buf();
        crate::util::check_file_existence(&path)?;
        Ok(Self { path })
    }

    /// Returns the path to the TLA+ file.
    pub fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Infer TLA module name. We assume that the TLA module name matches the
    /// name of the file.
    pub(crate) fn tla_module_name(&self) -> Option<String> {
        if self.path.is_file() {
            self.path.file_name().map(|file_name| {
                file_name
                    .to_string_lossy()
                    .trim_end_matches(".tla")
                    .to_owned()
            })
        } else {
            None
        }
    }
}

// TODO: replace the following `TryFrom` implementations with one with generic
//       bound `AsRef<Path>` once https://github.com/rust-lang/rust/issues/50133
//       is fixed
impl TryFrom<&str> for TlaFile {
    type Error = crate::Error;
    fn try_from(path: &str) -> Result<Self, Self::Error> {
        Self::new(path)
    }
}

impl TryFrom<String> for TlaFile {
    type Error = crate::Error;
    fn try_from(path: String) -> Result<Self, Self::Error> {
        Self::new(path)
    }
}

impl TryFrom<&Path> for TlaFile {
    type Error = crate::Error;
    fn try_from(path: &Path) -> Result<Self, Self::Error> {
        Self::new(path)
    }
}

impl TryFrom<PathBuf> for TlaFile {
    type Error = crate::Error;
    fn try_from(path: PathBuf) -> Result<Self, Self::Error> {
        Self::new(path)
    }
}

impl std::fmt::Display for TlaFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::util::absolute_path(&self.path))
    }
}

impl Artifact for TlaFile {
    fn as_string(&self) -> &str {
        todo!()
    }
    fn try_write_to_file(&self, path: &Path) -> Result<(), Error> {
        todo!()
    }
}
