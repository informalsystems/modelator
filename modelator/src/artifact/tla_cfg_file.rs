use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaConfigFile {
    path: PathBuf,
}

impl TlaConfigFile {
    pub(crate) fn new<P: AsRef<Path>>(path: P) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }

    pub(crate) fn path(&self) -> &PathBuf {
        &self.path
    }
}

impl<P> From<P> for TlaConfigFile
where
    P: AsRef<Path>,
{
    fn from(path: P) -> Self {
        Self::new(path.as_ref().to_path_buf())
    }
}

impl std::fmt::Display for TlaConfigFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.path)
    }
}
