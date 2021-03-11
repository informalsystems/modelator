use std::path::{Path, PathBuf};

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
