use crate::Error;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaFile {
    path: PathBuf,
}

impl TlaFile {
    pub(crate) fn new<P: AsRef<Path>>(path: P) -> Self {
        Self {
            path: path.as_ref().to_path_buf(),
        }
    }

    pub(crate) fn path(&self) -> &PathBuf {
        &self.path
    }

    pub(crate) fn check_existence(&self) -> Result<(), Error> {
        crate::util::check_file_existence(&self.path)
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

impl<P> From<P> for TlaFile
where
    P: AsRef<Path>,
{
    fn from(path: P) -> Self {
        Self::new(path.as_ref().to_path_buf())
    }
}

impl std::fmt::Display for TlaFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", crate::util::absolute_path(&self.path))
    }
}
