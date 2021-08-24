use super::Artifact;
use crate::Error;
use std::convert::TryFrom;
use std::fs;
use std::path::{Path, PathBuf};

/// `modelator`'s artifact representing a TLA+ file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaFile {
    path: PathBuf,
    content: String,
    file_name: String,
}

/// TODO:
fn tla_file_name(path: &PathBuf) -> Option<String> {
    if path.is_file() {
        path.file_name().map(|file_name| {
            file_name
                .to_string_lossy()
                .trim_end_matches(".tla")
                .to_owned()
        })
    } else {
        None
    }
}

impl TlaFile {
    // pub(crate) fn new<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
    fn new<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let path = path.as_ref().to_path_buf();
        crate::util::check_file_existence(&path)?;
        let content: String = fs::read_to_string(&path)?;
        let file_name = tla_file_name(&path);

        match file_name {
            Some(val) => Ok(Self {
                path,
                content,
                file_name: val,
            }),
            None => Err(Error::IO(format!("File doesn't exist {}", path.display()))),
        }
    }

    /// Returns the path to the TLA+ file.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns the content of the TLA+ file.
    pub fn content(&self) -> &str {
        &self.content
    }

    /// Returns the name of the TLA+ file.
    pub fn file_name(&self) -> &str {
        &self.file_name
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
