pub(crate) mod cmds;
pub(crate) mod json_trace;
pub(crate) mod tla_config_file;
pub(crate) mod tla_file;
pub(crate) mod tla_trace;

use crate::Error;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::str;

pub fn try_write_to_dir<'a, P: AsRef<Path>, C>(dir: P, collection: C) -> Result<(), Error>
where
    C: IntoIterator<Item = Box<&'a dyn Artifact>>,
{
    //NEXT: write files yadayada
    todo!()
}

pub trait ArtifactCreator
where
    Self: Sized,
{
    /// Create a new instance from a file content string.
    fn from_string(s: &str) -> Result<Self, Error>;

    /// Tries to read a file and initialize from the content.
    fn try_read_from_file<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let file_content = crate::util::try_read_file_contents(path)?;
        Ok(Self::from_string(&file_content)?)
    }
}

/// A wrapper around a file
/// NOTE: for now this is bare-bones but it will eventually include additional meta-data
/// which will justify the additional interface.
pub trait Artifact {
    /// Returns a string representation.
    fn as_string(&self) -> &str;

    /// Tries to write the contents to path using the result of as_string.
    fn try_write_to_file(&self, path: &Path) -> Result<(), Error> {
        Ok(std::fs::write(path, format!("{}", self.as_string()))?)
    }
}

// Re-exports.
pub use cmds::ModelCheckingTestArgs;
pub use json_trace::JsonTrace;
pub use tla_config_file::TlaConfigFile;
pub use tla_file::TlaFile;
pub use tla_trace::TlaTrace;
