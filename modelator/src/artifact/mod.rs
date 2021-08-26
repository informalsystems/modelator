pub(crate) mod json_trace;
pub(crate) mod tla_cfg;
pub(crate) mod tla_file;
pub(crate) mod tla_trace;

use crate::Error;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::str;

/// A wrapper around a file
/// NOTE: for now this is bare-bones but it will eventually include additional meta-data
/// which will justify the additional interface.
pub trait Artifact
where
    Self: Sized,
{
    /// Create a new instance from a file content string.
    fn new(s: &str) -> Result<Self, Error>;

    /// Returns a string representation.
    fn as_string(&self) -> &str;

    /// Tries to write the contents to path using the result of as_string.
    fn try_write_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), Error> {
        Ok(std::fs::write(&path, format!("{}", self.as_string()))?)
    }

    /// Tries to read a file and initialize from the content.
    fn try_read_from_file<P: AsRef<Path>>(&self, path: P) -> Result<Self, Error> {
        let file_content = crate::util::try_read_file_contents(path)?;
        Ok(Self::new(&file_content)?)
    }
}

// Re-exports.
pub use json_trace::JsonTrace;
pub use tla_cfg::TlaConfigFile;
pub use tla_file::TlaFile;
pub use tla_trace::TlaTrace;
