pub(crate) mod json_trace;
pub(crate) mod model_checker_stdout;
pub(crate) mod tla_config_file;
pub(crate) mod tla_file;
pub(crate) mod tla_file_suite;
pub(crate) mod tla_trace;

use crate::Error;
use std::path::{Path, PathBuf};
use std::str;

/// Try to write each artifact in any object implementing into_iter for Artifacts to the given directory
pub fn try_write_to_dir<'a, P: AsRef<Path>, C>(_dir: P, _collection: C) -> Result<(), Error>
where
    C: IntoIterator<Item = Box<&'a dyn Artifact>>,
{
    //TODO:
    todo!();
}

/// A sister trait for Artifacts for static constructor methods
/// NOTE: static methods and polymorphic methods prevent trait-object instantiation
/// so this approach allows dynamic use of Artifacts
pub trait ArtifactCreator
where
    Self: Sized,
{
    /// Create a new instance from a file content string.
    fn from_string(s: &str) -> Result<Self, Error>;

    /// Tries to read a file and initialize from the content.
    fn try_read_from_file<P: AsRef<Path>>(path: P) -> Result<Self, Error> {
        let file_content = crate::util::try_read_file_contents(path)?;
        Self::from_string(&file_content)
    }
}

/// A wrapper around a file
/// NOTE: for now this is bare-bones but it will eventually include additional meta-data
/// which will justify the additional interface.
pub trait Artifact {
    /// Returns a string representation.
    fn as_string(&self) -> String;

    /// Tries to write the contents to path using the result of as_string.
    fn try_write_to_file(&self, path: &Path) -> Result<(), Error> {
        Ok(std::fs::write(path, self.as_string())?)
    }
}

// Re-exports.
pub use json_trace::JsonTrace;
pub use model_checker_stdout::ModelCheckerStdout;
pub use tla_config_file::TlaConfigFile;
pub use tla_file::TlaFile;
pub use tla_file_suite::TlaFileSuite;
pub use tla_trace::TlaTrace;
