use crate::Error;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::str;

/// TODO:
pub trait Artifact
where
    Self: std::fmt::Display
        + for<'a> TryFrom<&'a str, Error = crate::Error>
        + TryFrom<String, Error = crate::Error>
        + for<'a> TryFrom<&'a Path, Error = crate::Error>
        + TryFrom<PathBuf, Error = crate::Error>,
{
    /// Returns a string representation.
    fn as_string(&self) -> &str;

    /// Tries to write the contents to path.
    fn try_write_to_file(&self, path: &Path) -> Result<(), Error>;
}

// impl std::fmt::Debug for dyn Artifact {
//     fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         todo!()
//     }
// }
