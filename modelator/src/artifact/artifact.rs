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
    fn as_string(&self) -> &str;
    fn write_to_file(&self, f: &Path) -> Result<(), Error>;
}

// impl std::fmt::Debug for dyn Artifact {
//     fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         todo!()
//     }
// }
