use crate::Error;
use std::str;

/// TODO:
pub trait Artifact: std::fmt::Display {
    /// TODO:
    fn from_string(s: &str) -> Result<Self, Error>
    where
        Self: Sized;

    /// TODO:
    fn from_file(path: &std::path::Path) -> Result<Self, Error>
    where
        Self: Sized;

    /// TODO:
    fn as_string(&self) -> &str;

    /// TODO:
    fn to_file(&self, path: &std::path::Path) -> Result<(), Error>;
}

impl std::fmt::Debug for dyn Artifact {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}
