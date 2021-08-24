use crate::Error;
use std::{fmt, path::Path, str};

pub trait Artifact: fmt::Display {
    fn from_string(s: &str) -> Result<Self, Error>
    where
        Self: Sized;

    fn from_file(f: &Path) -> Result<Self, Error>
    where
        Self: Sized;

    fn as_string(&self) -> &str;

    fn to_file(&self, f: &Path) -> Result<(), Error>;
}

impl fmt::Debug for dyn Artifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
