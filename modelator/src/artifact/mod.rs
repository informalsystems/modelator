mod tla_file;
mod tla_trace;
mod json_trace;

use crate::error::Error;
use std::{path::Path, str};

pub trait Artifact {
    fn name(&self) -> &'static str;

    fn to_file(&self, f: &Path) -> Result<(), Error>;

    fn from_file(f: &Path) -> Result<Self, Error>
    where
        Self: Sized;

    fn from_string(s: &str) -> Result<Self, Error>
    where
        Self: Sized;
}
