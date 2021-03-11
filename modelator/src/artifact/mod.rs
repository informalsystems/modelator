pub(crate) mod tla_file;
pub(crate) mod tla_trace;
pub(crate) mod json_trace;

use crate::error::Error;
use std::{path::Path, str};

// Re-exports.
pub use tla_trace::TlaTrace;
pub use json_trace::JsonTrace;

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
