use crate::Artifact;
use std::path::Path;

pub(crate) struct Trace {}

impl Artifact for Trace {
    fn name(&self) -> &'static str {
        "State trace from model checking"
    }

    fn from_string(_s: &str) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn from_file(_f: &Path) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn to_file(&self, _f: &Path) -> Result<(), crate::Error> {
        todo!()
    }
}
