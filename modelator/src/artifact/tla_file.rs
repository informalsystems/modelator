use std::{fmt::Display, path::Path};

#[derive(Debug)]
pub(crate) struct TLAFile {}

impl Display for TLAFile {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl crate::artifact::Artifact for TLAFile {
    fn name(&self) -> &'static str {
        "TLA+ file"
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
