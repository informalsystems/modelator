use crate::Artifact;
use std::{fmt::Display, path::Path};

use super::ArtifactFormat;

pub(crate) type TLAState = String;

#[derive(Debug)]
pub(crate) struct Model {}

impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl Artifact for Model {
    fn name(&self) -> &'static str {
        "TLA+ model"
    }

    fn typ(&self) -> &'static str {
        "model"
    }

    fn from_string(s: &str) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn from_file(f: &Path) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn formats(&self) -> Vec<ArtifactFormat> {
        vec![ArtifactFormat::TLA, ArtifactFormat::JSON]
    }

    fn to_file(&self, f: &Path, format: super::ArtifactFormat) -> Result<(), crate::Error> {
        todo!()
    }
}
