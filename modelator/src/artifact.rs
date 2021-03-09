use crate::error::Error;
use serde::{Deserialize, Serialize};
use std::{fmt, path::Path, str};

pub mod model;
pub mod trace;

pub enum ArtifactFormat {
    TLA,
    JSON,
    TLC,
}

#[derive(Debug, Deserialize, Serialize, PartialEq)]
pub struct ArtifactManifest {
    pub name: &'static str,
    #[serde(rename = "type")]
    pub typ: &'static str,
}

pub trait Artifact: fmt::Display {
    fn name(&self) -> &'static str;
    fn typ(&self) -> &'static str;
    fn formats(&self) -> Vec<ArtifactFormat>;

    fn from_string(s: &str) -> Result<Self, Error>
    where
        Self: Sized;
    fn from_file(f: &Path) -> Result<Self, Error>
    where
        Self: Sized;
    fn to_file(&self, f: &Path, format: ArtifactFormat) -> Result<(), Error>;
}

impl fmt::Debug for dyn Artifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
