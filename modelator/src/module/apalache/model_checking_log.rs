use super::{Artifact, ArtifactCreator};
use crate::Error;
use std::convert::TryFrom;
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;

/// `modelator`'s artifact containing a test trace encoded as TLA+.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelCheckingLog {
    backing_str: String,
}

impl ModelCheckingLog {
    fn new(backing_str: &str) -> ModelCheckingLog {
        return ModelCheckingLog {
            backing_str: backing_str.to_string(),
        };
    }
}

impl std::fmt::Display for ModelCheckingLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = format!("..."); //TODO:
        write!(f, s)?;
        Ok(())
    }
}

impl ArtifactCreator for ModelCheckingLog {
    fn from_string(s: &str) -> Result<Self, Error> {
        Ok(ModelCheckingLog::new(s))
    }
}

impl Artifact for ModelCheckingLog {
    fn as_string(&self) -> &str {
        return &self.backing_str;
    }
}
