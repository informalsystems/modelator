use super::{Artifact, ArtifactCreator};
use crate::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;

/// `modelator`'s artifact containing a test trace encoded as TLA+.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlcLog {
    backing_str: String,
}

impl TlcLog {
    fn new(backing_str: &str) -> TlcLog {
        return TlcLog {
            backing_str: backing_str.to_string(),
        };
    }
}

impl std::fmt::Display for TlcLog {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.backing_str)?;
        Ok(())
    }
}

impl ArtifactCreator for TlcLog {
    fn from_string(s: &str) -> Result<Self, Error> {
        Ok(TlcLog::new(s))
    }
}

impl Artifact for TlcLog {
    fn as_string(&self) -> &str {
        return &self.backing_str;
    }
}
