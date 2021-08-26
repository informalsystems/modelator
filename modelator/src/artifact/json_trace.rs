use super::Artifact;
use crate::Error;
use serde_json::Value as JsonValue;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::str::FromStr;

/// `modelator`'s artifact containing a test trace encoded as JSON.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonTrace {
    states: JsonValue,
}

impl IntoIterator for JsonTrace {
    type Item = JsonValue;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self.states {
            JsonValue::Array(states) => states.into_iter(),
            _ => panic!(
                "[modelator] JsonTrace {:?} should be a serde_json::Value::Array",
                self
            ),
        }
    }
}

impl From<Vec<JsonValue>> for JsonTrace {
    fn from(states: Vec<JsonValue>) -> Self {
        Self {
            states: JsonValue::Array(states),
        }
    }
}

impl std::fmt::Display for JsonTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#}", self.states)
    }
}

impl TryFrom<&str> for JsonTrace {
    type Error = crate::Error;
    fn try_from(_path: &str) -> Result<Self, Self::Error> {
        // Self::new(path)
        todo!();
    }
}

impl TryFrom<String> for JsonTrace {
    type Error = crate::Error;
    fn try_from(_path: String) -> Result<Self, Self::Error> {
        // Self::new(path)
        todo!();
    }
}

impl TryFrom<&Path> for JsonTrace {
    type Error = crate::Error;
    fn try_from(_path: &Path) -> Result<Self, Self::Error> {
        // Self::new(path)
        todo!();
    }
}

impl TryFrom<PathBuf> for JsonTrace {
    type Error = crate::Error;
    fn try_from(_path: PathBuf) -> Result<Self, Self::Error> {
        // Self::new(path)
        todo!();
    }
}

impl Artifact for JsonTrace {
    fn from_string(s: &str) -> Result<Self, Error> {
        todo!()
    }
    fn as_string(&self) -> &str {
        todo!()
    }
}
