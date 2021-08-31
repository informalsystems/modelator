use super::{Artifact, ArtifactCreator};
use crate::Error;
use serde_json::Value as JsonValue;
use std::convert::TryFrom;
use std::path::{Path, PathBuf};
use std::str::FromStr;

//TODO: make this match the

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

impl Artifact for JsonTrace {
    fn as_string(&self) -> String {
        serde_json::to_string_pretty(&self.states)
            .expect("should not fail as it [serde_json::Value] is serializable")
    }
}
