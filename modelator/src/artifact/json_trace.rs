use super::Artifact;
use crate::Error;
use serde_json::Value as JsonValue;
use std::path::Path;

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
    fn from_string(s: &str) -> Result<Self, Error> {
        todo!()
    }

    fn from_file(path: &std::path::Path) -> Result<Self, Error> {
        todo!()
    }

    fn as_string(&self) -> &str {
        todo!()
    }

    fn to_file(&self, path: &std::path::Path) -> Result<(), Error> {
        todo!()
    }
}
