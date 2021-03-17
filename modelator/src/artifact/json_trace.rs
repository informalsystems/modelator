use serde_json::Value as JsonValue;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonTrace {
    states: Vec<JsonValue>,
}

impl IntoIterator for JsonTrace {
    type Item = JsonValue;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}

impl From<Vec<JsonValue>> for JsonTrace {
    fn from(states: Vec<JsonValue>) -> Self {
        Self { states }
    }
}

impl std::fmt::Display for JsonTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let json = serde_json::Value::Array(self.states.clone().into_iter().collect());
        write!(f, "{:#}", json)
    }
}
