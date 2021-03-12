use serde_json::Value as JsonValue;
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
