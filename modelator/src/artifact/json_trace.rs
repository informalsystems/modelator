use serde_json::Value as JsonValue;
pub struct JsonTrace {
    pub states: Vec<JsonValue>,
}

impl IntoIterator for JsonTrace {
    type Item = JsonValue;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}
