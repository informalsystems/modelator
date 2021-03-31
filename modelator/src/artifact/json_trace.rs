use crate::EventStream;
use serde_json::Value as JsonValue;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsonTrace {
    states: JsonValue,
}

impl IntoIterator for JsonTrace {
    type Item = JsonValue;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self.states {
            JsonValue::Array(states) if !states.is_empty() => states.into_iter(),
            _ => panic!(
                "[modelator] JsonTrace {:?} should be a non-empty serde_json::Value::Array",
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

impl From<JsonTrace> for EventStream {
    fn from(trace: JsonTrace) -> Self {
        let mut events = EventStream::new();
        let mut values = trace.into_iter();
        // safe to unwrap here as we check above that JsonTrace in a non-empty array
        let init = values.next().unwrap();
        events.add_init(init);
        for value in values {
            if let JsonValue::Object(value) = value.clone() {
                if let Some(action) = value.get("action") {
                    events.add_action(action.clone());
                };
                if let Some(outcome) = value.get("actionOutcome") {
                    events.add_outcome(outcome.clone());
                }
            }
            events.add_expect(value);
        }
        events
    }
}
