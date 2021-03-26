use serde_json::Value as JsonValue;
use crate::EventStream;

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

impl Into<EventStream> for JsonTrace {
    fn into(self) -> EventStream {
        let mut events = EventStream::new();
        let mut values = self.into_iter();
        // safe to unwrap here as we check above that JsonTrace in a non-empty array
        let init = values.next().unwrap(); 
        events.add_init(init);
        for value in values {
            match value.clone() {
                JsonValue::Object(value) => 
                    match value.get("action") {
                        Some(action) => events.add_action(action.clone()),
                        None => {}
                    }    
                _ => {}
            }
            events.add_check(value);
        }
        events
    }
}