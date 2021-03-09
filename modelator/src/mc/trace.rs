use serde_json::Value as JsonValue;

pub(crate) type TLAState = String;
pub(crate) struct Trace {
    pub states: Vec<TLAState>,
}

impl Trace {
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub(crate) fn add(&mut self, state: TLAState) {
        self.states.push(state);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

pub struct JsonTrace {
    pub states: Vec<JsonValue>,
}

impl JsonTrace {
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub(crate) fn add(&mut self, state: JsonValue) {
        self.states.push(state);
    }
}

impl IntoIterator for JsonTrace {
    type Item = JsonValue;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}
