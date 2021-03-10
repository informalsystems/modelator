use crate::Error;
use serde_json::Value as JsonValue;

pub(crate) type TLAState = String;

#[derive(Debug)]
pub(crate) struct Trace {
    states: Vec<TLAState>,
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

    pub(crate) fn parse(self) -> Result<JsonTrace, Error> {
        let states = self
            .states
            .into_iter()
            .map(|state| crate::mc::json::state_to_json(&state))
            .collect::<Result<_, _>>()?;
        Ok(JsonTrace { states })
    }
}

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
