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
