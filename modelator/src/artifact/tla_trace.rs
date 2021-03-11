pub(crate) type TlaState = String;

#[derive(Debug)]
pub struct TlaTrace {
    states: Vec<TlaState>,
}

impl TlaTrace {
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub(crate) fn add(&mut self, state: TlaState) {
        self.states.push(state);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

impl IntoIterator for TlaTrace {
    type Item = TlaState;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}

impl std::fmt::Display for TlaTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, state) in self.states.iter().enumerate() {
            write!(f, "State{} ==\n{}", index + 1, state)?;
        }
        Ok(())
    }
}
