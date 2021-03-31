use crate::Error;
use std::str::FromStr;

pub(crate) type TlaState = String;

/// `modelator`'s artifact containing a test trace encoded as TLA+.
#[derive(Debug, Clone, PartialEq, Eq)]
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

impl FromStr for TlaTrace {
    type Err = Error;

    fn from_str(tla_trace: &str) -> Result<Self, Self::Err> {
        let lines = tla_trace.lines();
        let mut state_index = 0;
        let mut state = None;
        let mut trace = TlaTrace::new();

        for line in lines {
            // check if found the start of the next state
            let next_state = format!("State{} ==", state_index);
            if line.starts_with(&next_state) {
                if state_index > 0 {
                    // the previous state has ended, so we save it
                    let state = state
                        .take()
                        .expect("[modelator] a TLA trace state should have been started");
                    trace.add(state);
                }

                // start a new state with the remaining of this line
                let mut tla_state = TlaState::new();
                // trim the prefix
                let line = line.trim_start_matches(&next_state);
                // save remaining of the line
                tla_state.push_str(line);
                tla_state.push('\n');
                state = Some(tla_state);

                state_index += 1;
                continue;
            }

            // save any line if we have a state started
            if let Some(state) = state.as_mut() {
                state.push_str(line);
                state.push('\n');
            }
        }

        // save the last state
        let state = state
            .take()
            .expect("[modelator] a TLA trace should have at least one TLA state");
        trace.add(state);
        Ok(trace)
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
            write!(f, "State{} ==\n{}", index, state)?;
        }
        Ok(())
    }
}
