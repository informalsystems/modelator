use crate::artifact::tla_trace::{TlaState, TlaTrace};
use crate::Error;

pub(crate) fn parse(counterexample: &str) -> Result<TlaTrace, Error> {
    let lines = counterexample.lines();
    let mut state_index = 0;
    let mut state = None;
    let mut trace = TlaTrace::new();

    for line in lines {
        // ignore comments
        if line.starts_with("(*") || line.starts_with("\\*") {
            continue;
        }

        // we're done when we reach a line starting with "====="
        if line.starts_with("=====") {
            return Ok(trace);
        }

        // check if found the start of the next state
        let next_state = format!("State{} ==", state_index);
        let inv_violation = "InvariantViolation";
        if line.starts_with(&next_state) || line.starts_with(&inv_violation) {
            if state_index > 0 {
                // the previous state has ended, so we save it
                let state = state
                    .take()
                    .expect("[modelator] a trace state should have been started");
                trace.add(state);
            }

            // start a new state with the remaining of this line
            let mut tla_state = TlaState::new();
            // trim the two possible prefixes
            let line = line
                .trim_start_matches(&next_state)
                .trim_start_matches(&inv_violation);
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

    // error if we have reached the end of the file without a line starting
    // with "====="
    Err(Error::InvalidApalacheCounterexample(
        counterexample.to_owned(),
    ))
}
