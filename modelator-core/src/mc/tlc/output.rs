use crate::mc::trace::{TLAState, Trace};
use crate::Error;

pub(crate) fn parse(output: String) -> Result<Vec<Trace>, Error> {
    let mut traces = Vec::new();
    let mut lines = output.lines();

    while let Some(line) = lines.next() {
        // check if found the beginning of the next trace
        if line.starts_with("@!@!@ENDMSG 2121 @!@!@") {
            if let Some(trace) = parse_trace(&mut lines)? {
                traces.push(trace);
            }
        }
    }
    Ok(traces)
}

fn parse_trace<'a>(lines: &mut std::str::Lines<'a>) -> Result<Option<Trace>, Error> {
    let mut state_index = 0;
    let mut state = None;
    let mut counterexample = Trace::new();
    loop {
        let line = lines.next().expect("unexpected TLC log format.");

        // check if found the start of the next state
        if line.starts_with("@!@!@STARTMSG 2217:4 @!@!@") {
            state_index += 1;
            continue;
        }

        // check if found the end of the current state
        if line.starts_with("@!@!@ENDMSG 2217 @!@!@") {
            let state = state.take().expect("a state should have been started");
            counterexample.add(state);
            continue;
        }

        // any other tag means that this counterexample has ended
        if line.starts_with("@!@!@STARTMSG") {
            break;
        }

        // check if the next state is starting
        if line.starts_with(&format!("{}: ", state_index)) {
            // start next state
            assert!(
                state.is_none(),
                "previous couterexample state has not ended yet"
            );
            state = Some(TLAState::new());
            continue;
        }

        // save any remaining line
        let state = state
            .as_mut()
            .expect("counterexample state should have been started");
        state.push_str(line);
        state.push_str("\n");
    }

    let counterexample = if counterexample.is_empty() {
        None
    } else {
        Some(counterexample)
    };
    Ok(counterexample)
}
