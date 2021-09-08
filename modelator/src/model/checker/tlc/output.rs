use crate::artifact::tla_trace::{TlaState, TlaTrace};
use crate::model::checker::ModelCheckerRuntime;
use crate::Error;

use std::collections::HashMap;

// TODO: don't need entire options object
pub(crate) fn parse(output: &str, runtime: &ModelCheckerRuntime) -> Result<Vec<TlaTrace>, Error> {
    let mut parsed_output: HashMap<u8, HashMap<usize, Vec<String>>> = HashMap::new();

    let mut curr_message_id = None;
    let mut curr_message = String::new();

    output.lines().for_each(|line| {
        if line.starts_with("@!@!@STARTMSG ") {
            // without annotattion
            let (code, class) = curr_message_id.take().unwrap_or((0, 0));
            parsed_output
                .entry(class)
                .or_default()
                .entry(code)
                .or_default()
                .push(curr_message.drain(..).collect());

            let (code, class) = line.splitn(3, ' ').nth(1).unwrap().split_once(':').unwrap();
            curr_message_id.insert((code.parse().unwrap(), class.parse().unwrap()));
        } else if line.starts_with("@!@!@ENDMSG ") {
            let (code, class) = curr_message_id.take().unwrap_or((0, 0));
            parsed_output
                .entry(class)
                .or_default()
                .entry(code)
                .or_default()
                .push(curr_message.drain(..).collect());

            let c_code = line.splitn(3, ' ').nth(1).unwrap();
            assert_eq!(code, c_code.parse::<usize>().unwrap());
        } else {
            curr_message.push_str(line);
            curr_message.push('\n');
        }
    });

    if let Some(lines) = parsed_output.get(&4).and_then(|x| x.get(&2217)) {
        let mut traces = Vec::new();
        let mut trace = None;
        for line in lines {
            if line.starts_with("1: <Initial predicate>") {
                // start of new trace
                if let Some(t) = trace.take() {
                    traces.push(t);
                }
                trace = Some(TlaTrace::new());
            }
            if let Some(t) = trace.as_mut() {
                t.add(line.split_once('\n').unwrap().1.into());
            }
        }
        // last trace
        if let Some(t) = trace.take() {
            traces.push(t);
        }
        Ok(traces)
    } else if let Some(errors) = parsed_output.get(&1) {
        // Message Codes ref
        // https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/output/EC.java
        // Message Classes ref
        // https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/output/MP.java
        // NONE = 0; ERROR = 1; TLCBUG = 2; WARNING = 3; STATE = 4;

        let message = errors
            .iter()
            .map(|(code, message)| {
                format!(
                    "[{}:{}]: {}",
                    runtime.log.to_string_lossy(),
                    code,
                    &message
                        .iter()
                        .map(|x| x.trim().replace("\n", " "))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        Err(Error::TLCFailure(message))
    } else {
        Ok(vec![])
    }
}

fn parse_trace<'a>(
    lines: &mut impl Iterator<Item = &'a str>,
    runtime: &ModelCheckerRuntime,
) -> Result<Option<TlaTrace>, Error> {
    let mut state_index = 0;
    let mut state = None;
    let mut trace = TlaTrace::new();
    loop {
        let line = lines
            .next()
            .ok_or_else(|| Error::InvalidTLCOutput(runtime.log.clone()))?;

        // check if found the start of the next state
        if line.starts_with("@!@!@STARTMSG 2217:4 @!@!@") {
            state_index += 1;
            continue;
        }

        // check if found the end of the current state
        if line.starts_with("@!@!@ENDMSG 2217 @!@!@") {
            let state = state
                .take()
                .expect("[modelator] a trace state should have been started");
            trace.add(state);
            continue;
        }

        // any other tag means that this trace has ended
        if line.starts_with("@!@!@STARTMSG") {
            break;
        }

        // check if the next state is starting
        if line.starts_with(&format!("{}: ", state_index)) {
            // start next state
            assert!(
                state.is_none(),
                "[modelator] previous trace state has not ended yet"
            );
            state = Some(TlaState::new());
            continue;
        }

        // save any remaining line
        let state = state
            .as_mut()
            .expect("[modelator] trace state should have been started");
        state.push_str(line);
        state.push('\n');
    }

    let trace = if trace.is_empty() { None } else { Some(trace) };
    Ok(trace)
}
