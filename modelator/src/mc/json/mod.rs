use super::trace::{JsonTrace, Trace};
use super::util;
use crate::{jar, Error};
use serde_json::Value as JsonValue;
use std::path::{Path, PathBuf};
use tokio::process::Command;

pub(crate) async fn traces_to_json<P: AsRef<Path>>(
    modelator_dir: P,
    traces: Vec<Trace>,
) -> Result<Vec<JsonTrace>, Error> {
    let mut json_traces = Vec::with_capacity(traces.len());
    for trace in traces {
        let json_trace = trace_to_json(&modelator_dir, trace).await?;
        json_traces.push(json_trace);
    }
    Ok(json_traces)
}

async fn trace_to_json<P: AsRef<Path>>(modelator_dir: P, trace: Trace) -> Result<JsonTrace, Error> {
    let mut json_trace = JsonTrace::new();

    // temporary file where each trace state is written to
    let state_file = modelator_dir
        .as_ref()
        .join(format!("{}.state", util::random_string()));

    for state in trace.states {
        // tla2json errors with -1 in the TLA state; for this reason we
        // replace them before converting the state to json
        let constant = "15162342";
        assert!(!state.contains(constant));
        let state = state.replace("-1", constant);

        // write state to a file
        tokio::fs::write(&state_file, &state)
            .await
            .map_err(Error::IO)?;

        // convert it to json
        let result = cmd(&modelator_dir, &state_file).output().await;

        // remove temporary trace state file (before checking if an error has
        // occurred)
        tokio::fs::remove_file(&state_file)
            .await
            .map_err(Error::IO)?;

        // exit if an error has occurred
        let output = result.map_err(Error::IO)?;

        if output.status.success() {
            // if the command succeeded, get json from the stdout
            let json = util::output_to_string(&output.stdout);

            // replace constant back
            let json = json.replace(constant, "-1");

            // parse json
            let json: JsonValue = serde_json::from_str(&json).map_err(Error::Serde)?;

            // add to trace
            json_trace.add(json);
        } else {
            // if the command has not succeeded, get error from the stderr
            let error = util::output_to_string(&output.stderr);
            return Err(Error::Tla2Json { state, error });
        }
    }
    Ok(json_trace)
}

fn cmd<P: AsRef<Path>>(modelator_dir: P, state_file: &PathBuf) -> Command {
    let tla2json = jar::Jar::Tla2Json.file(&modelator_dir);
    let mut cmd = Command::new("java");
    cmd
        // set jar
        .arg("-jar")
        .arg(tla2json.as_path())
        // set state file
        .arg("-S")
        .arg(state_file.as_path());
    cmd
}
