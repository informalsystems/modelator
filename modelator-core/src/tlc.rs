use crate::jar;
use color_eyre::{eyre, Report};
use rayon::prelude::*;
use serde_json::Value;
use std::path::Path;
use xshell::{cmd, rm_rf, write_file};

pub struct Tlc {
    pub input: String,
    pub all_counterexamples: bool,
    pub workers: String,
    pub log: String,
}

type State = String;
struct Counterexample {
    states: Vec<State>,
}

impl Counterexample {
    fn new() -> Self {
        Self { states: Vec::new() }
    }

    fn add(&mut self, state: State) {
        self.states.push(state);
    }

    fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

impl Tlc {
    pub fn run(&self, dir: &str) -> Result<Vec<String>, Report> {
        // trim .tla from input file
        let model_name = self.input.trim_end_matches(".tla");
        let tla_file = format!("{}.tla", model_name);
        let cfg_file = format!("{}.cfg", model_name);

        // check that both the tla and the corresponding .cfg file exist
        if !Path::new(&tla_file).is_file() {
            eyre::bail!("TLA file not found: {}", tla_file);
        }
        if !Path::new(&cfg_file).is_file() {
            eyre::bail!("TLC config file not found: {}", cfg_file);
        }

        // create tlc command
        let tla2tools = jar::Jar::Tla.file(&dir);
        let community_modules = jar::Jar::CommunityModules.file(&dir);
        let workers = &self.workers;
        let mut cmd = cmd!("java -cp {tla2tools}:{community_modules} -XX:+UseParallelGC tlc2.TLC {tla_file} -tool -modelcheck -config {cfg_file} -workers {workers}");
        // maybe add additional "-continue" argument
        if self.all_counterexamples {
            cmd = cmd.arg("-continue");
        }

        // run tlc
        let output = cmd
            // ignore tlc error
            .ignore_status()
            .output()
            // get the stdout
            .map(|output| Self::output_to_string(&output.stdout))?;

        // save TLC log
        write_file(&self.log, &output)?;

        // convert tlc output to counterexamples
        let counterexamples = TlcOutput::parse(output)?;
        if counterexamples.is_empty() {
            eyre::bail!(
                "no counterexample found. check the TLC log in '{}'",
                self.log
            )
        }
        // convert each counterexample to json
        self.counterexamples_to_json(counterexamples, dir)
    }

    fn counterexamples_to_json(
        &self,
        counterexamples: Vec<Counterexample>,
        dir: &str,
    ) -> Result<Vec<String>, Report> {
        counterexamples
            .into_par_iter()
            .enumerate()
            .map(|(index, counterexample)| self.counterexample_to_json(index, counterexample, dir))
            .collect()
    }

    fn counterexample_to_json(
        &self,
        index: usize,
        counterexample: Counterexample,
        dir: &str,
    ) -> Result<String, Report> {
        // convert each state in the counterexample to json
        let tla2json = jar::Jar::Tla2Json.file(&dir);

        // list with each counterexample state converted to json
        let mut jsons = Vec::new();
        // temporary file where each counterexample state is written to
        let state_file = format!("{}/counterexample{}.state", dir, index);

        for state in counterexample.states {
            // tla2json errors with -1 in the TLA state; for this reason we
            // replace them before converting the state to json
            let constant = "15162342";
            assert!(!state.contains(constant));
            let state = state.replace("-1", constant);

            // write state to a file
            write_file(&state_file, &state)?;

            // convert it to json
            let result = cmd!("java -jar {tla2json} -S {state_file}")
                .ignore_status()
                .output();

            // remove temporary counterexample state file (before checking if
            // an error has occurred)
            rm_rf(&state_file)?;

            // exit if an error has occurred
            let output = result?;
            if output.status.success() {
                // if the command succeeded, get json from the stdout
                let json = Self::output_to_string(&output.stdout);

                // replace constant back
                let json = json.replace(constant, "-1");

                // save json
                jsons.push(json);
            } else {
                // if the command has not succeeded, get error from the stderr
                let error = Self::output_to_string(&output.stderr);
                eyre::bail!(
                    "error parsing TLA state.\nstate:\n{}\nerror:\n{}",
                    state,
                    error
                );
            }
        }

        // aggregate all counterexample states (already converted to json) into
        // a json array
        let json_array = format!("[{}]", jsons.join(","));

        // pretty print json array
        let counterexample: Value = serde_json::from_str(&json_array)?;
        let counterexample = serde_json::to_string_pretty(&counterexample)?;
        Ok(counterexample)
    }

    fn output_to_string(output: &Vec<u8>) -> String {
        String::from_utf8_lossy(output).to_string()
    }
}

struct TlcOutput;

impl TlcOutput {
    fn parse(output: String) -> Result<Vec<Counterexample>, Report> {
        let mut counterexamples = Vec::new();
        let mut lines = output.lines();

        while let Some(line) = lines.next() {
            // check if found the beginning of the next counterexample
            if line.starts_with("@!@!@ENDMSG 2121 @!@!@") {
                if let Some(counterexample) = Self::parse_counterexample(&mut lines)? {
                    counterexamples.push(counterexample);
                }
            }
        }
        Ok(counterexamples)
    }

    fn parse_counterexample<'a>(
        lines: &mut std::str::Lines<'a>,
    ) -> Result<Option<Counterexample>, Report> {
        let mut state_index = 0;
        let mut state = None;
        let mut counterexample = Counterexample::new();
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
                state = Some(State::new());
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
}
