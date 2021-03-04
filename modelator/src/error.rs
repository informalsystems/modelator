use std::fmt::Debug;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(std::io::Error),

    #[error("Invalid unicode: {0:?}")]
    InvalidUnicode(std::ffi::OsString),

    #[error("File not found: {0}")]
    FileNotFound(std::path::PathBuf),

    #[error("Error parsing TLA state:\n{state}\nerror:\n{error}")]
    TlaParse { state: String, error: String },

    #[error("No trace found. Check the model checker log: {0}")]
    NoTraceFound(std::path::PathBuf),

    #[error("Invalid TLC output: {0}")]
    InvalidTLCOutput(std::path::PathBuf),

    #[error("Reqwest error: {0}")]
    Reqwest(reqwest::Error),

    #[error("Serde error: {0}")]
    Serde(serde_json::Error),

    #[error("Nom error: {0}")]
    Nom(String)
}

#[derive(Error, Debug)]
pub enum TestError<Runner: Debug, Step: Debug> {
    #[error("Error while running modelator: {0}")]
    Modelator(Error),

    #[error("Test step failed to be deserialized: {0}")]
    Deserialize(serde_json::Error),

    #[error(
        "Test failed on step {step_index}/{step_count}:\nsteps: {steps:#?}\nrunner: {runner:#?}"
    )]
    FailedTest {
        step_index: usize,
        step_count: usize,
        steps: Vec<Step>,
        runner: Runner,
    },
}
