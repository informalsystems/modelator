use serde::Serialize;
use std::fmt::Debug;
use thiserror::Error;

#[allow(clippy::upper_case_acronyms)]
#[derive(Error, Debug, Serialize)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(String),

    #[error("Invalid unicode: {0:?}")]
    InvalidUnicode(std::ffi::OsString),

    #[error("File not found: {0}")]
    FileNotFound(std::path::PathBuf),

    #[error("Missing Java. Please install it.")]
    MissingJava,

    #[error("Current Java version is: {0}. Minimum Java version supported is: {1}")]
    MinimumJavaVersion(usize, usize),

    #[error("Error parsing TLA state:\n{state}\nerror:\n{error}")]
    TlaParse { state: String, error: String },

    #[error("No test found in {0}")]
    NoTestFound(std::path::PathBuf),

    #[error("No trace found in {0}")]
    NoTraceFound(std::path::PathBuf),

    #[error("Invalid TLC output: {0}")]
    InvalidTLCOutput(std::path::PathBuf),

    #[error("TLC failure: {0}")]
    TLCFailure(String),

    #[error("Apalache failure: {0}")]
    ApalacheFailure(String),

    #[error("Invalid Apalache counterexample: {0}")]
    InvalidApalacheCounterexample(String),

    #[error("Nom error: {0}")]
    Nom(String),
}

impl Error {
    pub(crate) fn io(err: std::io::Error) -> Error {
        Error::IO(err.to_string())
    }

    pub(crate) fn nom(err: nom::Err<nom::error::Error<&str>>) -> Error {
        Error::Nom(err.to_string())
    }
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
