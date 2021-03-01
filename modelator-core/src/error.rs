use thiserror::Error;

#[derive(Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(std::io::Error),

    #[error("Invalid unicode error: {0:#?}")]
    InvalidUnicode(std::ffi::OsString),

    #[error("File not found: {0}")]
    FileNotFound(std::path::PathBuf),

    #[error("Reqwest error: {0}")]
    Reqwest(reqwest::Error),

    #[error("Error parsing TLA state:\n{state}\nerror:\n{error}")]
    Tla2Json { state: String, error: String },

    #[error("Serde error: {0}")]
    Serde(serde_json::Error),

    #[error("No trace found. Check the model checker log: {0}")]
    NoTraceFound(std::path::PathBuf),

    #[error("Invalid TLC output: {0}")]
    InvalidTLCOutput(std::path::PathBuf),
}
