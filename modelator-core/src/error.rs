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
}
