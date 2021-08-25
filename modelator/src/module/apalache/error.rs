use serde::Serialize;
use std::fmt;
use thiserror::Error;

/// Errors from Apalache model checker
#[derive(Debug, Error, Serialize)]
pub enum ApalacheError {
    /// Simple error from stdout
    Stdout(String),
}

impl fmt::Display for ApalacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}
