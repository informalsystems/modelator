// This module is inspired by what's in:
// https://github.com/informalsystems/ibc-rs/blob/ad827a94e5c84ceb1af764a255dd1821d7852fef/relayer-cli/src/conclude.rs
use crate::Error;
use serde::Serialize;
use serde_json::Value as JsonValue;

#[derive(Serialize, Debug)]
pub struct CliOutput {
    /// The return status
    pub status: CliStatus,

    /// The result of a command.
    pub result: JsonValue,
}

impl CliOutput {
    pub(crate) fn with_result(result: Result<JsonValue, Error>) -> Self {
        let (status, result) = match result {
            Ok(result) => (CliStatus::Success, result),
            Err(err) => {
                let result = match serde_json::to_value(err) {
                    Ok(json_val) => json_val,
                    Err(e) => {
                        panic!("[modelator] CLI error serialization failed: {:?}", e)
                    }
                };
                (CliStatus::Error, result)
            }
        };
        Self { status, result }
    }

    pub fn exit(self) {
        let pretty = match serde_json::to_string_pretty(&self) {
            Ok(pretty) => pretty,
            Err(e) => panic!("[modelator] CLI output serialization failed: {:?}", e),
        };
        println!("{}", pretty);

        // the return code
        if self.status == CliStatus::Error {
            std::process::exit(1);
        } else {
            std::process::exit(0);
        }
    }
}

/// Represents the exit status of any CLI command
#[derive(Serialize, Debug, PartialEq, Eq)]
pub enum CliStatus {
    #[serde(rename(serialize = "success"))]
    Success,

    #[serde(rename(serialize = "error"))]
    Error,
}
