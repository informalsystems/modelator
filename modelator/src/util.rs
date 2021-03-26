use crate::Error;
use serde::de::DeserializeOwned;
use std::path::PathBuf;
use std::process::Command;

pub(crate) fn cmd_output_to_string(output: &[u8]) -> String {
    String::from_utf8_lossy(output).to_string()
}

pub(crate) fn cmd_show(cmd: &Command) -> String {
    let cmd = format!("{:?}", cmd).replace("\"", "");
    let cmd = cmd.trim_start_matches("Command { std:");
    let cmd = cmd.trim_end_matches(", kill_on_drop: false }");
    cmd.to_owned()
}

pub(crate) fn absolute_path(path: &PathBuf) -> String {
    match path.canonicalize() {
        Ok(path) => path.to_string_lossy().to_string(),
        Err(e) => panic!("[modelator] couldn't compute absolute path: {:?}", e),
    }
}

/// A macro that generates a complete setter method from a one-liner with necessary information
#[macro_export]
macro_rules! set_option {
    ($name:ident, $t:ty) => {
        pub fn $name(mut self, $name: $t) -> Self {
            self.$name = Some($name.clone());
            self
        }
    };
    ($name:ident, $t:ty, $val:expr) => {
        pub fn $name(mut self, $name: $t) -> Self {
            self.$name = $val;
            self
        }
    };
}

/// Tries to parse a string as the given type
pub fn parse_from_str<T: DeserializeOwned>(input: &str) -> Result<T, Error> {
    match serde_json::from_str(input) {
        Ok(res) => Ok(res),
        Err(e) => Err(Error::ParseError(e.to_string())),
    }
}

/// Tries to parse a Json Value as the given type
pub fn parse_from_value<T: DeserializeOwned>(input: serde_json::Value) -> Result<T, Error> {
    match serde_json::from_value(input) {
        Ok(res) => Ok(res),
        Err(e) => Err(Error::ParseError(e.to_string())),
    }
}
