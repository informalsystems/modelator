use serde::Serialize;
use std::fmt;

/// Contains an Apalache stdout string together with a summary
/// string containing either the line of a matched error, or a string
/// explaining that no error match was found.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize, PartialEq)]
pub struct ErrorMessage {
    summary: String,
    stdout: String,
}

impl fmt::Display for ErrorMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}

const APALACHE_STDOUT_ERRORS: [&str; 21] = [
    "Error by TLA+ parser",
    "Configuration error (see the manual)",
    "Input error (see the manual)",
    "Assignment error",
    "rewriter error",
    "unexpected expression",
    "Unexpected expressions in the specification (see the error messages)",
    "Input error (see the manual)",
    "Typing input error",
    "Type checker error",
    "Irrecoverable preprocessing error",
    "no rule to rewrite a TLA+ expression",
    "rewriter error",
    "error when rewriting to SMT",
    "type error",
    "unexpected TLA+ expression",
    "internal error",
    "checker error",
    "unexpected TLA+ expression",
    "The specification is malformed",
    "Unable to find assignments for all state variables",
];

/// Return the first line containing one of the errors, if any.
/// The list of errors is not exhaustive.
fn try_extract_error_reason(apalache_stdout: &str) -> Option<String> {
    for line in apalache_stdout.split('\n') {
        for summary in APALACHE_STDOUT_ERRORS.iter() {
            if line.contains(summary) {
                return Some(line.to_string());
            }
        }
    }
    None
}

impl ErrorMessage {
    pub(crate) fn new(apalache_stdout: &str) -> ErrorMessage {
        let summary = match try_extract_error_reason(apalache_stdout) {
            Some(line) => line,
            None => {
                "(Modelator) unable to parse reason for error from Apalache output.".to_string()
            }
        };
        ErrorMessage {
            summary,
            stdout: apalache_stdout.to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_errors() {
        let s = "0\n0error when rewriting to SMT0\n0";
        let compare = ErrorMessage {
            summary: "0error when rewriting to SMT0".to_string(),
            stdout: s.to_string(),
        };
        assert_eq!(ErrorMessage::new(s), compare);
    }
}
