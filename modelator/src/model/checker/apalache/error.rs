use serde::Serialize;
use std::fmt;

/// Contains an Apalache stdout string together with a summary
/// string containing either the line of a matched error, or a string
/// explaining that no error match was found.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize, PartialEq)]
pub struct ApalacheError {
    summary: String,
    stdout: String,
    stderr: String,
}

impl fmt::Display for ApalacheError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_TODO() {}
}
