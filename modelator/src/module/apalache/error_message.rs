use crate::Error;
use serde::Serialize;
use std::fmt::Debug;

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize)]
pub(crate) struct ErrorMessage {
    summary: String,
    stdout: String,
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

fn try_extract_error_message(apalache_stdout: &str) -> Option<ApalacheErrorMessage> {
    todo!()
}
