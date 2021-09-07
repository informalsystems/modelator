use crate::Error;

use serde::Serialize;
use std::fmt;
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize, PartialEq)]
pub struct CmdOutput {
    pub stdout: String,
    pub stderr: String,
}

impl fmt::Display for CmdOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}

fn is_counterexample_line(line: &str) -> bool {
    line.contains("Check the counterexample in:")
}

fn is_error_line(line: &str) -> bool {
    //Searching for strings of this form
    //Len is 14
    //E@11:13:36.959
    13 < line.len() && &line[(line.len() - 14)..(line.len() - 13)] == "E@"
}

impl CmdOutput {
    pub fn apalache_stdout_error_lines(&self) -> Vec<String> {
        self.stdout
            .lines()
            .filter(|line| is_error_line(line))
            .map(ToString::to_string)
            .collect()
    }

    /// Try to get a list of counterexample filenames from stdout. If other Apalache errors are found then
    /// return a Result<Error>
    pub fn parse_counterexample_filenames(&self) -> Result<Vec<String>, Error> {
        let unparsed_lines = match self.non_counterexample_error() {
            Some(err) => Err(Error::ApalacheFailure(err)),
            None => Ok(self
                .apalache_stdout_error_lines()
                .into_iter()
                .filter(|line| is_counterexample_line(line))
                .collect())
        }?;
        unparsed_lines.in
    }

    pub fn non_counterexample_error(&self) -> Option<ApalacheError> {
        match (self.stdout.is_empty(), self.stderr.is_empty()) {
            (true, true) => Some(ApalacheError {
                summary: "stdout and stderr both empty".to_owned(),
                output: CmdOutput {
                    stdout: self.stdout.clone(),
                    stderr: self.stderr.clone(),
                },
            }),
            (false, true) => {
                let non_counterexample_error_lines: Vec<String> = self
                    .apalache_stdout_error_lines()
                    .into_iter()
                    .filter(|line| !is_counterexample_line(line))
                    .collect();

                match non_counterexample_error_lines.is_empty() {
                    true => None,
                    false => Some(ApalacheError {
                        summary: "Non counterexample errors found in stdout:\n".to_owned()
                            + &non_counterexample_error_lines.join("\n"),
                        output: CmdOutput {
                            stdout: self.stdout.clone(),
                            stderr: self.stderr.clone(),
                        },
                    }),
                }
            }
            _ => Some(ApalacheError {
                summary: "stderr not empty".to_owned(),
                output: CmdOutput {
                    stdout: self.stdout.clone(),
                    stderr: self.stderr.clone(),
                },
            }),
        }
    }
}

/// Contains an Apalache stdout string together with a summary
/// string containing either the line of a matched error, or a string
/// explaining that no error match was found.
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize, PartialEq)]
pub struct ApalacheError {
    summary: String,
    output: CmdOutput,
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
