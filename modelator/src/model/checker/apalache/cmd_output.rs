use crate::Error;

use serde::Serialize;
use std::fmt;
#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct CmdOutput {
    pub(crate) stdout: String,
    pub(crate) stderr: String,
}

impl fmt::Display for CmdOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}

fn is_counterexample_line(line: &str) -> bool {
    line.contains("Check the counterexample in:")
}

fn parse_filename(line: &str) -> String {
    // The line looks like '...d. Check the counterexample in: counterexample1.tla, MC1.out, counterexample1.json E@11:13:37.003'
    assert!(is_counterexample_line(line));
    match line.find("in:") {
        None => {
            panic!("Expected to find substring 'in:' in line when parsing for counterexample file name")
        }
        Some(ix) => {
            let slice = &line[ix..];
            let mut split = slice.split(' ');
            // Now have [:, counterexample.tla,, ...]
            split.next();
            let with_trailing_comma = split.next().unwrap();
            with_trailing_comma[..with_trailing_comma.len() - 1].to_owned()
        }
    }
}

fn is_deadlock_line(line: &str) -> bool {
    // This log message appears in a spurious case https://github.com/informalsystems/apalache/issues/1040
    line.starts_with("Found a deadlock. No SMT model.")
}

fn is_error_line(line: &str) -> bool {
    //Searching for strings of this form
    //Len is 14
    //E@11:13:36.959
    if line.len() < 14 {
        return false;
    }
    let substr = &line[(line.len() - 14)..(line.len() - 12)];
    // Exclude the deadlock error.
    substr == "E@" && !is_deadlock_line(line)
}

impl CmdOutput {
    pub(crate) fn apalache_stdout_error_lines(&self) -> Vec<String> {
        self.stdout
            .lines()
            .filter(|line| is_error_line(line))
            .map(ToString::to_string)
            .collect()
    }

    /// Try to get a list of counterexample filenames from stdout. If other Apalache errors are found then
    /// return a Result<Error>
    pub(crate) fn parse_counterexample_filenames(&self) -> Result<Vec<String>, Error> {
        let raw_lines_that_must_be_parsed: Vec<String> = match self.non_counterexample_error() {
            Some(err) => Err(Error::ApalacheFailure(err)),
            None => Ok(self
                .apalache_stdout_error_lines()
                .into_iter()
                .filter(|line| is_counterexample_line(line))
                .collect()),
        }?;
        Ok(raw_lines_that_must_be_parsed
            .iter()
            .map(|line| parse_filename(line))
            .collect())
    }

    pub(crate) fn non_counterexample_error(&self) -> Option<ApalacheError> {
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
    fn test_is_error_line() {
        let line = "State 2: state invariant 0 violated. Check the counterexample in: counterexample1.tla, MC1.out, counterexample1.json E@11:13:37.003";
        let res = is_error_line(line);
        assert!(res);
    }

    #[test]
    fn test_parse_filename() {
        let line = "State 2: state invariant 0 violated. Check the counterexample in: counterexample1.tla, MC1.out, counterexample1.json E@11:13:37.003";
        let res = parse_filename(line);
        assert_eq!("counterexample1.tla".to_owned(), res);
    }

    #[test]
    fn test_parse_all_counterexample_filenames() {
        let to_parse = r#"PASS #13: BoundedChecker                                          I@11:13:35.033
State 2: Checking 1 state invariants                              I@11:13:36.959
State 2: state invariant 0 violated. Check the counterexample in: counterexample1.tla, MC1.out, counterexample1.json E@11:13:37.003
State 2: state invariant 0 violated. Check the counterexample in: counterexample2.tla, MC2.out, counterexample2.json E@11:13:37.015
Found 2 error(s)                                                  I@11:13:37.017
Total time: 4.857 sec                                             I@11:13:37.020
EXITCODE: ERROR (12)
        "#;
        let output = CmdOutput {
            stdout: to_parse.to_owned(),
            stderr: "".to_owned(),
        };
        let res = output.parse_counterexample_filenames().unwrap();
        let expect = vec!["counterexample1.tla", "counterexample2.tla"];
        assert_eq!(expect[0], res[0]);
        assert_eq!(expect[1], res[1]);
    }
}
