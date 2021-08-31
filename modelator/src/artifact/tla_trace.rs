use super::{Artifact, ArtifactCreator};
use crate::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, tag_no_case, take_until},
    character::complete::{alpha1, alphanumeric1, char, multispace0, multispace1},
    combinator::{map, opt, recognize, rest},
    multi::{many0, many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    IResult,
};

pub(crate) type TlaState = String;

/// `modelator`'s artifact containing a test trace encoded as TLA+.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaTrace {
    /// TODO: file_contents backing strings are to be removed
    file_contents_backing: String,

    states: Vec<TlaState>,
    // Name of module that is extended by the trace
    pub(crate) extends_module_name: Option<String>,
}

impl TlaTrace {
    pub(crate) fn add(&mut self, state: TlaState) {
        self.states.push(state);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    pub(crate) fn new() -> Self {
        Self {
            states: Vec::new(),
            extends_module_name: None,
            file_contents_backing: "".to_owned(),
        }
    }
}

impl IntoIterator for TlaTrace {
    type Item = TlaState;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.states.into_iter()
    }
}

impl std::fmt::Display for TlaTrace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (index, state) in self.states.iter().enumerate() {
            write!(f, "State{} ==\n{}", index, state)?;
        }
        Ok(())
    }
}

impl ArtifactCreator for TlaTrace {
    fn from_string(s: &str) -> Result<Self, Error> {
        // Ok(TlaTrace {
        //     states: Vec::new(),
        //     extends_module_name: None,
        //     file_contents_backing: "".to_owned(),
        // })
        let tla_trace = remove_tla_comments(s);

        let tla: TlaTraceFileContent<'_> = parse_tla_trace_file_contents(&tla_trace).unwrap().1;

        let mut states: Vec<(usize, &str)> = tla
            .operators
            .into_iter()
            .filter(|(identifier, _)| identifier.starts_with("State"))
            .map(|(k, state)| (k[5..k.len()].parse().unwrap(), state))
            .collect();

        states.sort_unstable();
        states.dedup_by_key(|(k, _)| *k);

        assert_eq!(
            (states.first().unwrap().0, states.last().unwrap().0 + 1),
            (0, states.len()),
            "some consecutive states are missing in .tla trace"
        );

        let mut trace = Self::new();
        states
            .into_iter()
            .for_each(|(_, state)| trace.add(state.into()));
        Ok(trace)
    }
}

impl Artifact for TlaTrace {
    fn as_string(&self) -> String {
        match &self.extends_module_name {
            None => format!("{}", self),
            Some(name) => {
                format!(
                    "---- MODULE trace ----\n\nEXTENDS {}\n\n{}\n====",
                    name, self
                )
            }
        }
    }
}

fn tla_single_line_comment(i: &str) -> IResult<&str, &str> {
    recognize(pair(tag("\\*"), is_not("\n\r")))(i)
}

fn tla_multi_line_comment(i: &'_ str) -> IResult<&str, &str> {
    recognize(delimited(tag("(*"), take_until("*)"), tag("*)")))(i)
}

fn remove_tla_single_line_comments(i: &str) -> IResult<&str, String> {
    map(
        preceded(
            opt(tla_single_line_comment),
            separated_list0(tla_single_line_comment, alt((take_until("\\*"), rest))),
        ),
        |value| value.concat(),
    )(i)
}

fn remove_tla_multi_line_comments(i: &str) -> IResult<&str, String> {
    map(
        preceded(
            opt(tla_multi_line_comment),
            separated_list0(tla_multi_line_comment, alt((take_until("(*"), rest))),
        ),
        |value| value.concat(),
    )(i)
}

fn remove_tla_comments(i: &str) -> String {
    let (_, s) = remove_tla_single_line_comments(i).unwrap();
    let (_, s) = remove_tla_multi_line_comments(&s).unwrap();
    s
}

fn tla_identifiers(i: &str) -> IResult<&str, &str> {
    recognize(pair(
        alt((alpha1, tag("_"))),
        many0(alt((alphanumeric1, tag("_")))),
    ))(i)
}

#[derive(Debug)]
struct TlaTraceFileContent<'a> {
    name: &'a str,
    extends: Vec<&'a str>,
    operators: Vec<(&'a str, &'a str)>,
}

fn parse_tla_trace_file_contents(i: &str) -> IResult<&str, TlaTraceFileContent<'_>> {
    map(
        terminated(
            tuple((
                terminated(
                    delimited(
                        many1(char('-')),
                        delimited(
                            multispace1,
                            preceded(tag_no_case("MODULE "), tla_identifiers),
                            multispace1,
                        ),
                        many1(char('-')),
                    ),
                    multispace1,
                ),
                opt(terminated(
                    preceded(
                        tag_no_case("EXTENDS "),
                        separated_list1(
                            delimited(multispace0, char(','), multispace0),
                            tla_identifiers,
                        ),
                    ),
                    multispace1,
                )),
                separated_list1(
                    multispace1,
                    separated_pair(
                        tla_identifiers,
                        delimited(multispace0, tag("=="), multispace0),
                        take_until("\n\n"),
                    ),
                ),
            )),
            delimited(multispace0, many1(char('=')), multispace0),
        ),
        |(name, extends, operators)| TlaTraceFileContent {
            name,
            extends: extends.unwrap_or_default(),
            operators,
        },
    )(i)
}
