use super::Artifact;
use crate::Error;
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
    states: Vec<TlaState>,
}

impl TlaTrace {
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub(crate) fn add(&mut self, state: TlaState) {
        self.states.push(state);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.states.is_empty()
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
                terminated(
                    preceded(
                        tag_no_case("EXTENDS "),
                        separated_list1(
                            delimited(multispace0, char(','), multispace0),
                            tla_identifiers,
                        ),
                    ),
                    multispace1,
                ),
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
            extends,
            operators,
        },
    )(i)
}

impl FromStr for TlaTrace {
    type Err = Error;

    fn from_str(tla_trace: &str) -> Result<Self, Self::Err> {
        let tla_trace = remove_tla_comments(tla_trace);

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

        let mut trace = TlaTrace::new();
        states
            .into_iter()
            .for_each(|(_, state)| trace.add(state.into()));
        Ok(trace)
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
