use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while},
    character::complete::{char, digit1, multispace0, satisfy},
    combinator::{complete, cut, map, opt, recognize, value},
    multi::{many1, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, separated_pair},
    IResult,
};

use serde_json::Value as JsonValue;

pub(crate) fn parse_state(i: &str) -> IResult<&str, JsonValue> {
    map(
        preceded(
            opt(delimited(multispace0, complete(tag("/\\")), multispace0)),
            separated_list0(
                delimited(multispace0, complete(tag("/\\")), multispace0),
                parse_var,
            ),
        ),
        |value| JsonValue::Object(value.into_iter().collect()),
    )(i)
}

fn parse_var(i: &str) -> IResult<&str, (String, JsonValue)> {
    delimited(
        multispace0,
        separated_pair(
            parse_identifier,
            delimited(multispace0, char('='), multispace0),
            parse_any_value,
        ),
        multispace0,
    )(i)
}

// TODO: what else can TLA var idenfitiers have?
fn parse_identifier(i: &str) -> IResult<&str, String> {
    map(
        many1(satisfy(|c| c.is_alphanumeric() || "_-".contains(c))),
        |value| value.into_iter().collect(),
    )(i)
}

fn parse_identifiers_as_values(i: &str) -> IResult<&str, JsonValue> {
    map(parse_identifier, JsonValue::String)(i)
}

fn parse_any_value(i: &str) -> IResult<&str, JsonValue> {
    preceded(
        multispace0,
        alt((
            parse_bool,
            parse_function,
            parse_range,
            parse_number,
            parse_string,
            parse_identifiers_as_values,
            parse_set,
            parse_sequence,
            parse_record,
        )),
    )(i)
}

fn parse_bool(i: &str) -> IResult<&str, JsonValue> {
    map(
        alt((value(true, tag("TRUE")), value(false, tag("FALSE")))),
        JsonValue::Bool,
    )(i)
}

fn parse_number(i: &str) -> IResult<&str, JsonValue> {
    alt((parse_pos_number, parse_neg_number))(i)
}

fn parse_pos_number(i: &str) -> IResult<&str, JsonValue> {
    map(digit1, |value: &str| {
        JsonValue::Number(
            value
                .parse::<u64>()
                .expect("u64 parsed by nom should be a valid u64")
                .into(),
        )
    })(i)
}

fn parse_neg_number(i: &str) -> IResult<&str, JsonValue> {
    map(preceded(char('-'), digit1), |value| {
        JsonValue::Number(
            format!("-{}", value)
                .parse::<i64>()
                .expect("i64 parsed by nom should be a valid i64")
                .into(),
        )
    })(i)
}

fn parse_string(i: &str) -> IResult<&str, JsonValue> {
    map(
        delimited(char('"'), cut(take_while(|c| c != '"')), char('"')),
        |value: &str| JsonValue::String(value.into()),
    )(i)
}

fn parse_range(i: &str) -> IResult<&str, JsonValue> {
    map(
        separated_pair(parse_number, tag(".."), parse_number),
        |(low, high)| {
            JsonValue::Array(
                (low.as_i64().unwrap()..=high.as_i64().unwrap())
                    .map(|x| JsonValue::Number(x.into()))
                    .collect(),
            )
        },
    )(i)
}

fn parse_set(i: &str) -> IResult<&str, JsonValue> {
    map(
        delimited(
            pair(char('{'), multispace0),
            cut(separated_list0(
                delimited(multispace0, char(','), multispace0),
                parse_any_value,
            )),
            pair(multispace0, char('}')),
        ),
        JsonValue::Array,
    )(i)
}

fn parse_sequence(i: &str) -> IResult<&str, JsonValue> {
    map(
        delimited(
            pair(tag("<<"), multispace0),
            cut(separated_list0(
                delimited(multispace0, char(','), multispace0),
                parse_any_value,
            )),
            pair(multispace0, tag(">>")),
        ),
        JsonValue::Array,
    )(i)
}

fn parse_function(i: &str) -> IResult<&str, JsonValue> {
    map(
        delimited(
            multispace0,
            separated_list1(
                delimited(multispace0, complete(tag("@@")), multispace0),
                alt((
                    map(parse_function_entry, |x| {
                        JsonValue::Object(vec![x].into_iter().collect())
                    }),
                    delimited(
                        pair(char('('), multispace0),
                        parse_function,
                        pair(multispace0, char(')')),
                    ),
                )),
            ),
            multispace0,
        ),
        |values| {
            JsonValue::Object(
                values
                    .into_iter()
                    .flat_map(|value| {
                        value
                            .as_object()
                            .unwrap()
                            .into_iter()
                            .map(|(k, v)| (k.clone(), v.clone()))
                            .collect::<Vec<_>>()
                    })
                    .collect(),
            )
        },
    )(i)
}

fn parse_function_entry(i: &str) -> IResult<&str, (String, JsonValue)> {
    preceded(
        multispace0,
        separated_pair(
            parse_identifier,
            delimited(multispace0, complete(tag(":>")), multispace0),
            parse_any_value,
        ),
    )(i)
}

fn parse_record(i: &str) -> IResult<&str, JsonValue> {
    map(
        delimited(
            pair(char('['), multispace0),
            cut(separated_list1(
                delimited(multispace0, char(','), multispace0),
                parse_record_entry,
            )),
            pair(multispace0, char(']')),
        ),
        |value| JsonValue::Object(value.into_iter().collect()),
    )(i)
}

fn parse_record_entry(i: &str) -> IResult<&str, (String, JsonValue)> {
    preceded(
        multispace0,
        separated_pair(
            parse_identifier,
            delimited(multispace0, tag("|->"), multispace0),
            parse_any_value,
        ),
    )(i)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;
    use serde_json::json;

    macro_rules! check_ok {
        ($fun:ident, $value:expr) => {{
            check_ok!($fun, $value, $value)
        }};
        ($fun:ident, $value:expr, $json_value:expr) => {{
            const REST: &str = "_REST";
            let argument = format!("{}{}", $value, REST);
            let expected = Ok((REST, json!($json_value)));
            $fun(&argument) == expected
        }};
    }

    #[test]
    fn parse_bool_test() {
        assert!(check_ok!(parse_bool, "TRUE", true));
        assert!(check_ok!(parse_bool, "FALSE", false));
    }

    #[quickcheck]
    fn parse_pos_number_test(value: u64) -> bool {
        check_ok!(parse_number, value)
    }

    #[quickcheck]
    fn parse_neg_number_test(value: i64) -> bool {
        check_ok!(parse_number, value)
    }

    #[test]
    fn parse_string_test() {
        let parse_and_check =
            |value| assert!(check_ok!(parse_string, format!("\"{}\"", value), value));
        parse_and_check("");
        parse_and_check("A1");
        parse_and_check("abc XYZ!");
        parse_and_check("abc;.\n123-_\\");
    }

    #[test]
    fn parse_state_test() {
        let states = vec![
            (
                booleans_and_numbers_state_without_first_logical_and(),
                booleans_and_numbers_expected(),
            ),
            (
                booleans_and_numbers_state(),
                booleans_and_numbers_expected(),
            ),
            (sets_state(), sets_expected()),
            (sequences_state(), sequences_expected()),
            (records_state(), records_expected()),
            (functions_state(), functions_expected()),
            (state1(), expected1()),
            (state2(), expected2()),
            (state3(), expected3()),
            (state4(), expected4()),
            (state5(), expected5()),
        ];
        for (state, expected) in states {
            let result = parse_state(state);
            println!("\n\nR: {:?}", result);
            assert!(result.is_ok());
            let (input, state) = result.unwrap();
            assert!(input.is_empty());
            assert_eq!(state, expected);
        }
    }

    const fn booleans_and_numbers_state_without_first_logical_and() -> &'static str {
        r#"
            empty_set = {} /\ set = {1, 2, 3} /\ pos_number = 1 /\ neg_number = -1 /\ bool = TRUE
        "#
    }

    const fn booleans_and_numbers_state() -> &'static str {
        r#"
            /\ empty_set = {}
            /\ set = {1, 2, 3}
            /\ pos_number = 1
            /\ neg_number = -1
            /\ bool = TRUE
        "#
    }

    fn booleans_and_numbers_expected() -> JsonValue {
        json!({
            "empty_set": [],
            "set": [1, 2, 3],
            "pos_number": 1,
            "neg_number": -1,
            "bool": true
        })
    }

    const fn sets_state() -> &'static str {
        r#"
            /\ empty_set = {}
            /\ set = {1, 2, 3}
            /\ pos_number = 1
            /\ neg_number = -1
            /\ bool = TRUE
        "#
    }

    fn sets_expected() -> JsonValue {
        json!({
            "empty_set": [],
            "set": [1, 2, 3],
            "pos_number": 1,
            "neg_number": -1,
            "bool": true
        })
    }

    const fn sequences_state() -> &'static str {
        r#"
            /\ empty_seq = <<>>
            /\ seq = <<1, 2, 3>>
            /\ pos_number = 1
            /\ neg_number = -1
            /\ bool = TRUE
        "#
    }

    fn sequences_expected() -> JsonValue {
        json!({
            "empty_seq": [],
            "seq": [1, 2, 3],
            "pos_number": 1,
            "neg_number": -1,
            "bool": true
        })
    }

    const fn records_state() -> &'static str {
        r#"
            /\ record = (t1 :> "-" @@ t2 :> "-")
            /\ mix = (set :> {-1, -2, 3} @@ number :> 99)
        "#
    }

    fn records_expected() -> JsonValue {
        json!({
            "record": {
                "t1": "-",
                "t2": "-",
            },
            "mix": {
                "set": [-1, -2, 3],
                "number": 99,
            },
        })
    }

    const fn functions_state() -> &'static str {
        r#"
            /\ function = [t1 |-> "-", t2 |-> "-"]
            /\ mix = [set |-> {-1, -2, 3}, number |-> 99]
        "#
    }

    fn functions_expected() -> JsonValue {
        json!({
            "function": {
                "t1": "-",
                "t2": "-",
            },
            "mix": {
                "set": [-1, -2, 3],
                "number": 99,
            },
        })
    }

    /// The tests that follow are translated from some of the tests in <https://github.com/japgolly/tla2json>
    const fn state1() -> &'static str {
        r#"
            /\ browsers = (b1 :> << >>)
            /\ network = <<>>
            /\ tabs = (t1 :> [status |-> "-"] @@ t2 :> [status |-> "-"])
            /\ remote = {}
            /\ workers = (w1 :> [status |-> "-"] @@ w2 :> [status |-> "-"])
        "#
    }

    fn expected1() -> JsonValue {
        json!({
            "browsers": {
                "b1": []
            },
            "network": [],
            "tabs": {
                "t1": {
                    "status": "-"
                },
                "t2": {
                    "status": "-"
                }
            },
            "remote": [],
            "workers": {
                "w1": {
                    "status": "-"
                },
                "w2": {
                    "status": "-"
                }
            },
        })
    }

    const fn state2() -> &'static str {
        r#"
/\ tabs = ( t1 :> [status |-> "-"] @@
  t2 :>
      [ drafts |-> {},
        worker |-> w1,
        status |-> "loading",
        awaiting |-> {"Remote"} ] )
/\ workers = ( w1 :>
      [ drafts |-> {},
        time |-> 1,
        status |-> "live",
        browser |-> b1,
        sync |-> [Remote |-> [desired |-> 0, lastReq |-> 0, lastAck |-> 0]] ] @@
  w2 :> [status |-> "-"] )
"#
    }

    fn expected2() -> JsonValue {
        json!({
            "tabs": {
                "t1": {
                    "status": "-"
                },
                "t2": {
                    "drafts": [],
                    "worker": "w1",
                    "status": "loading",
                    "awaiting": [
                        "Remote"
                    ]
                }
            },
            "workers": {
                "w1": {
                    "drafts": [],
                    "time": 1,
                    "status": "live",
                    "browser": "b1",
                    "sync": {
                        "Remote": {
                            "desired": 0,
                            "lastReq": 0,
                            "lastAck": 0,
                        }
                    }
                },
                "w2": {
                    "status": "-"
                }
            },
        })
    }

    const fn state3() -> &'static str {
        r#"
/\ tabs = ( t1 :>
      [ drafts |-> {},
        worker |-> w2,
        status |-> "loading",
        awaiting |-> {"Remote"} ] @@
  t2 :>
      [ drafts |-> {},
        worker |-> w1,
        status |-> "loading",
        awaiting |-> {"Remote"} ] )
/\ workers = ( w1 :>
      [ drafts |-> {},
        time |-> 1,
        status |-> "live",
        browser |-> b1,
        sync |-> [Remote |-> [desired |-> 0, lastReq |-> 0, lastAck |-> 0]] ] @@
  w2 :>
      [ drafts |-> {},
        time |-> 1,
        status |-> "live",
        browser |-> b1,
        sync |-> [Remote |-> [desired |-> 0, lastReq |-> 0, lastAck |-> 0]] ] )
"#
    }

    fn expected3() -> JsonValue {
        json!({
            "tabs": {
                "t1": {
                    "drafts": [],
                    "worker": "w2",
                    "status": "loading",
                    "awaiting": [
                        "Remote"
                    ]
                },
                "t2": {
                    "drafts": [],
                    "worker": "w1",
                    "status": "loading",
                    "awaiting": [
                        "Remote"
                    ]
                }
            },
            "workers": {
                "w1": {
                    "drafts": [],
                    "time": 1,
                    "status": "live",
                    "browser": "b1",
                    "sync": {
                        "Remote": {
                            "desired": 0,
                            "lastReq": 0,
                            "lastAck": 0,
                        }
                    }
                },
                "w2": {
                    "drafts": [],
                    "time": 1,
                    "status": "live",
                    "browser": "b1",
                    "sync": {
                        "Remote": {
                            "desired": 0,
                            "lastReq": 0,
                            "lastAck": 0,
                        }
                    }
                },
            },
        })
    }

    const fn state4() -> &'static str {
        r#"
/\ tabs = ( t1 :> [drafts |-> {}, worker |-> w2, status |-> "loading", awaiting |-> {}] @@
  t2 :> [worker |-> w1, status |-> "clean"] )
"#
    }

    fn expected4() -> JsonValue {
        json!({
            "tabs": {
                "t1": {
                    "drafts": [],
                    "worker": "w2",
                    "status": "loading",
                    "awaiting": []
                },
                "t2": {
                    "worker": "w1",
                    "status": "clean"
                }
            },
        })
    }

    const fn state5() -> &'static str {
        r#"
/\ network = << [ drafts |-> {},
     type |-> "sync:T->W",
     from |-> t2,
     to |-> w1,
     newEdit |-> [isEmpty |-> FALSE, get |-> (w1 :> 0 @@ w2 :> 0)] ] >>
/\ tabs = ( t1 :>
      [ worker |-> w2,
        status |-> "dirty",
        draft |-> [isEmpty |-> TRUE],
        localChange |-> TRUE ] @@
  t2 :>
      [ worker |-> w1,
        status |-> "dirty",
        draft |-> [isEmpty |-> TRUE],
        localChange |-> FALSE ] )
"#
    }

    fn expected5() -> JsonValue {
        json!({
            "network": [
                {
                    "drafts": [],
                    "type": "sync:T->W",
                    "from": "t2",
                    "to": "w1",
                    "newEdit": {
                        "isEmpty": false,
                        "get": {
                            "w1": 0,
                            "w2": 0
                        }
                    },
                }
            ],
            "tabs": {
                "t1": {
                    "worker": "w2",
                    "status": "dirty",
                    "draft": {
                        "isEmpty": true,
                    },
                    "localChange": true,
                },
                "t2": {
                    "worker": "w1",
                    "status": "dirty",
                    "draft": {
                        "isEmpty": true,
                    },
                    "localChange": false,
                }
            },
        })
    }
}
