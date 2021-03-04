use nom::branch::alt;
use nom::bytes::complete::{is_a, tag, take_while};
use nom::character::complete::{char, digit1, multispace0, satisfy};
use nom::combinator::{cut, value};
use nom::multi::{many0, many1, separated_list0, separated_list1};
use nom::sequence::{preceded, separated_pair, terminated};
use nom::IResult;
use serde_json::Value as JsonValue;

pub(crate) fn parse_state(input: &str) -> IResult<&str, JsonValue> {
    many0(parse_var)(input).map(|(input, value)| {
        let vars = value.into_iter().collect();
        (input, JsonValue::Object(vars))
    })
}

fn parse_var(input: &str) -> IResult<&str, (String, JsonValue)> {
    preceded(
        space,
        terminated(
            preceded(
                tag("/\\"),
                separated_pair(
                    preceded(space, parse_identifier),
                    preceded(space, char('=')),
                    preceded(space, parse_any_value),
                ),
            ),
            space,
        ),
    )(input)
    .map(|(input, (var, value))| (input, (var.into_iter().collect(), value)))
}

fn space(input: &str) -> IResult<&str, &str> {
    multispace0(input)
}

fn parse_identifier(input: &str) -> IResult<&str, Vec<char>> {
    // TODO: what else can TLA var idenfitiers have?
    many1(satisfy(|c| c.is_alphanumeric() || "_-".contains(c)))(input)
}

fn parse_any_value(input: &str) -> IResult<&str, JsonValue> {
    preceded(
        space,
        alt((
            parse_bool,
            parse_number,
            parse_string,
            parse_set,
            parse_record,
            parse_function,
        )),
    )(input)
}

fn parse_bool(input: &str) -> IResult<&str, JsonValue> {
    let parse_true = value(JsonValue::Bool(true), tag("TRUE"));
    let parse_false = value(JsonValue::Bool(false), tag("FALSE"));
    alt((parse_true, parse_false))(input)
}

fn parse_number(input: &str) -> IResult<&str, JsonValue> {
    alt((parse_pos_number, parse_neg_number))(input)
}

fn parse_pos_number(input: &str) -> IResult<&str, JsonValue> {
    digit1(input).map(|(input, value)| {
        let value: u64 = value
            .parse()
            .expect("u64 parsed by nom should be a valid u64");
        (input, JsonValue::Number(value.into()))
    })
}

fn parse_neg_number(input: &str) -> IResult<&str, JsonValue> {
    preceded(is_a("-"), digit1)(input).map(|(input, value)| {
        let value: i64 = format!("-{}", value)
            .parse()
            .expect("i64 parsed by nom should be a valid i64");
        (input, JsonValue::Number(value.into()))
    })
}

fn parse_string(input: &str) -> IResult<&str, JsonValue> {
    // we support any string that doesn't escape with '\"'
    preceded(
        char('\"'),
        cut(terminated(take_while(|c| c != '\"'), char('\"'))),
    )(input)
    .map(|(input, value)| {
        let value = JsonValue::String(value.to_owned());
        (input, value)
    })
}

fn parse_set(input: &str) -> IResult<&str, JsonValue> {
    preceded(
        char('{'),
        cut(terminated(
            separated_list0(preceded(space, char(',')), parse_any_value),
            preceded(space, char('}')),
        )),
    )(input)
    .map(|(input, value)| {
        let value = JsonValue::Array(value);
        (input, value)
    })
}

fn parse_record(input: &str) -> IResult<&str, JsonValue> {
    preceded(
        char('('),
        cut(terminated(
            separated_list1(preceded(space, tag("@@")), parse_record_entry),
            preceded(space, char(')')),
        )),
    )(input)
    .map(|(input, vars)| {
        let vars = vars.into_iter().collect();
        let value = JsonValue::Object(vars);
        (input, value)
    })
}

fn parse_record_entry(input: &str) -> IResult<&str, (String, JsonValue)> {
    preceded(
        space,
        separated_pair(
            preceded(space, parse_identifier),
            preceded(space, tag(":>")),
            preceded(space, parse_any_value),
        ),
    )(input)
    .map(|(input, (var, value))| (input, (var.into_iter().collect(), value)))
}

fn parse_function(input: &str) -> IResult<&str, JsonValue> {
    preceded(
        char('['),
        cut(terminated(
            separated_list1(preceded(space, char(',')), parse_function_entry),
            preceded(space, char(']')),
        )),
    )(input)
    .map(|(input, vars)| {
        let vars = vars.into_iter().collect();
        let value = JsonValue::Object(vars);
        (input, value)
    })
}

fn parse_function_entry(input: &str) -> IResult<&str, (String, JsonValue)> {
    preceded(
        space,
        separated_pair(
            preceded(space, parse_identifier),
            preceded(space, tag("|->")),
            preceded(space, parse_any_value),
        ),
    )(input)
    .map(|(input, (var, value))| (input, (var.into_iter().collect(), value)))
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
            (booleans_and_numbers_state(), booleans_and_numbers_expected()),
            (sets_state(), sets_expected()),
            (records_state(), records_expected()),
            (functions_state(), functions_expected()),
            // (state1(), expected1()),
            // (state2(), expected2()),
            // (state3(), expected3()),
            // (state4(), expected4()),
            // (state5(), expected5()),
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

    fn booleans_and_numbers_state() -> &'static str {
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

    fn sets_state() -> &'static str {
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

    fn records_state() -> &'static str {
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

    fn functions_state() -> &'static str {
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

    /// The tests that follow are translated from some of the tests in https://github.com/japgolly/tla2json
    fn state1() -> &'static str {
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

    fn state2() -> &'static str {
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
                    "status": {
                        "drafts": [],
                        "worker": "w1",
                        "status": "loading",
                        "awaiting": [
                            "Remote"
                        ]
                    }
                }
            },
            "workers": {
                "w1": {
                    "status": {
                        "drafts": [],
                        "time": 1,
                        "status": "live",
                        "browser": "b1",
                        "awaiting": {
                            "Remote": {
                                "desired": 0,
                                "lastReq": 0,
                                "lastAck": 0,
                            }
                        }
                    }
                },
                "w2": {
                    "status": "-"
                }
            },
        })
    }

    fn state3() -> &'static str {
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
                    "awaiting": {
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
                    "awaiting": {
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

    fn state4() -> &'static str {
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

    fn state5() -> &'static str {
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
            "network": {
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
            },
            "tabs": {
                "t1": {
                    "worker": "w2",
                    "status": "loading",
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
