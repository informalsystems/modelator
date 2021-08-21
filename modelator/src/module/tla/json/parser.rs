use nom::bytes::complete::take_while;
use nom::character::complete::{digit1, multispace0, satisfy};
use nom::{
    alt, call, char, complete, many1, map, named, opt, preceded, return_error, separated_list0,
    separated_list1, separated_pair, tag, terminated, value,
};

use serde_json::Value as JsonValue;

named!(
    pub(crate) parse_state<&str, JsonValue>,
    map!(
        preceded!(
            space,
            preceded!(opt!(tag!("/\\")), separated_list0!(complete!(tag!("/\\")), parse_var))
        ),
        |value| JsonValue::Object(value.into_iter().collect())
    )
);

named!(
    parse_var<&str, (String, JsonValue)>,
    preceded!(
        space,
        terminated!(
            separated_pair!(
                preceded!(space, parse_identifier),
                preceded!(space, char!('=')),
                preceded!(space, parse_any_value)
            ),
            space
        )
    )
);

named!(
    space<&str, &str>,
    call!(multispace0)
);

// TODO: what else can TLA var idenfitiers have?
named!(
    parse_identifier<&str, String>,
    map!(
        many1!(call!(satisfy(|c| c.is_alphanumeric() || "_-".contains(c)))),
        |value| value.into_iter().collect()
    )
);

named!(
    parse_identifiers_as_values<&str, JsonValue>,
    map!(
        parse_identifier,
        |value| JsonValue::String(value)
    )
);

named!(
    parse_any_value<&str, JsonValue>,
    preceded!(
        space,
        alt!(
            parse_bool
            | parse_number
            | parse_string
            | parse_identifiers_as_values
            | parse_set
            | parse_sequence
            | parse_record
            | parse_function
        )
    )
);

named!(
    parse_bool<&str, JsonValue>,
    map!(
        alt!(value!(true, tag!("TRUE")) | value!(false, tag!("FALSE"))),
        |value| JsonValue::Bool(value)
    )
);

named!(
    parse_number<&str, JsonValue>,
    alt!(parse_pos_number | parse_neg_number)
);

named!(
    parse_pos_number<&str, JsonValue>,
    map!(
        call!(digit1),
        |value| JsonValue::Number(value
            .parse::<u64>()
            .expect("u64 parsed by nom should be a valid u64")
            .into()
        )
    )
);

named!(
    parse_neg_number<&str, JsonValue>,
    map!(
        preceded!(char!('-'), call!(digit1)),
        |value| JsonValue::Number(format!("-{}", value)
            .parse::<i64>()
            .expect("i64 parsed by nom should be a valid i64")
            .into()
        )
    )
);

// following comment is for future:
// old nom code used `cut(terminated(...))`
// equivalent nom macro calls is used, `return_error!(terminated!(...))`
// used in: parse_string, parse_set, parse_sequence, parse_record, parse_function

named!(
    parse_string<&str, JsonValue>,
    map!(
        preceded!(
            char!('"'),
            return_error!(terminated!(
                call!(take_while(|c| c != '\"')),
                char!('"')
            ))
        ),
        |value| JsonValue::String(value.into())
    )
);

named!(
    parse_set<&str, JsonValue>,
    map!(
        preceded!(
            char!('{'),
            return_error!(terminated!(
                separated_list0!(
                    preceded!(space, char!(',')),
                    parse_any_value
                ),
                preceded!(space, char!('}'))
            ))
        ),
        |value| JsonValue::Array(value)
    )
);

named!(
    parse_sequence<&str, JsonValue>,
    map!(
        preceded!(
            tag!("<<"),
            return_error!(terminated!(
                separated_list0!(
                    preceded!(space, char!(',')),
                    parse_any_value
                ),
                preceded!(space, tag!(">>"))
            ))
        ),
        |value| JsonValue::Array(value)
    )
);

named!(
    parse_function<&str, JsonValue>,
    map!(
        preceded!(
            char!('('),
            return_error!(terminated!(
                separated_list1!(
                    preceded!(space, tag!("@@")),
                    parse_function_entry
                ),
                preceded!(space, char!(')'))
            ))
        ),
        |value| JsonValue::Object(value.into_iter().collect())
    )
);

named!(
    parse_function_entry<&str, (String, JsonValue)>,
    preceded!(
        space,
        separated_pair!(
            preceded!(space, parse_identifier),
            preceded!(space, tag!(":>")),
            preceded!(space, parse_any_value)
        )
    )
);

named!(
    parse_record<&str, JsonValue>,
    map!(
        preceded!(
            char!('['),
            return_error!(terminated!(
                separated_list1!(
                    preceded!(space, char!(',')),
                    parse_record_entry
                ),
                preceded!(space, char!(']'))
            ))
        ),
        |value| JsonValue::Object(value.into_iter().collect())
    )
);

named!(
    parse_record_entry<&str, (String, JsonValue)>,
    preceded!(
        space,
        separated_pair!(
            preceded!(space, parse_identifier),
            preceded!(space, tag!("|->")),
            preceded!(space, parse_any_value)
        )
    )
);

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

    fn booleans_and_numbers_state_without_first_logical_and() -> &'static str {
        r#"
            empty_set = {} /\ set = {1, 2, 3} /\ pos_number = 1 /\ neg_number = -1 /\ bool = TRUE
        "#
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

    fn sequences_state() -> &'static str {
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
