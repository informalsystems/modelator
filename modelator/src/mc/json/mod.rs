// Parser for TLA+ state.
mod parser;

use crate::Error;
use serde_json::Value as JsonValue;

pub fn state_to_json(input: &str) -> Result<JsonValue, Error> {
    parser::parse_state(input)
        .map(|(input, value)| {
            assert!(
                input.is_empty(),
                "[modelator] full TLA state should have been parsed"
            );
            value
        })
        .map_err(|err| Error::Nom(err.to_string()))
}
