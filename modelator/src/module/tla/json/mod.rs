// Parser for TLA+ state.
mod parser;

use crate::Error;
use serde_json::Value as JsonValue;

pub(crate) fn state_to_json(state: &str) -> Result<JsonValue, Error> {
    parser::parse_state(state)
        .map(|(input, value)| {
            assert!(
                input.is_empty(),
                "[modelator] full TLA state should have been parsed"
            );
            value
        })
        .map_err(Error::nom)
}
