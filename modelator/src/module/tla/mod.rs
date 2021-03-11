/// Conversion from TLA traces to JSON.
mod json;

use crate::artifact::{JsonTrace, TlaTrace};

// #[modelator::module]
pub struct Tla;

impl Tla {
    // #[modelator::method]
    pub fn tla_trace_to_json_trace(tla_trace: TlaTrace) -> Result<JsonTrace, crate::Error> {
        tracing::debug!("Tla::tla_trace_to_json_trace:\n{:#?}", tla_trace);
        let states = tla_trace
            .into_iter()
            .map(|state| json::state_to_json(&state))
            .collect::<Result<_, _>>()?;
        Ok(JsonTrace { states })
    }
}
