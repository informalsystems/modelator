use crate::artifact::JsonTrace;
use crate::{Error, TestError};
use serde::de::DeserializeOwned;
use std::fmt::Debug;

/// A `TestRunner` drives a test by executing a series of steps
/// (see [crate::run]).
pub trait TestRunner<S> {
    /// Executes the first step against  the runner.
    fn initial_step(&mut self, step: S) -> bool;

    /// Executes each next step against the runner.
    fn next_step(&mut self, step: S) -> bool;
}

pub(crate) fn run<Runner, Step>(trace: JsonTrace, mut runner: Runner) -> Result<(), TestError<Step>>
where
    Runner: TestRunner<Step> + Debug,
    Step: DeserializeOwned + Debug + Clone,
{
    // parse test
    let steps = trace
        .into_iter()
        .map(|step| {
            serde_json::from_value(step)
                .map_err(|e| TestError::Modelator(Error::JsonParseError(e.to_string())))
        })
        .collect::<Result<Vec<Step>, _>>()?;
    let step_count = steps.len();

    for (i, step) in steps.clone().into_iter().enumerate() {
        // check each step
        let ok = if i == 0 {
            runner.initial_step(step)
        } else {
            runner.next_step(step)
        };

        if !ok {
            return Err(TestError::FailedTest {
                step_index: i + 1,
                step_count,
                steps,
            });
        }
    }
    Ok(())
}
