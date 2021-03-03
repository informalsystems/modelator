use crate::{JsonTrace, TestError};
use serde::de::DeserializeOwned;
use std::fmt::Debug;

pub trait TestRunner<S> {
    fn initial_step(&mut self, step: S) -> bool;
    fn next_step(&mut self, step: S) -> bool;
}

pub(crate) fn run<Runner, Step>(
    trace: JsonTrace,
    mut runner: Runner,
) -> Result<(), TestError<Runner, Step>>
where
    Runner: TestRunner<Step> + Debug,
    Step: DeserializeOwned + Debug + Clone,
{
    // parse test
    let steps = trace
        .into_iter()
        .map(|step| serde_json::from_value(step).map_err(TestError::Deserialize))
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
                runner,
            });
        }
    }
    Ok(())
}
