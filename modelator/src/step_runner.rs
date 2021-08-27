use crate::artifact::JsonTrace;
use crate::{Error, TestError};
use serde::de::DeserializeOwned;
use std::fmt::Debug;

/// A `StepRunner` drives a SUT by executing a series of steps
/// (see [crate::run_tla_steps]).
pub trait StepRunner<Step: DeserializeOwned + Debug + Clone> {
    /// Executes the first step against  the runner.
    fn initial_step(&mut self, step: Step) -> Result<(), String>;

    /// Executes each next step against the runner.
    fn next_step(&mut self, step: Step) -> Result<(), String>;

    /// Run this runner on a Json trace
    fn run(&mut self, trace: JsonTrace) -> Result<(), TestError> {
        // parse test
        let steps = trace
            .into_iter()
            .map(|step| {
                serde_json::from_value(step)
                    .map_err(|e| TestError::Modelator(Error::JsonParseError(e.to_string())))
            })
            .collect::<Result<Vec<Step>, _>>()?;

        for (i, step) in steps.clone().into_iter().enumerate() {
            // check each step
            let result = if i == 0 {
                self.initial_step(step)
            } else {
                self.next_step(step)
            };

            if let Err(message) = result {
                return Err(TestError::FailedTest {
                    message,
                    location: "".to_string(),
                    test: format!("{:?}", steps),
                    system: "".to_string(),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::NumberSystem;
    use serde::Deserialize;

    #[derive(Debug, Clone, Deserialize)]
    #[serde(rename_all = "camelCase")]
    struct NumbersStep {
        a: u64,
        b: u64,
        action: Action,
        action_outcome: String,
    }

    #[derive(Debug, Clone, Deserialize)]
    enum Action {
        None,
        IncreaseA,
        IncreaseB,
    }

    impl StepRunner<NumbersStep> for NumberSystem {
        fn initial_step(&mut self, step: NumbersStep) -> Result<(), String> {
            self.a = step.a;
            self.b = step.b;
            Ok(())
        }

        fn next_step(&mut self, step: NumbersStep) -> Result<(), String> {
            // Execute the action, and check the outcome
            let res = match step.action {
                Action::None => Ok(()),
                Action::IncreaseA => self.increase_a(1),
                Action::IncreaseB => self.increase_b(2),
            };
            let outcome = match res {
                Ok(()) => "OK".to_string(),
                Err(s) => s,
            };
            assert_eq!(outcome, step.action_outcome);

            // Check that the system state matches the state of the model
            assert_eq!(self.a, step.a);
            assert_eq!(self.b, step.b);

            Ok(())
        }
    }

    #[test]
    fn test_step_runner() {
        let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
        let tla_config_file = "tests/integration/tla/Numbers.cfg";
        let runtime = crate::ModelatorRuntime::default();
        let mut runner = NumberSystem::default();
        assert!(runtime
            .run_tla_steps(tla_tests_file, tla_config_file, &mut runner)
            .is_ok());
    }
}
