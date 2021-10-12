use modelator::test_util::NumberSystem;

use modelator::TestReport;
use serde::Deserialize;
use std::path::Path;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
struct NumbersStep {
    a: u64,
    b: u64,
    action: Action,
    action_outcome: String,
}

// We also define the abstract actions: do nothing / increase a / increase b.
#[derive(Debug, Clone, Deserialize)]
enum Action {
    None,
    IncreaseA,
    IncreaseB,
}

impl modelator::step_runner::StepRunner<NumbersStep> for NumberSystem {
    fn initial_step(&mut self, step: NumbersStep) -> Result<(), String> {
        self.a = step.a;
        self.b = step.b;
        self.recalculate();
        Ok(())
    }

    // how to handle all subsequent steps
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

pub fn default<P: AsRef<Path>>(
    tla_tests_file_path: P,
    tla_config_file_path: P,
) -> Result<TestReport, modelator::Error> {
    let runtime = modelator::ModelatorRuntime::default();
    let mut system = NumberSystem::default();
    runtime.run_tla_steps(tla_tests_file_path, tla_config_file_path, &mut system)
}
