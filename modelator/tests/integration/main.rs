// We follow the approach proposed in the following link for integration tests:
// https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html

use modelator::artifact::JsonTrace;
use modelator::{Error, Options};
use modelator::{ModelChecker, ModelCheckerOptions};
use once_cell::sync::Lazy;
use serde_json::json;
use std::path::Path;
use std::sync::Mutex;

const TLA_DIR: &'static str = "tests/integration/tla";

// we use this lock to make sure that the tlc & apalache tests are not run in
// parallel
static LOCK: Lazy<Mutex<()>> = Lazy::new(Mutex::default);

#[test]
fn tlc() {
    let _guard = LOCK.lock();
    if let Err(e) = all_tests(ModelChecker::Tlc) {
        panic!("{}", e);
    }
}

#[test]
fn apalache() {
    let _guard = LOCK.lock();
    if let Err(e) = all_tests(ModelChecker::Apalache) {
        panic!("{}", e);
    }
}

fn all_tests(model_checker: ModelChecker) -> Result<(), Error> {
    // create modelator options
    let model_checker_options = ModelCheckerOptions::default().model_checker(model_checker);
    let options = Options::default().model_checker_options(model_checker_options);

    // compute path to tla dir
    let tla_dir = Path::new(TLA_DIR);

    // create all tests
    let tests = vec![numbers_a_max_b_min_test(), numbers_a_min_b_max_test()];

    for (tla_tests_file, tla_config_file, expected) in tests {
        // generate traces
        let mut traces = modelator::traces(
            tla_dir.join(tla_tests_file),
            tla_dir.join(tla_config_file),
            options.clone(),
        )?;

        // extract single trace
        assert_eq!(traces.len(), 1, "a single trace should have been generated");
        let trace = traces.pop().unwrap();

        assert_eq!(trace, expected);
    }

    Ok(())
}

fn numbers_a_max_b_min_test() -> (&'static str, &'static str, JsonTrace) {
    let tla_tests_file = "NumbersAMaxBMinTest.tla";
    let tla_config_file = "Numbers.cfg";
    let expected: Vec<_> = (0..=10)
        .map(|a| {
            json!({
                "a": a,
                "b": 0,
            })
        })
        .collect();
    (tla_tests_file, tla_config_file, expected.into())
}

fn numbers_a_min_b_max_test() -> (&'static str, &'static str, JsonTrace) {
    let tla_tests_file = "NumbersAMinBMaxTest.tla";
    let tla_config_file = "Numbers.cfg";
    let expected: Vec<_> = (0..=10)
        .step_by(2)
        .map(|b| {
            json!({
                "a": 0,
                "b": b,
            })
        })
        .collect();
    (tla_tests_file, tla_config_file, expected.into())
}
