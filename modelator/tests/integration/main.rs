// We follow the approach proposed in the following link for integration tests:
// https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html

use modelator::artifact::JsonTrace;
use modelator::{Error, Options};
use serde_json::json;
use std::path::Path;

const TLA_DIR: &'static str = "tests/integration/tla";

#[test]
fn tlc() {
    let options = Options::default();
    if let Err(e) = all_tests(options) {
        panic!("{}", e);
    }
}

fn all_tests(options: Options) -> Result<(), Error> {
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
