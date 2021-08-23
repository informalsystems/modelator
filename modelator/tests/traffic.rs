// We follow the approach proposed in the following link for integration tests:
// https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html

use modelator::{Error, ModelChecker, ModelCheckerOptions, Options};
use once_cell::sync::Lazy;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

// we use this lock to make sure that the tlc & apalache tests are not run in
// parallel
static LOCK: Lazy<Mutex<()>> = Lazy::new(Mutex::default);

const TLA_DIR: &str = "tests/integration/tla";

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

    // create all tests
    let tests = vec![traffic_test()];

    for (tla_tests_file, tla_config_file) in tests {
        for (tla_tests_file, tla_config_file) in
            absolute_and_relative_paths(tla_tests_file, tla_config_file)
        {
            // generate traces using Rust API
            let mut traces = modelator::traces(&tla_tests_file, &tla_config_file, &options)?;
            // extract single trace
            assert_eq!(traces.len(), 3, "expecting 3 traces to be generated");
            let trace = traces.pop().unwrap();
            println!("{}", trace);
        }
    }
    Ok(())
}

fn absolute_and_relative_paths(
    tla_tests_file: &'static str,
    tla_config_file: &'static str,
) -> Vec<(PathBuf, PathBuf)> {
    // compute path to tla dir
    let tla_dir = Path::new(TLA_DIR);
    let relative_tla_tests_file = tla_dir.join(tla_tests_file);
    let relative_tla_config_file = tla_dir.join(tla_config_file);
    let absolute_tla_tests_file = relative_tla_tests_file.canonicalize().unwrap();
    let absolute_tla_config_file = relative_tla_config_file.canonicalize().unwrap();
    vec![
        (relative_tla_tests_file, relative_tla_config_file),
        (absolute_tla_tests_file, absolute_tla_config_file),
    ]
}

fn traffic_test() -> (&'static str, &'static str) {
    let tla_tests_file = "TrafficCrossingTest.tla";
    let tla_config_file = "TrafficCrossing.cfg";
    (tla_tests_file, tla_config_file)
}
