// We follow the approach proposed in the following link for integration tests:
// https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html

use modelator::artifact::{JsonTrace, TlaFile};
use modelator::{CliOptions, CliStatus, Error, ModelChecker, ModelCheckerOptions, Options};
use once_cell::sync::Lazy;
use serde_json::{json, Value as JsonValue};
use std::path::{Path, PathBuf};
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

    // create all tests
    let tests = vec![numbers_a_max_b_min_test(), numbers_a_min_b_max_test()];

    for (tla_tests_file, tla_config_file, expected) in tests {
        for (tla_tests_file, tla_config_file) in
            absolute_and_relative_paths(tla_tests_file, tla_config_file)
        {
            // generate traces using Rust API
            let mut traces = modelator::traces(&tla_tests_file, &tla_config_file, &options)?;
            // extract single trace
            assert_eq!(traces.len(), 1, "a single trace should have been generated");
            let trace = traces.pop().unwrap();
            assert_eq!(trace, expected);

            // TODO: disabling these tests for now, as they do not integrate well
            // with running model checkers in a temporary directory
            // See https://github.com/informalsystems/modelator/issues/47
            //
            // // generate traces using CLI
            // let mut traces = cli_traces(&tla_tests_file, &tla_config_file, &options)?;
            // // extract single trace
            // assert_eq!(traces.len(), 1, "a single trace should have been generated");
            // let trace = traces.pop().unwrap();
            // assert_eq!(trace, expected);

            // // parse file if apalache and simply assert it works
            // if model_checker == ModelChecker::Apalache {
            //     use std::convert::TryFrom;
            //     let tla_tests_file = TlaFile::try_from(tla_tests_file).unwrap();
            //     let tla_parsed_file =
            //         modelator::module::Apalache::parse(tla_tests_file, &options).unwrap();
            //     std::fs::remove_file(tla_parsed_file.path()).unwrap();
            // }
        }
    }
    Ok(())
}

fn cli_traces<P: AsRef<Path>>(
    tla_tests_file: P,
    tla_config_file: P,
    options: &Options,
) -> Result<Vec<JsonTrace>, Error> {
    use clap::Clap;
    // run CLI to generate tests
    let cli_output = CliOptions::parse_from(&[
        "modelator",
        "tla",
        "generate-tests",
        &tla_tests_file.as_ref().to_string_lossy().to_string(),
        &tla_config_file.as_ref().to_string_lossy().to_string(),
    ])
    .run();
    assert_eq!(cli_output.status, CliStatus::Success);
    let tests = cli_output
        .result
        .as_array()
        .unwrap()
        .into_iter()
        .map(|json_entry| {
            let test = json_entry.as_object().unwrap();
            (
                test.get("tla_file").unwrap().as_str().unwrap(),
                test.get("tla_config_file").unwrap().as_str().unwrap(),
            )
        })
        .collect::<Vec<_>>();

    // run CLI to run the model checker configured on each tla test
    let traces = tests
        .clone()
        .into_iter()
        .map(|(tla_file, tla_config_file)| {
            let module = match options.model_checker_options.model_checker {
                ModelChecker::Tlc => "tlc",
                ModelChecker::Apalache => "apalache",
            };
            CliOptions::parse_from(&["modelator", module, "test", tla_file, tla_config_file]).run()
        })
        .map(|cli_output| {
            assert_eq!(cli_output.status, CliStatus::Success);
            cli_output
                .result
                .as_object()
                .unwrap()
                .get("tla_trace_file")
                .unwrap()
                .as_str()
                .unwrap()
                .to_owned()
        })
        .collect::<Vec<_>>();

    // cleanup test files created
    for (tla_file, tla_config_file) in tests {
        std::fs::remove_file(tla_file).unwrap();
        std::fs::remove_file(tla_config_file).unwrap();
    }

    // run CLI to convert each tla trace to json
    let traces = traces
        .into_iter()
        .map(|tla_trace_file| {
            CliOptions::parse_from(&[
                "modelator",
                "tla",
                "tla-trace-to-json-trace",
                &tla_trace_file,
            ])
            .run()
        })
        .map(|cli_output| {
            assert_eq!(cli_output.status, CliStatus::Success);
            cli_output
                .result
                .as_object()
                .unwrap()
                .get("json_trace_file")
                .unwrap()
                .as_str()
                .unwrap()
                .to_owned()
        })
        .map(|json_trace_file| {
            let json_trace = std::fs::read_to_string(json_trace_file).unwrap();
            serde_json::from_str::<Vec<JsonValue>>(&json_trace)
                .unwrap()
                .into()
        })
        .collect::<Vec<_>>();
    Ok(traces)
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
        (
            relative_tla_tests_file.clone(),
            relative_tla_config_file.clone(),
        ),
        (
            absolute_tla_tests_file.clone(),
            absolute_tla_config_file.clone(),
        ),
    ]
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
