// We follow the approach proposed in the following link for integration tests:
// https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html

use modelator::artifact::JsonTrace;
use modelator::test_util::NumberSystem;
use modelator::{ActionHandler, EventRunner, EventStream, StateHandler};
use modelator::{CliOptions, CliStatus, Error, checker::{ModelChecker, ModelCheckerRuntime, ModelatorRuntime}};
use once_cell::sync::Lazy;
use serde::Deserialize;
use serde_json::Value as JsonValue;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

#[derive(Default, Debug, PartialEq)]
struct Numbers {
    a: i64,
    b: i64,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
struct A {
    a: u64,
}
#[derive(Debug, Clone, Deserialize, PartialEq)]
struct B {
    b: u64,
}

#[derive(Debug, Clone, Deserialize)]
enum Action {
    None,
    IncreaseA,
    IncreaseB,
}

impl StateHandler<A> for NumberSystem {
    fn init(&mut self, state: A) {
        self.a = state.a
    }
    fn read(&self) -> A {
        A { a: self.a }
    }
}
impl StateHandler<B> for NumberSystem {
    fn init(&mut self, state: B) {
        self.b = state.b
    }
    fn read(&self) -> B {
        B { b: self.b }
    }
}

impl ActionHandler<Action> for NumberSystem {
    type Outcome = String;

    fn handle(&mut self, action: Action) -> Self::Outcome {
        let result_to_outcome = |res| match res {
            Ok(()) => "OK".to_string(),
            Err(s) => s,
        };
        match action {
            Action::None => result_to_outcome(Ok(())),
            Action::IncreaseA => result_to_outcome(self.increase_a(1)),
            Action::IncreaseB => result_to_outcome(self.increase_b(2)),
        }
    }
}

#[test]
fn event_runner() {
    let events = EventStream::new()
        .init(A { a: 0 })
        .init(B { b: 0 })
        .action(Action::IncreaseA)
        .action(Action::IncreaseB)
        .check(|state: A| assert!(state.a == 1))
        .check(|state: B| assert!(state.b == 2));

    let mut system = NumberSystem::default();
    let mut runner = EventRunner::new()
        .with_state::<A>()
        .with_state::<B>()
        .with_action::<Action>();
    let result = runner.run(&mut system, &mut events.into_iter());
    println!("{:?}", result);
    assert!(result.is_ok());
}

// TODO: This test succeeds when run separately,
// and fails interchangeably with TLC test when run via `cargo test`
// Seems to be related to https://github.com/informalsystems/modelator/issues/43
//
// #[test]
// fn json_event_runner() {
//     let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
//     let tla_config_file = "tests/integration/tla/Numbers.cfg";
//     let options = modelator::Options::default();

//     let mut runner = Runner::<Numbers>::new()
//         .with_state::<A>()
//         .with_state::<B>()
//         .with_action::<String>();

//     assert!(run(tla_tests_file, tla_config_file, &options, &mut runner).is_ok());
// }

const TLA_DIR: &str = "tests/integration/tla";

// we use this lock to make sure that the tlc & apalache tests are not run in
// parallel
static LOCK: Lazy<Mutex<()>> = Lazy::new(Mutex::default);

// TODO: disabled because of non-deterministic test failures
// see https://github.com/informalsystems/modelator/issues/43
// #[test]
#[allow(dead_code)]
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
    let model_checker_runtime = ModelCheckerRuntime::default().model_checker(model_checker);
    let options = ModelatorRuntime::default().model_checker_runtime(model_checker_runtime);

    // create all tests
    let tests = vec![
        numbers_a_max_b_min_test(),
        numbers_a_min_b_max_test(),
        numbers_a_max_b_max_test(),
    ];

    for (tla_tests_file, tla_config_file, expected) in tests {
        for (tla_tests_file, tla_config_file) in
            absolute_and_relative_paths(tla_tests_file, tla_config_file)
        {
            let mut system = NumberSystem::default();
            let mut runner = EventRunner::new()
                .with_state::<A>()
                .with_state::<B>()
                .with_action::<Action>();

            // generate traces using Rust API
            let mut traces = modelator::traces(&tla_tests_file, &tla_config_file, &options)?;
            // extract single trace
            assert_eq!(traces.len(), 1, "a single trace should have been generated");
            let trace = traces.pop().unwrap()?;

            let result = runner.run(&mut system, &mut EventStream::from(trace).into_iter());
            assert!(result.is_ok());
            assert_eq!(system, expected);

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

#[allow(dead_code)]
fn cli_traces<P: AsRef<Path>>(
    tla_tests_file: P,
    tla_config_file: P,
    options: &ModelatorRuntime,
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
        .iter()
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
            let module = match options.model_checker_runtime.model_checker {
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
        (relative_tla_tests_file, relative_tla_config_file),
        (absolute_tla_tests_file, absolute_tla_config_file),
    ]
}

fn numbers_a_max_b_min_test() -> (&'static str, &'static str, NumberSystem) {
    let tla_tests_file = "NumbersAMaxBMinTest.tla";
    let tla_config_file = "Numbers.cfg";
    let expected = NumberSystem {
        a: 6,
        b: 0,
        sum: 6,
        prod: 0,
    };
    (tla_tests_file, tla_config_file, expected)
}

fn numbers_a_min_b_max_test() -> (&'static str, &'static str, NumberSystem) {
    let tla_tests_file = "NumbersAMinBMaxTest.tla";
    let tla_config_file = "Numbers.cfg";
    let expected = NumberSystem {
        a: 0,
        b: 6,
        sum: 6,
        prod: 0,
    };
    (tla_tests_file, tla_config_file, expected)
}

fn numbers_a_max_b_max_test() -> (&'static str, &'static str, NumberSystem) {
    let tla_tests_file = "NumbersAMaxBMaxTest.tla";
    let tla_config_file = "Numbers.cfg";
    let expected = NumberSystem {
        a: 6,
        b: 6,
        sum: 12,
        prod: 36,
    };
    (tla_tests_file, tla_config_file, expected)
}
