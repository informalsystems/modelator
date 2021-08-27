//! `modelator` is a framework for model-based testing.
#![warn(
    unreachable_pub,
    missing_docs,
    missing_copy_implementations,
    trivial_numeric_casts,
    unused_extern_crates,
    rust_2018_idioms
)]
// It makes sense to allow those when the development is active
#![allow(unused_imports, dead_code)]

/// Modelator's error type.
mod error;

/// List of artifacts.
pub mod artifact;

/// List of checkers.
pub mod checker;

/// Caching of model-checker outputs.
mod cache;

/// Jar utilities.
mod jar;

/// Command-line interface.
mod cli;

/// Datastructure converter.
/// Allows to define conversion rules to make (cook)
/// concrete data-structures from the abstract ones for testing purposes.
pub mod datachef;

/// Utilitary functions.
mod util;

/// Provides the way to run sets of test functions on several kinds of test inputs.
pub mod tester;

/// A framework for event-based testing of message-passing systems
/// with possibly partitioned system state.
pub mod event;

/// A runner for steps obtained from Json traces
pub mod step_runner;

/// TLA+ module.
pub mod tla;

/// Testing utilities
pub mod test_util;

use artifact::model_checker_stdout::ModelCheckerStdout;
use artifact::TlaFileSuite;
use checker::{Options, ModelChecker};
/// Re-exports.
pub use cli::{output::CliOutput, output::CliStatus, CliOptions};
pub use datachef::Recipe;
pub use error::{Error, TestError};
pub use event::{ActionHandler, Event, EventRunner, EventStream, StateHandler};
use serde::de::DeserializeOwned;
pub use step_runner::StepRunner;

use crate::artifact::{Artifact, ArtifactCreator};

use std::env;
use std::fmt::Debug;
use std::path::Path;
use tempfile::tempdir;

pub(crate) fn setup(options: &Options) -> Result<(), Error> {
    // init tracing subscriber (in case it's not already)
    if let Err(e) = tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .try_init()
    {
        tracing::trace!(
            "modelator attempted to init the tracing_subscriber: {:?}",
            e
        );
    }

    // create modelator dir (if it doens't already exist)
    if !options.dir.as_path().is_dir() {
        std::fs::create_dir_all(&options.dir)?;
    }

    // download missing jars
    jar::download_jars(&options.dir)?;
    tracing::trace!("modelator setup completed");

    Ok(())
}

/// Given a [crate::artifact::TlaFile] with TLA+ test assertions,
/// as well as a [crate::artifact::TlaConfigFile] with TLA+ configuration,
/// generate all traces resulting from the test assertions.
///
/// The traces are generated by executing a model checker,
/// which can be selected via [crate::options::Options].
///
/// # Examples
///
/// ```
/// let tla_tests_file_path = "tests/integration/tla/NumbersAMaxBMinTest.tla";
/// let tla_config_file_path = "tests/integration/tla/Numbers.cfg";
/// let options = modelator::Options::default();
/// let trace_results = modelator::traces(tla_tests_file_path, tla_config_file_path, &options).unwrap();
/// println!("{:?}", trace_results);
/// ```
pub fn traces<P: AsRef<Path>>(
    tla_tests_file_path: P,
    tla_config_file_path: P,
    options: &Options,
) -> Result<Vec<Result<artifact::JsonTrace, Error>>, Error> {
    // setup modelator
    setup(options)?;

    let file_suite =
        TlaFileSuite::from_tla_and_config_paths(tla_tests_file_path, tla_config_file_path)?;
    let tests = tla::Tla::generate_tests(&file_suite)?;

    #[allow(clippy::needless_collect)]
    // rust iterators are lazy
    // so we need to collect the traces in memory before deleting the work directory

    // run the model checker configured on each tla test
    let trace_results = tests
        .into_iter()
        .map(|(tla_file, tla_config_file)| {
            let test_file_suite = {
                let collected = {
                    let mut dependencies = file_suite.dependency_tla_files.clone();
                    dependencies.push(file_suite.tla_file.clone());
                    dependencies
                };
                TlaFileSuite {
                    tla_file,
                    tla_config_file,
                    dependency_tla_files: collected,
                }
            };
            match options.model_checker_options.model_checker {
                ModelChecker::Tlc => checker::Tlc::test(&test_file_suite, options),
                ModelChecker::Apalache => checker::Apalache::test(&test_file_suite, options),
            }
        })
        .collect::<Vec<_>>();

    // convert each tla trace to json
    Ok(trace_results
        .into_iter()
        .map(|res| res.and_then(|it| tla::Tla::tla_trace_to_json_trace(it.0)))
        .collect())
}

/// This is the most simple interface to run your system under test (SUT)
/// against traces obtained from TLA+ tests.
/// The function generates TLA+ traces using [`crate::traces`] and execute them against
/// the SUT that implements [`StepRunner`].
///
/// For more information, please consult the documentation of [`traces`] and
/// [`StepRunner`].
///
/// # Example
///
// #[allow(clippy::needless_doctest_main)]
/// ```
/// use modelator::{run_tla_steps, StepRunner};
/// use serde::Deserialize;
///
/// // Suppose your system under test (SUT) consists of two integer variables,
/// // where each number can be increased independently;
/// // SUT also maintains the sum and product of the numbers.
/// use modelator::test_util::NumberSystem;
///
/// // We define a structure that is capable to serialize the states of a TLA+ trace.
/// #[derive(Debug, Clone, Deserialize)]
/// #[serde(rename_all = "camelCase")]
/// struct NumbersStep {
///     a: u64,
///     b: u64,
///     action: Action,
///     action_outcome: String
/// }
///
/// // We also define the abstract actions: do nothing / increase a / increase b.
/// #[derive(Debug, Clone, Deserialize)]
/// enum Action {
///     None,
///     IncreaseA,
///     IncreaseB
/// }
///
/// // We implement `StepRunner` for our SUT
/// // This implementation needs to define only a couple of functions:
/// impl StepRunner<NumbersStep> for NumberSystem {
///     // how to handle the initial step (initialize your system)
///     fn initial_step(&mut self, step: NumbersStep) -> Result<(), String> {
///         self.a = step.a;
///         self.b = step.b;
///         Ok(())
///     }
///
///     // how to handle all subsequent steps
///     fn next_step(&mut self, step: NumbersStep) -> Result<(), String> {
///         // Execute the action, and check the outcome
///         let res = match step.action {
///             Action::None => Ok(()),
///             Action::IncreaseA => self.increase_a(1),
///             Action::IncreaseB => self.increase_b(2),
///         };
///         let outcome = match res {
///             Ok(()) => "OK".to_string(),
///             Err(s) => s,
///         };
///         assert_eq!(outcome, step.action_outcome);
///
///         // Check that the system state matches the state of the model
///         assert_eq!(self.a, step.a);
///         assert_eq!(self.b, step.b);
///
///         Ok(())
///     }
/// }
///
/// // To run your system against a TLA+ test, just point to the corresponding TLA+ files.
/// fn test() {
///     let tla_tests_file_path = "tests/integration/tla/NumbersAMaxBMinTest.tla";
///     let tla_config_file_path = "tests/integration/tla/Numbers.cfg";
///     let options = modelator::Options::default();
///     let mut system = NumberSystem::default();
///     assert!(run_tla_steps(tla_tests_file_path, tla_config_file_path, &options, &mut system).is_ok());
/// }
/// ```
pub fn run_tla_steps<P, System, Step>(
    tla_tests_file_path: P,
    tla_config_file_path: P,
    options: &Options,
    system: &mut System,
) -> Result<Vec<Result<(), TestError>>, Error>
where
    P: AsRef<Path>,
    System: StepRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let trace_results = traces(tla_tests_file_path, tla_config_file_path, options)?;
    Ok(trace_results
        .into_iter()
        .map(|trace_result| system.run(trace_result.map_err(TestError::Modelator)?))
        .collect())
}

/// Run the system under test (SUT) using the abstract events obtained
/// from TLA+ traces. Traces are generated using [`traces`],
/// To interpret abstract events an [EventRunner] needs to be created,
/// as well as [StateHandler] and [ActionHandler] to be implemented
/// for abstract states and actions you want to handle.
///
/// # Example
///
/// ```
/// use modelator::{run_tla_events, EventRunner, ActionHandler, StateHandler};
/// use serde::Deserialize;
///
/// // Suppose your system under test (SUT) consists of two integer variables,
/// // where each number can be increased independently;
/// // SUT also maintains the sum and product of the numbers.
/// use modelator::test_util::NumberSystem;
///
/// // In order to drive your SUT, we could define two abstract states,
/// // that contain the state of the variables `a` and `b`.
/// #[derive(Debug, Clone, Deserialize, PartialEq)]
/// struct A {
///     a: u64,
/// }
/// #[derive(Debug, Clone, Deserialize, PartialEq)]
/// struct B {
///     b: u64,
/// }
///
/// // We also define the abstract actions: do nothing / increase a / increase b.
/// #[derive(Debug, Clone, Deserialize)]
/// enum Action {
///     None,
///     IncreaseA,
///     IncreaseB
/// }
///
/// // We define StateHandlers that are able to initialize your SUT from
/// // these abstract states, as well as to read them at any point in time.
/// impl StateHandler<A> for NumberSystem {
///     fn init(&mut self, state: A) {
///         self.a = state.a
///     }
///     fn read(&self) -> A {
///         A { a: self.a }
///     }
/// }
/// impl StateHandler<B> for NumberSystem {
///     fn init(&mut self, state: B) {
///         self.b = state.b
///     }
///     fn read(&self) -> B {
///         B { b: self.b }
///     }
/// }
///
/// // We define also an action handler that processes abstract actions
/// impl ActionHandler<Action> for NumberSystem {
///     type Outcome = String;
///
///     fn handle(&mut self, action: Action) -> Self::Outcome {
///         let result_to_outcome = |res| match res {
///             Ok(()) => "OK".to_string(),
///             Err(s) => s
///         };
///         match action {
///             Action::None => "OK".to_string(),
///             Action::IncreaseA => result_to_outcome(self.increase_a(1)),
///             Action::IncreaseB => result_to_outcome(self.increase_b(2))
///         }
///     }
/// }
///
/// // To run your system against a TLA+ test, just point to the corresponding TLA+ files.
/// fn main() {
///     let tla_tests_file_path = "tests/integration/tla/NumbersAMaxBMaxTest.tla";
///     let tla_config_file_path = "tests/integration/tla/Numbers.cfg";
///     let options = modelator::Options::default();
///     
///     // We create a system under test
///     let mut system = NumberSystem::default();
///
///     // We construct a runner, and tell which which states and actions it should process.
///     let mut runner = EventRunner::new()
///         .with_state::<A>()
///         .with_state::<B>()
///         .with_action::<Action>();
///
///     // run your system against the events produced from TLA+ tests.
///     let result = run_tla_events(tla_tests_file_path, tla_config_file_path, &options, &mut system, &mut runner);
///     // At each step of a test, the state of your system is being checked
///     // against the state that the TLA+ model expects
///     assert!(result.is_ok());
///     // You can also check the final state of your system, if you want.
///     assert_eq!(system.a, 6);
///     assert_eq!(system.b, 6);
///     assert_eq!(system.sum, 12);
///     assert_eq!(system.prod, 36);
/// }
/// ```
// #[allow(clippy::needless_doctest_main)]
#[allow(clippy::needless_doctest_main)]
pub fn run_tla_events<P, System>(
    tla_tests_file_path: P,
    tla_config_file_path: P,
    options: &Options,
    system: &mut System,
    runner: &mut event::EventRunner<System>,
) -> Result<Vec<Result<(), TestError>>, Error>
where
    P: AsRef<Path>,
    System: Debug + Default,
{
    let trace_results = traces(tla_tests_file_path, tla_config_file_path, options)?;

    Ok(trace_results
        .into_iter()
        .map(|trace_result| {
            let trace = trace_result.map_err(TestError::Modelator)?;
            let events: EventStream = trace.clone().into();
            runner
                .run(system, &mut events.into_iter())
                .map_err(|op| match op {
                    TestError::UnhandledTest { system, .. } => TestError::UnhandledTest {
                        test: trace.to_string(),
                        system,
                    },
                    TestError::FailedTest {
                        message,
                        location,
                        system,
                        ..
                    } => TestError::FailedTest {
                        test: trace.to_string(),
                        message,
                        location,
                        system,
                    },
                    other => other,
                })
        })
        .collect())
}
