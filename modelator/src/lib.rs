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

/// Modelator's options.
mod options;

/// Modelator's error type.
mod error;

/// List of artifacts.
pub mod artifact;

/// List of modules.
pub mod module;

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

/// Testing utilities
pub mod test_util;

/// Re-exports.
pub use cli::{output::CliOutput, output::CliStatus, CliOptions};
pub use datachef::Recipe;
pub use error::{Error, TestError};
pub use event::{ActionHandler, Event, EventRunner, EventStream, StateHandler};
pub use options::{ModelChecker, ModelCheckerOptions, ModelCheckerWorkers, Options};
use serde::de::DeserializeOwned;
pub use step_runner::StepRunner;

use std::env;
use std::fmt::Debug;
use std::path::Path;
use tempfile::tempdir;

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
/// let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
/// let tla_config_file = "tests/integration/tla/Numbers.cfg";
/// let options = modelator::Options::default();
/// let traces = modelator::traces(tla_tests_file, tla_config_file, &options).unwrap();
/// println!("{:?}", traces);
/// ```
pub fn traces<P: AsRef<Path>>(
    tla_tests_file: P,
    tla_config_file: P,
    options: &Options,
) -> Result<Vec<artifact::JsonTrace>, Error> {
    // setup modelator
    setup(&options)?;

    // create a temporary directory, and copy TLA+ files there
    let dir = tempdir().map_err(Error::io)?;
    let tla_tests_file = util::copy_files_into("tla", tla_tests_file, dir.path())?;
    let tla_config_file = util::copy_files_into("cfg", tla_config_file, dir.path())?;

    // save the current, and change to the temporary directory
    let current_dir = env::current_dir().map_err(Error::io)?;
    env::set_current_dir(dir.path()).map_err(Error::io)?;

    // generate tla tests
    use std::convert::TryFrom;
    let tla_tests_file = artifact::TlaFile::try_from(tla_tests_file)?;
    let tla_config_file = artifact::TlaConfigFile::try_from(tla_config_file)?;
    let tests = module::Tla::generate_tests(tla_tests_file, tla_config_file)?;

    // run the model checker configured on each tla test
    let traces = tests
        .into_iter()
        .map(
            |(tla_file, tla_config_file)| match options.model_checker_options.model_checker {
                ModelChecker::Tlc => module::Tlc::test(tla_file, tla_config_file, options),
                ModelChecker::Apalache => {
                    module::Apalache::test(tla_file, tla_config_file, options)
                }
            },
        )
        .collect::<Result<Vec<_>, _>>()?;

    // cleanup everything by removing the temporary directory
    dir.close().map_err(Error::io)?;
    // restore the current directory
    env::set_current_dir(current_dir).map_err(Error::io)?;

    // convert each tla trace to json
    traces
        .into_iter()
        .map(module::Tla::tla_trace_to_json_trace)
        .collect()
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
/// # Example
///
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
/// fn main() {
///     let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
///     let tla_config_file = "tests/integration/tla/Numbers.cfg";
///     let options = modelator::Options::default();
///     let mut system = NumberSystem::default();
///     assert!(run_tla_steps(tla_tests_file, tla_config_file, &options, &mut system).is_ok());
/// }
/// ```
// #[allow(clippy::needless_doctest_main)]
pub fn run_tla_steps<P, System, Step>(
    tla_tests_file: P,
    tla_config_file: P,
    options: &Options,
    system: &mut System,
) -> Result<(), TestError>
where
    P: AsRef<Path>,
    System: StepRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let traces = traces(tla_tests_file, tla_config_file, options).map_err(TestError::Modelator)?;
    for trace in traces {
        system.run(trace)?;
    }
    Ok(())
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
///     let tla_tests_file = "tests/integration/tla/NumbersAMaxBMaxTest.tla";
///     let tla_config_file = "tests/integration/tla/Numbers.cfg";
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
///     let result = run_tla_events(tla_tests_file, tla_config_file, &options, &mut system, &mut runner);
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
    tla_tests_file: P,
    tla_config_file: P,
    options: &Options,
    system: &mut System,
    runner: &mut event::EventRunner<System>,
) -> Result<(), TestError>
where
    P: AsRef<Path>,
    System: Debug + Default,
{
    let traces = traces(tla_tests_file, tla_config_file, options).map_err(TestError::Modelator)?;
    for trace in traces {
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
            })?;
    }
    Ok(())
}

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
        std::fs::create_dir_all(&options.dir).map_err(Error::io)?;
    }

    // download missing jars
    jar::download_jars(&options.dir)?;
    tracing::trace!("modelator setup completed");

    Ok(())
}
