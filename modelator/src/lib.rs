//! `modelator` is a framework for model-based testing.
#![warn(
    unreachable_pub,
    missing_docs,
    missing_copy_implementations,
    trivial_numeric_casts,
    unused_extern_crates,
    rust_2018_idioms
)]

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

/// Test runner.
pub mod runner;

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

/// Re-exports.
pub use cli::{output::CliOutput, output::CliStatus, CliOptions};
pub use datachef::Recipe;
pub use error::{Error, TestError};
pub use event::{ActionHandler, Event, EventStream, Runner, StateHandler};
pub use options::{ModelChecker, ModelCheckerOptions, ModelCheckerWorkers, Options};

use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::path::Path;

/// Generate TLA+ traces (encoded as JSON) given a [crate::artifact::TlaFile]
/// containing TLA+ assertions and a [crate::artifact::TlaConfigFile].
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

    // generate tla tests
    use std::convert::TryFrom;
    let tla_tests_file = artifact::TlaFile::try_from(tla_tests_file.as_ref())?;
    let tla_config_file = artifact::TlaConfigFile::try_from(tla_config_file.as_ref())?;
    let tests = module::Tla::generate_tests(tla_tests_file, tla_config_file)?;

    // run the model checker configured on each tla test
    let traces = tests
        .clone()
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

    // cleanup test files created
    for (tla_file, tla_config_file) in tests {
        std::fs::remove_file(tla_file.path()).map_err(Error::io)?;
        std::fs::remove_file(tla_config_file.path()).map_err(Error::io)?;
    }

    // convert each tla trace to json
    traces
        .into_iter()
        .map(module::Tla::tla_trace_to_json_trace)
        .collect()
}

/// Generate TLA+ traces using [`traces`] and executes them against the Rust
/// implementation of the modeled system using a test `runner`.
/// This `runner` implements the [crate::runner::TestRunner] trait.
///
/// For more information, please consult the documentation of [`traces`] and
/// [crate::runner::TestRunner].
///
/// # Examples
///
/// ```
/// use serde::Deserialize;
/// use modelator::runner::TestRunner;
///
/// #[derive(Debug, Clone)]
/// struct NumbersTestRunner;
///
/// impl NumbersTestRunner {
///     fn is_even(number: usize) -> bool {
///         number % 2 == 0
///     }
/// }
///
/// #[derive(Debug, Clone, Deserialize)]
/// struct NumbersStep {
///     a: usize,
///     b: usize,
/// }
///
/// impl TestRunner<NumbersStep> for NumbersTestRunner {
///     fn initial_step(&mut self, step: NumbersStep) -> bool {
///         Self::is_even(step.b)
///     }
///
///     fn next_step(&mut self, step: NumbersStep) -> bool {
///         Self::is_even(step.b)
///     }
/// }
///
/// fn main() {
///     let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
///     let tla_config_file = "tests/integration/tla/Numbers.cfg";
///     let options = modelator::Options::default();
///     let runner = NumbersTestRunner;
///     assert!(modelator::run(tla_tests_file, tla_config_file, &options, runner).is_ok());
/// }
/// ```
#[allow(clippy::needless_doctest_main)]
pub fn run<P, Runner, Step>(
    tla_tests_file: P,
    tla_config_file: P,
    options: &Options,
    runner: Runner,
) -> Result<(), TestError<Step>>
where
    P: AsRef<Path>,
    Runner: runner::TestRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let traces = traces(tla_tests_file, tla_config_file, options).map_err(TestError::Modelator)?;
    for trace in traces {
        runner::run(trace, runner.clone())?;
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
