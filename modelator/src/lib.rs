/// Modelator's options.
mod options;

/// Modelator's error type.
mod error;

/// List of artifacts.
pub mod artifact;

/// List of modules.
pub mod module;

/// Download jar utilities.
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

pub mod tester;

pub mod event;

/// Re-exports.
pub use cli::{CliOptions, CliOutput, CliStatus};
pub use datachef::Recipe;
pub use error::{Error, TestError};
pub use event::{ActionHandler, Event, EventStream, Runner, StateHandler};
pub use options::{ModelChecker, ModelCheckerOptions, ModelCheckerWorkers, Options};

use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::path::Path;

pub fn traces<P: AsRef<Path>>(
    tla_tests_file: P,
    tla_config_file: P,
    options: Options,
) -> Result<Vec<artifact::JsonTrace>, Error> {
    // setup modelator
    setup(&options)?;

    // generate tla tests
    let tests = module::Tla::generate_tests(tla_tests_file.into(), tla_config_file.into())?;

    // run the model checker configured on each tla test
    let traces = tests
        .clone()
        .into_iter()
        .map(
            |(tla_file, tla_config_file)| match options.model_checker_options.model_checker {
                ModelChecker::Tlc => module::Tlc::test(tla_file, tla_config_file, &options),
                ModelChecker::Apalache => {
                    module::Apalache::test(tla_file, tla_config_file, &options)
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

pub fn run<P, Runner, Step>(
    tla_tests_file: P,
    tla_config_file: P,
    runner: &mut Runner,
) -> Result<(), TestError<Step>>
where
    P: AsRef<Path>,
    Runner: runner::TestRunner<Step> + Debug,
    Step: DeserializeOwned + Debug + Clone,
{
    let options = Options::default();
    let traces = traces(tla_tests_file, tla_config_file, options).map_err(TestError::Modelator)?;
    for trace in traces {
        //let runner = runner.clone();
        runner::run(trace, runner)?;
    }
    Ok(())
}

pub(crate) fn setup(options: &Options) -> Result<(), Error> {
    // create modelator dir (if it doens't already exist)
    if !options.dir.as_path().is_dir() {
        std::fs::create_dir_all(&options.dir).map_err(Error::io)?;
    }

    // write missing jars
    jar::write_jars(&options.dir)?;
    tracing::trace!("modelator setup completed");

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

    Ok(())
}
