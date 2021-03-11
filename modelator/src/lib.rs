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

/// Re-exports.
pub use error::{Error, TestError};
pub use options::{ModelCheckerOptions, ModelCheckerWorkers, Options};

use serde::de::DeserializeOwned;
use std::fmt::Debug;
use std::path::Path;

pub fn traces<P: AsRef<Path>>(
    tla_tests_file: P,
    tla_config_file: P,
    options: Options,
) -> Result<Vec<artifact::JsonTrace>, Error> {
    // create modelator dir (if it doens't already exist)
    if !options.dir.as_path().is_dir() {
        std::fs::create_dir_all(&options.dir).map_err(Error::IO)?;
    }

    // TODO: maybe replace this and the previous step with a build.rs;
    //       see e.g. https://github.com/tensorflow/rust/blob/master/tensorflow-sys/build.rs
    // download missing jars
    jar::download_jars(&options.dir)?;
    tracing::trace!("modelator setup completed");

    // generate tla tests
    let tests = module::Tla::generate_tests(tla_tests_file.into(), tla_config_file.into())?;

    // run tlc on each tla test
    let traces = tests
        .into_iter()
        .map(|(tla_file, tla_config_file)| module::Tlc::test(tla_file, tla_config_file, &options))
        .collect::<Result<Vec<_>, _>>()?;

    // convert each tla trace to json
    traces
        .into_iter()
        .map(|tla_trace| module::Tla::tla_trace_to_json_trace(tla_trace))
        .collect()
}

pub fn run<P, Runner, Step>(
    tla_tests_file: P,
    tla_config_file: P,
    runner: Runner,
) -> Result<(), TestError<Runner, Step>>
where
    P: AsRef<Path>,
    Runner: runner::TestRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let options = Options::default();
    let traces = traces(tla_tests_file, tla_config_file, options).map_err(TestError::Modelator)?;
    for trace in traces {
        let runner = runner.clone();
        runner::run(trace, runner)?;
    }
    Ok(())
}
