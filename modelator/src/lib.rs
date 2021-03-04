/// Modelator's options.
mod options;

/// Modelator's error type.
mod error;

/// Download jar utilities.
mod jar;

/// Model checkers.
mod mc;

/// Test runner.
pub mod runner;

/// Re-exports.
pub use error::{Error, TestError};
pub use mc::JsonTrace;
pub use options::{ModelChecker, Options, RunMode, Workers};

use serde::de::DeserializeOwned;
use std::fmt::Debug;

pub async fn traces(options: Options) -> Result<Vec<JsonTrace>, Error> {
    // create modelator dir (if it doens't already exist)
    if !options.dir.as_path().is_dir() {
        tokio::fs::create_dir_all(&options.dir)
            .await
            .map_err(Error::IO)?;
    }

    // TODO: maybe replace this and the previous step with a build.rs;
    //       see e.g. https://github.com/tensorflow/rust/blob/master/tensorflow-sys/build.rs
    // download missing jars
    jar::download_jars(&options.dir).await?;
    tracing::trace!("modelator setup completed");

    // run model checker
    mc::run(options).await
}

pub async fn run<Runner, Step>(
    options: Options,
    runner: Runner,
) -> Result<(), TestError<Runner, Step>>
where
    Runner: runner::TestRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let traces = traces(options).await.map_err(TestError::Modelator)?;
    for trace in traces {
        let runner = runner.clone();
        runner::run(trace, runner)?;
    }
    Ok(())
}
