/// Modelator's options.
mod options;

/// Modelator's error type.
mod error;

/// Download jar utilities.
mod jar;

/// Model checkers.
mod mc;

/// Test runner.
mod runner;

/// Re-exports.
pub use error::{Error, TestError};
pub use options::{ModelChecker, Options, RunMode, Workers};
pub use mc::JsonTrace;

use serde::de::DeserializeOwned;
use std::fmt::Debug;

pub async fn run(options: Options) -> Result<Vec<JsonTrace>, Error> {
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

    // run model checker
    mc::run(options).await
}

pub async fn test<Runner, Step>(
    options: Options,
    runner: Runner,
) -> Result<(), TestError<Runner, Step>>
where
    Runner: runner::TestRunner<Step> + Debug + Clone,
    Step: DeserializeOwned + Debug + Clone,
{
    let traces = run(options).await.map_err(TestError::Modelator)?;
    for trace in traces {
        let runner = runner.clone();
        runner::test(trace, runner)?;
    }
    Ok(())
}
