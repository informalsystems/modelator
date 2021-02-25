/// Modelator's config.
mod config;

/// Modelator's error type.
mod error;

/// Download jar utilities.
mod jar;

/// Model checkers.
mod mc;

/// Re-exports.
pub use config::{Options, ModelChecker, Workers};
pub use error::Error;

pub async fn run(options: Options) -> Result<Vec<String>, Error> {
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
