/// Modelator's config.
mod config;

/// Modelator's error type.
mod error;

/// Download jar utilities.
mod jar;

/// TLC model-checker.
// mod tlc;

/// Re-exports.
pub use config::{Config, ModelChecker, Workers};
pub use error::Error;

use std::path::Path;

pub async fn run<P, I>(
    tla_model: P,
    tla_config: P,
    invariants: Vec<I>,
    options: Config,
) -> Result<Vec<String>, Error>
where
    P: AsRef<Path>,
    I: Into<String>,
{
    // check that both the tla model and the tla config files exist
    let tla_model = tla_model.as_ref();
    let tla_config = tla_config.as_ref();
    if !tla_model.is_file() {
        return Err(Error::FileNotFound(tla_model.to_path_buf()));
    }
    if !tla_config.is_file() {
        return Err(Error::FileNotFound(tla_config.to_path_buf()));
    }

    // create modelator dir (if it doens't already exist)
    if !options.dir.as_path().is_dir() {
        tokio::fs::create_dir_all(&options.dir)
            .await
            .map_err(Error::IO)?;
    }

    // download missing jars
    jar::download_jars(&options.dir).await?;

    // get tlc counterexample
    // tlc.run(&dir)
    Ok(Vec::new())
}
