/// Definition of a Trace.
mod trace;

/// TLC model-checker.
mod tlc;

/// Conversion from TLA counterexamples to JSON.
mod json;

/// Utilitary functions.
mod util;

use crate::{Error, ModelChecker, Options, RunMode};
use std::path::{Path, PathBuf};

pub(crate) async fn run(options: Options) -> Result<Vec<String>, Error> {
    // check that the model tla file exists
    let model_file = Path::new(&format!("{}.tla", &options.model_name)).to_path_buf();
    if !model_file.is_file() {
        return Err(Error::FileNotFound(model_file));
    }

    // check that the model cfg file exists
    let cfg_file = Path::new(&format!("{}.cfg", &options.model_name)).to_path_buf();
    if !cfg_file.is_file() {
        return Err(Error::FileNotFound(cfg_file));
    }

    // create new model with the tests negated if `RunMode::Test`
    let model_file = match &options.run_mode {
        RunMode::Test(test_name) => create_test(&options.model_name, test_name, &cfg_file).await?,
        RunMode::Explore(_) => model_file,
    };

    // run the model checker
    let traces = match options.model_checker {
        ModelChecker::TLC => tlc::run(model_file, &options),
    }
    .await?;

    // check if no trace was found
    if traces.is_empty() {
        return Err(Error::NoTraceFound(options.log));
    }

    // convert each trace to json
    json::traces_to_json(&options.dir, traces).await
}

async fn create_test<P: AsRef<Path>>(
    model_name: &str,
    test_name: &str,
    cfg_file: P,
) -> Result<PathBuf, Error> {
    let test_model_name = format!("{}_{}", model_name, test_name);
    let invariant = format!("{}Neg", test_name);
    // create test model where the test is negated
    let test_model = test_model(model_name, test_name, &test_model_name, &invariant);
    // create test config with negated test as an invariant
    let test_cfg = test_cfg(&invariant, cfg_file).await?;

    // write test model to test model file
    let test_model_file = Path::new(&format!("{}.tla", test_model_name)).to_path_buf();
    tokio::fs::write(&test_model_file, test_model)
        .await
        .map_err(Error::IO)?;

    // write test cfg to test cfg file
    let test_cfg_file = Path::new(&format!("{}.cfg", test_model_name)).to_path_buf();
    tokio::fs::write(&test_cfg_file, test_cfg)
        .await
        .map_err(Error::IO)?;
    Ok(test_model_file)
}

fn test_model(model_name: &str, test_name: &str, test_model_name: &str, invariant: &str) -> String {
    format!(
        r#"
---------- MODULE {} ----------

EXTENDS {}

{} == ~{}

===============================
"#,
        test_model_name, model_name, invariant, test_name
    )
}

async fn test_cfg<P: AsRef<Path>>(invariant: &str, cfg_file: P) -> Result<String, Error> {
    let cfg = tokio::fs::read_to_string(cfg_file)
        .await
        .map_err(Error::IO)?;
    Ok(format!(
        r#"
{}
INVARIANT {}
"#,
        cfg, invariant
    ))
}
