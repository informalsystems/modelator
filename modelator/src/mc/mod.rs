/// Definition of a Trace.
mod trace;

/// TLC model-checker.
mod tlc;

/// Conversion from TLA counterexamples to JSON.
mod json;

/// Utilitary functions.
mod util;

/// Re-exports.
pub use trace::JsonTrace;

use crate::{Error, ModelChecker, Options, RunMode};
use std::path::{Path, PathBuf};

pub(crate) async fn run(mut options: Options) -> Result<Vec<JsonTrace>, Error> {
    // check that the model tla file exists
    if !options.model_file.is_file() {
        return Err(Error::FileNotFound(options.model_file));
    }

    // compute model directory
    let mut model_dir = options.model_file.clone();
    assert!(model_dir.pop());

    // extract tla model name
    let model_name = options
        .model_file
        .file_name()
        .unwrap()
        .to_string_lossy()
        .trim_end_matches(".tla")
        .to_owned();

    // check that the model cfg file exists
    let cfg_file = model_dir.join(format!("{}.cfg", model_name));
    if !cfg_file.is_file() {
        return Err(Error::FileNotFound(cfg_file));
    }

    // create new model file with the tests negated if `RunMode::Test`
    if let RunMode::Test(test_name) = &options.run_mode {
        let model_file = create_test(model_dir, &model_name, test_name, cfg_file).await?;
        // update model file in options
        options.model_file = model_file;
    };

    // run the model checker
    let traces = match options.model_checker {
        ModelChecker::TLC => tlc::run(&options),
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
    model_dir: P,
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
    let test_model_file = model_dir.as_ref().join(format!("{}.tla", test_model_name));
    tokio::fs::write(&test_model_file, test_model)
        .await
        .map_err(Error::IO)?;

    // write test cfg to test cfg file
    let test_cfg_file = model_dir.as_ref().join(format!("{}.cfg", test_model_name));
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
