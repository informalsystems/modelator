/// Definition of a Trace.
mod trace;

/// TLC model-checker.
mod tlc;

/// Conversion from TLA counterexamples to JSON.
mod json;

/// Utilitary functions.
mod util;

use crate::{Options, Error, ModelChecker};
use std::path::Path;

pub(crate) async fn run(options: Options) -> Result<Vec<String>, Error> {
    // check that the model tla file exists
    let model_file = format!("{}.tla", &options.model_name);
    let model_file = Path::new(&model_file);
    if !model_file.is_file() {
        return Err(Error::FileNotFound(model_file.to_path_buf()));
    }

    // check that the model cfg file exists
    let cfg_file = format!("{}.cfg", &options.model_name);
    let cfg_file = Path::new(&cfg_file);
    if !cfg_file.is_file() {
        return Err(Error::FileNotFound(cfg_file.to_path_buf()));
    }

    // create new model with the tests negated

    // match options.model_checker {
    // ModelChecker::TLC => tlc::run(&dir),
    // }

    let traces = Vec::new();
    // check if no trace was found
    if traces.is_empty() {
        return Err(Error::NoTraceFound(options.log));
    }

    // convert each trace to json
    json::traces_to_json(options.dir, traces).await
}
