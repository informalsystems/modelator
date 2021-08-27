use std::env;
use std::path::{Path, PathBuf};

/// Set of options to configure `modelator`.
#[derive(Clone, Debug)]
pub struct ModelatorRuntime {
    /// Model checker options.
    pub model_checker_runtime: ModelCheckerRuntime,

    /// Modelator directory.
    pub dir: PathBuf,
}

impl ModelatorRuntime {
    /// Set TLC options.
    pub fn model_checker_runtime(mut self, model_checker_runtime: ModelCheckerRuntime) -> Self {
        self.model_checker_runtime = model_checker_runtime;
        self
    }

    /// Set modelator directory.
    pub fn dir(mut self, dir: impl AsRef<Path>) -> Self {
        self.dir = dir.as_ref().to_path_buf();
        self
    }
}

impl Default for ModelatorRuntime {
    fn default() -> Self {
        Self {
            model_checker_runtime: ModelCheckerRuntime::default(),
            dir: env::current_dir().unwrap().join(".modelator"), //Path::new(".modelator").to_path_buf(),
        }
    }
}

/// Set of options to select the model checker to be used and configure them.
#[derive(Clone, Debug)]
pub struct ModelCheckerRuntime {
    /// Which model checker to use.
    pub model_checker: ModelChecker,

    /// Number of model checker worker threads. Possible values: 'auto' to
    /// select the number of worker threads based on the number of available
    /// cores; and any number (e.g. '4') precising the number of workers threads.
    pub workers: ModelCheckerWorkers,

    /// Model checker log file for debugging purposes.
    pub log: PathBuf,
}

impl ModelCheckerRuntime {
    /// Set the model checker.
    pub fn model_checker(mut self, model_checker: ModelChecker) -> Self {
        self.model_checker = model_checker;
        self
    }

    /// Set number of model checker workers.
    pub fn workers(mut self, workers: ModelCheckerWorkers) -> Self {
        self.workers = workers;
        self
    }

    /// Set model checker log file.
    pub fn log(mut self, log: impl AsRef<Path>) -> Self {
        self.log = log.as_ref().to_path_buf();
        self
    }
}

impl Default for ModelCheckerRuntime {
    fn default() -> Self {
        Self {
            model_checker: ModelChecker::Apalache,
            workers: ModelCheckerWorkers::Auto,
            log: Path::new("mc.log").to_path_buf(),
        }
    }
}

/// Configuration option to select the model checker to be used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModelChecker {
    /// Option representing the [TLC](https://github.com/tlaplus/tlaplus) model
    /// checker.
    Tlc,
    /// Option representing the [Apalache](http://github.com/informalsystems/apalache)
    /// mode checker.
    Apalache,
}

/// Configuration option to select the number of model checker workers.
#[derive(Clone, Copy, Debug)]
pub enum ModelCheckerWorkers {
    /// Automatically select the number of model checker worker threads based
    /// on the number of available cores.
    Auto,
    /// Number of model checker worker threads.
    Count(usize),
}

impl std::str::FromStr for ModelCheckerWorkers {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "auto" => Ok(Self::Auto),
            _ => {
                if let Ok(count) = s.parse() {
                    Ok(Self::Count(count))
                } else {
                    Err(unsupported(s))
                }
            }
        }
    }
}

fn unsupported(s: &str) -> String {
    format!("unsupported value {:?}", s)
}
