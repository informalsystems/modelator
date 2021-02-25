use std::path::{Path, PathBuf};
pub enum ModelChecker {
    TLC,
}
pub enum Workers {
    /// Automatically select the number of worker threads based on the number of
    /// available cores.
    Auto,
    /// Precise number of worker threads.
    Count(usize),
}

pub struct Config {
    /// Which model checker to use.
    pub model_checker: ModelChecker,

    /// Number of model checker workers.
    pub workers: Workers,

    /// Model checker log file for debugging purposes.
    pub log: PathBuf,

    /// Modelator directory.
    pub dir: PathBuf,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            model_checker: ModelChecker::TLC,
            workers: Workers::Auto,
            log: Path::new("mc.log").to_path_buf(),
            dir: Path::new(".modelator").to_path_buf(),
        }
    }
}

impl Config {
    /// Set which `ModelChecker` to use.
    pub fn model_checker(mut self, model_checker: ModelChecker) -> Self {
        self.model_checker = model_checker;
        self
    }

    /// Set number of model checker workers.
    pub fn workers(mut self, workers: Workers) -> Self {
        self.workers = workers;
        self
    }

    /// Set model checker log file.
    pub fn log(mut self, log: impl AsRef<Path>) -> Self {
        self.log = log.as_ref().to_path_buf();
        self
    }

    /// Set modelator directory.
    pub fn dir(mut self, dir: impl AsRef<Path>) -> Self {
        self.dir = dir.as_ref().to_path_buf();
        self
    }
}
