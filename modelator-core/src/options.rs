use std::path::{Path, PathBuf};
#[derive(Clone, Copy, Debug)]
pub enum ModelChecker {
    TLC,
}

#[derive(Clone, Debug)]
pub enum RunMode {
    /// Test mode. The argument is the name of the test.
    Test(String),
    /// Exploration mode. The argument is the number of traces to be generated.
    /// This mode corresponds to TLC's simulation mode.
    Explore(usize),
}

#[derive(Clone, Copy, Debug)]
pub enum Workers {
    /// Automatically select the number of model checker worker threads based
    // on the number of available cores.
    Auto,
    /// Number of model checker worker threads.
    Count(usize),
}

#[derive(Clone, Debug)]
pub struct Options {
    /// Name of the TLA model.
    pub model_name: String,

    /// Which model checker to use.
    pub model_checker: ModelChecker,

    /// Model checher run mode.
    pub run_mode: RunMode,

    /// Number of model checker workers.
    pub workers: Workers,

    /// Model checker log file for debugging purposes.
    pub log: PathBuf,

    /// Modelator directory.
    pub dir: PathBuf,
}

impl Options {
    pub fn new<S: Into<String>>(model_name: S) -> Self {
        let model_name = model_name.into().trim_end_matches(".tla").to_owned();
        Self {
            model_name,
            model_checker: ModelChecker::TLC,
            workers: Workers::Auto,
            run_mode: RunMode::Explore(10),
            log: Path::new("mc.log").to_path_buf(),
            dir: Path::new(".modelator").to_path_buf(),
        }
    }

    /// Set the TLC model checker.
    pub fn tlc(mut self) -> Self {
        self.model_checker = ModelChecker::TLC;
        self
    }

    /// Set the test run mode given the test name.
    pub fn test<S: Into<String>>(mut self, test_name: S) -> Self {
        self.run_mode = RunMode::Test(test_name.into());
        self
    }

    /// Set the explore run mode given the number of traces to be generated.
    pub fn explore(mut self, trace_count: usize) -> Self {
        self.run_mode = RunMode::Explore(trace_count);
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
