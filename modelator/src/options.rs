use clap::Clap;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Clap)]
pub struct Options {
    /// Name of the TLA model.
    #[clap(parse(try_from_str = parse_model_name))]
    pub model_name: String,

    /// Which model checker to use. Possible values: 'TLC'.
    #[clap(short, long, default_value = "TLC")]
    pub model_checker: ModelChecker,

    /// Model checher run mode. Possible values: 'explore,10' to explore the
    /// model randomly and generate 10 random traces; and 'test,X' to generate
    /// a test for X (if possible).
    #[clap(short, long, default_value = "explore,10")]
    pub run_mode: RunMode,

    /// Number of model checker workers. Possible values: 'auto' to select the
    /// number of model checker worker threads based on on the number of
    /// available cores; and any number (e.g. '4') precising the number of
    /// workers threads.
    #[clap(short, long, default_value = "auto")]
    pub workers: Workers,

    /// Model checker log file for debugging purposes.
    #[clap(long, default_value = "mc.log")]
    pub log: PathBuf,

    /// Modelator directory.
    #[clap(long, default_value = ".modelator")]
    pub dir: PathBuf,
}

fn parse_model_name(s: &str) -> clap::Result<String> {
    Ok(strip_tla_extension(s))
}

impl Options {
    pub fn new<S: Into<String>>(model_name: S) -> Self {
        Self {
            model_name: strip_tla_extension(model_name),
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

fn strip_tla_extension<S: Into<String>>(model_name: S) -> String {
    model_name.into().trim_end_matches(".tla").to_owned()
}

#[derive(Clone, Copy, Debug)]
pub enum ModelChecker {
    TLC,
}

impl std::str::FromStr for ModelChecker {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "TLC" => Ok(Self::TLC),
            _ => Err(unsupported(s)),
        }
    }
}

#[derive(Clone, Debug)]
pub enum RunMode {
    /// Test mode. The argument is the name of the test.
    Test(String),
    /// Exploration mode. The argument is the number of traces to be generated.
    /// This mode corresponds to TLC's simulation mode.
    Explore(usize),
}

impl std::str::FromStr for RunMode {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let parts: Vec<_> = s.split(',').collect();
        if parts.len() != 2 {
            return Err(unsupported(s));
        }

        match parts[0] {
            "test" => Ok(Self::Test(parts[1].to_string())),
            "explore" => {
                if let Ok(count) = parts[1].parse() {
                    Ok(Self::Explore(count))
                } else {
                    Err(unsupported(s))
                }
            }
            _ => Err(unsupported(s)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Workers {
    /// Automatically select the number of model checker worker threads based
    // on the number of available cores.
    Auto,
    /// Number of model checker worker threads.
    Count(usize),
}

impl std::str::FromStr for Workers {
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
