use modelator::model::checker::ModelCheckerWorkers;
use modelator::model::checker::{ModelChecker, ModelCheckerRuntime};
use modelator::ModelatorRuntime;
use serde::Deserialize;
use serde_json::Value as JsonValue;
use shlex;
use std::fmt::Debug;
use std::fs;
use std::path::PathBuf;

use crate::error::IntegrationTestError;

static ROOT_DIR: &str = "tests/integration";

pub fn resource_path(suffix: &str) -> PathBuf {
    PathBuf::new().join(ROOT_DIR).join("resource").join(suffix)
}

/// Take the cli cmd string and split it to mimic the result of std::env::args_os()
pub fn mimic_os_args(cmd: &str) -> Vec<String> {
    // Delegate to a crate because parsing command line strings is non trivial
    shlex::split(cmd).unwrap()
}

pub struct StepRunnerArgs {
    pub modelator_runtime: ModelatorRuntime,
    pub test_function_name: String,
    pub tla_tests_filepath: PathBuf,
    pub tla_config_filepath: PathBuf,
    pub expect: JsonValue,
}

pub type StepRunnerTestFn = dyn Fn(StepRunnerArgs) -> Result<(), IntegrationTestError>;

#[derive(Debug, Deserialize)]
pub struct ModelCheckerRuntimeConfig {
    model_checker: ModelChecker,
    workers: String,
    traces_per_test: String,
}

impl ModelCheckerRuntimeConfig {
    pub fn to_model_checker_runtime(&self) -> ModelCheckerRuntime {
        use std::str::FromStr;
        return ModelCheckerRuntime::default()
            .workers(ModelCheckerWorkers::from_str(&self.workers).unwrap())
            .model_checker(self.model_checker)
            .traces_per_test(self.traces_per_test.parse::<usize>().unwrap());
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
#[serde(rename_all = "snake_case")]
pub enum TestContent {
    Cli {
        cmd: String,
        expect_status: String,
    },
    StepRunner {
        test_function: String,
        tla_tests_filename: String,
        tla_config_filename: String,
        model_checker_runtime: ModelCheckerRuntimeConfig,
        expect: JsonValue,
    },
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub struct Test {
    pub name: String,
    pub description: String,
    pub content: TestContent,
}

pub struct TestBatch {
    pub config: TestBatchConfig,
    pub step_runner: Option<Box<StepRunnerTestFn>>,
}

pub struct TestBatchResourceBundle {
    /// filename of .json config in /resource
    pub config_filename: &'static str,
    /// look up a step runner test function by name
    pub step_runner: Option<Box<StepRunnerTestFn>>,
}

#[derive(Debug, Deserialize)]
pub struct TestBatchConfig {
    pub name: String,
    pub description: String,
    pub tests: Vec<Test>,
}

impl TestBatchConfig {
    pub fn load(filename: &str) -> Result<TestBatchConfig, serde_json::Error> {
        let path = resource_path(filename);
        let content = fs::read_to_string(path)
            .expect(&format!("Unable to read contents of a {} file", filename).to_owned());
        let ret: TestBatchConfig = serde_json::from_str(&content)?;
        return Ok(ret);
    }
}
