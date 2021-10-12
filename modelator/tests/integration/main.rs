use modelator::StepRunner;
use modelator::TestReport;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde_json::Error;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::path::PathBuf;
use std::{fs, path::Path};

mod resource;

static ROOT_DIR: &str = "tests/integration";

fn resource_path(suffix: &str) -> PathBuf {
    PathBuf::new().join(ROOT_DIR).join("resource").join(suffix)
}

#[test]
/// This is the single, master, integration test
fn integration_test() {
    // We follow the approach proposed in the following link for integration tests:
    // https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html
    // TLDR: use 1 integration test in tests/integration/

    match load_test_batches() {
        Ok(batches) => batches.iter().for_each(|batch| {
            for test in batch.config.tests.iter() {
                if let Err(e) = run_single_test(&batch, &test) {
                    panic!(
                        r#"Test batch {} failed.
[name:{},description:{}]
Error: 
{}
"#,
                        batch.config.name, e, batch.config.name, batch.config.description
                    )
                }
            }
        }),
        Err(e) => panic!("{}", e),
    }
}

#[derive(Debug, Deserialize)]
#[serde(tag = "type")]
#[serde(rename_all = "snake_case")]
enum Test {
    Cli {
        cmd: String,
    },
    StepRunner {
        test_function: String,
        tla_tests_filename: String,
        tla_config_filename: String,
    },
}

/// A function taking a pair of .tla and .cfg paths and executing run_tla_steps
type StepRunnerTestFn = dyn Fn(&PathBuf, &PathBuf) -> Result<TestReport, modelator::Error>;

type StepRunnerLookup = dyn Fn(&str) -> Box<StepRunnerTestFn>;

struct TestBatch {
    config: TestBatchConfig,
    step_runner_lookup: Option<Box<StepRunnerLookup>>,
}

struct TestBatchResourceBundle {
    /// filename of .json config in /resource
    config_filename: &'static str,
    /// look up a step runner test function by name
    step_runner: Option<Box<StepRunnerLookup>>,
}

#[derive(Debug, Deserialize)]
struct TestBatchConfig {
    name: String,
    description: String,
    tests: Vec<Test>,
}

impl TestBatchConfig {
    fn load(filename: &str) -> Result<TestBatchConfig, serde_json::Error> {
        let path = resource_path(filename);
        let content = fs::read_to_string(path)
            .expect(&format!("Unable to read contents of a {} file", filename).to_owned());
        let ret: TestBatchConfig = serde_json::from_str(&content)?;
        return Ok(ret);
    }
}

fn run_single_test(batch: &TestBatch, test: &Test) -> Result<(), modelator::Error> {
    match test {
        Test::Cli { cmd } => {
            todo!()
        }
        Test::StepRunner {
            test_function,
            tla_tests_filename,
            tla_config_filename,
        } => match batch.step_runner_lookup.as_ref().unwrap()(test_function)(
            &resource_path(tla_tests_filename),
            &resource_path(tla_config_filename),
        ) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        },
    }
}

fn load_test_batches() -> Result<Vec<Box<TestBatch>>, Error> {
    let mut ret: Vec<Box<TestBatch>> = Vec::new();
    for resource_bundle in test_batch_resources() {
        let config = TestBatchConfig::load(resource_bundle.config_filename)?;
        let batch = Box::new(TestBatch {
            config,
            step_runner_lookup: resource_bundle.step_runner,
        });
        ret.push(batch);
    }
    Ok(ret)
}

fn test_batch_resources() -> Vec<Box<TestBatchResourceBundle>> {
    let mut ret: Vec<Box<TestBatchResourceBundle>> = Vec::new();

    {
        ret.push(Box::new(TestBatchResourceBundle {
            config_filename: "smoke.json",
            step_runner: None,
        }));
    }

    {
        let lookup: Box<StepRunnerLookup> =
            Box::new(|test_function_name| match test_function_name {
                "default" => Box::new(
                    |tla_tests_filename: &PathBuf,
                     tla_config_filename: &PathBuf|
                     -> Result<TestReport, modelator::Error> {
                        resource::numbers::default(tla_tests_filename, tla_config_filename)
                    },
                ),
                _ => panic!("test function lookup failed"),
            });

        ret.push(Box::new(TestBatchResourceBundle {
            config_filename: "Numbers.json",
            step_runner: Some(lookup),
        }));
    }

    ret
}
