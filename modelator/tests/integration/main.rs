use modelator::StepRunner;
use modelator::TestReport;
use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde_json::Error;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::path::PathBuf;
use std::{fs, path::Path};

static ROOT_DIR: &str = "tests/integration";

#[test]
/// This is the single, master, integration test
fn integration_test() {
    // We follow the approach proposed in the following link for integration tests:
    // https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html
    // TLDR: use 1 integration test in tests/integration/

    match load_test_batches() {
        Ok(batches) => batches.iter().for_each(|batch| {
            for test in batch.config.tests.iter() {
                if let Err(e) = run_single_test(test, &batch.step_runner) {
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
#[serde(rename_all = "lowercase")]
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

fn run_single_test(test: &Test, step_runner: &StepRunnerLookup) -> Result<(), Error> {
    match test {
        Test::Cli { cmd } => {
            todo!()
        }
        Test::StepRunner {
            test_function,
            tla_tests_filename,
            tla_config_filename,
        } => match step_runner(test_function)(
            tla_tests_filename.to_owned(),
            tla_config_filename.to_owned(),
        ) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        },
    }
}

struct TestBatch {
    config: TestBatchConfig,
    step_runner: Box<StepRunnerLookup>,
}

fn load_test_batches() -> Result<Vec<Box<TestBatch>>, Error> {
    let mut ret: Vec<Box<TestBatch>> = Vec::new();
    for resource_bundle in test_batch_resources() {
        let config = TestBatchConfig::load(resource_bundle.config_filename)?;
        let batch = Box::new(TestBatch {
            config,
            step_runner: resource_bundle.step_runner.unwrap(),
        });
        ret.push(batch);
    }
    Ok(ret)
}

/// A function taking a pair of .tla and .cfg paths and executing run_tla_steps
trait StepRunnerTestFn<P: AsRef<Path>>: Fn(P, P) -> Result<TestReport, crate::Error> {}

type StepRunnerLookup = dyn Fn(&str) -> Box<dyn StepRunnerTestFn<String>>;

struct TestBatchResourceBundle {
    /// filename of .json config in /resource
    config_filename: &'static str,
    /// look up a step runner test function by name
    step_runner: Option<Box<StepRunnerLookup>>,
}

fn test_batch_resources() -> Vec<Box<TestBatchResourceBundle>> {
    let mut ret: Vec<Box<TestBatchResourceBundle>> = Vec::new();

    ret.push(Box::new(TestBatchResourceBundle {
        config_filename: "smoke.json",
        step_runner: None,
    }));

    ret.push(Box::new(TestBatchResourceBundle {
        config_filename: "Numbers.json",
        step_runner: Some(Box::new(|&function_name|{
            match function_name{
                "default"=>
            }
        })),
    }));

    ret
}

#[derive(Debug, Deserialize)]
struct TestBatchConfig {
    name: String,
    description: String,
    tests: Vec<Test>,
}

impl TestBatchConfig {
    fn load(filename: &str) -> Result<TestBatchConfig, serde_json::Error> {
        let path = PathBuf::new()
            .join(ROOT_DIR)
            .join("resource")
            .join(filename);
        let content = fs::read_to_string(path)
            .expect(&format!("Unable to read contents of a {} file", filename).to_owned());
        let ret: TestBatchConfig = serde_json::from_str(&content)?;
        return Ok(ret);
    }
}
