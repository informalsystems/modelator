pub mod common;
mod resource;

use common::*;
use resource::numbers;

/// Register integration tests here by specifying a config file path and
/// (optionally) a handler for step runner tests.
fn test_batch_resources() -> Vec<Box<TestBatchResourceBundle>> {
    let mut ret: Vec<Box<TestBatchResourceBundle>> = Vec::new();

    {
        ret.push(Box::new(TestBatchResourceBundle {
            config_filename: "smoke.json",
            step_runner: None,
        }));
    }

    {
        ret.push(Box::new(TestBatchResourceBundle {
            config_filename: "Numbers.json",
            step_runner: Some(Box::new(|args| numbers::test(args))),
        }));
    }

    ret
}

#[test]
/// This is the single, master, integration test
fn integration_test() {
    // We follow the approach proposed in the following link for integration tests:
    // https://matklad.github.io/2021/02/27/delete-cargo-integration-tests.html
    // TLDR: use exactly 1 integration test in tests/integration/

    match load_test_batches() {
        Ok(batches) => batches.iter().for_each(|batch| {
            for test in batch.config.tests.iter() {
                if let Err(err) = run_single_test(&batch, &test) {
                    panic!(
                        r#"Test batch {} failed.
[name:{},description:{}]
Error: 
{}
"#,
                        batch.config.name, batch.config.name, batch.config.description, err
                    )
                }
            }
        }),
        Err(e) => panic!("{}", e),
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
            expect,
        } => match batch.step_runner.as_ref().unwrap()(StepRunnerArgs {
            test_function_name: test_function.to_owned(),
            tla_tests_filepath: resource_path(tla_tests_filename),
            tla_config_filepath: resource_path(tla_config_filename),
            expect: expect.to_owned(),
        }) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        },
    }
}

fn load_test_batches() -> Result<Vec<Box<TestBatch>>, modelator::Error> {
    let mut ret: Vec<Box<TestBatch>> = Vec::new();
    for resource_bundle in test_batch_resources() {
        let config = TestBatchConfig::load(resource_bundle.config_filename).map_err(|err| {
            modelator::Error::JsonParseError(format!(
                "Failed to parse {} [serde::de::Error : {}]",
                resource_bundle.config_filename,
                err.to_string()
            ))
        })?;

        let batch = Box::new(TestBatch {
            config,
            step_runner: resource_bundle.step_runner,
        });

        ret.push(batch);
    }
    Ok(ret)
}
