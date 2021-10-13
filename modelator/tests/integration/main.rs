pub mod common;
pub mod error;
mod resource;

use clap::Clap;
use common::*;
use error::IntegrationTestError;
use modelator::Error;
use modelator::ModelatorRuntime;
use resource::numbers;

/// Register integration tests here by specifying a config file path and
/// (optionally) a handler for step runner tests.
fn test_batch_resources() -> Vec<Box<TestBatchResourceBundle>> {
    let mut ret: Vec<Box<TestBatchResourceBundle>> = Vec::new();

    // {
    //     ret.push(Box::new(TestBatchResourceBundle {
    //         config_filename: "smoke.json",
    //         step_runner: None,
    //     }));
    // }

    // {
    //     ret.push(Box::new(TestBatchResourceBundle {
    //         config_filename: "IBC_ics02.json",
    //         step_runner: None,
    //     }));
    // }

    // {
    //     ret.push(Box::new(TestBatchResourceBundle {
    //         config_filename: "Numbers.json",
    //         step_runner: Some(Box::new(|args| numbers::test(args))),
    //     }));
    // }

    // {
    //     ret.push(Box::new(TestBatchResourceBundle {
    //         config_filename: "TrafficCrossing.json",
    //         step_runner: None,
    //     }));
    // }

    {
        ret.push(Box::new(TestBatchResourceBundle {
            config_filename: "Indices.json",
            step_runner: None,
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

    // Use to match a single test <batch name>/<test name>
    let pattern = "";

    let filter = |batch_name, test_name| {
        let compare = format!("{}/{}", batch_name, test_name);
        pattern.is_empty() || compare == pattern
    };

    match load_test_batches() {
        Ok(batches) => batches.iter().for_each(|batch| {
            for test in batch.config.tests.iter() {
                if filter(&batch.config.name, &test.name) {
                    if let Err(err) = run_single_test(&batch, &test.content) {
                        panic!(
                            r#"Test {} in batch {} failed.
[name:{},batch_name:{},description:{}]
Error: 
{}
"#,
                            test.name,
                            batch.config.name,
                            test.name,
                            batch.config.name,
                            batch.config.description,
                            err
                        )
                    }
                }
            }
        }),
        Err(e) => panic!("{}", e),
    }
}

fn run_single_test(
    batch: &TestBatch,
    test_content: &TestContent,
) -> Result<(), IntegrationTestError> {
    match test_content {
        TestContent::Cli { cmd, expect_status } => {
            let os_args = mimic_os_args(cmd);
            let cli_app = modelator::cli::App::try_parse_from(os_args)?;
            let result = cli_app.run();
            let actual = serde_json::to_string(&result.status).unwrap();
            // The actual status is a double quoted string so add quotes
            let expect = format!("\"{}\"", expect_status);
            match expect == actual {
                true => Ok(()),
                false => Err(IntegrationTestError::ExpectedValueMismatch(expect, actual)),
            }
        }
        TestContent::StepRunner {
            test_function,
            tla_tests_filename,
            tla_config_filename,
            expect,
            model_checker_runtime,
        } => match batch.step_runner.as_ref().unwrap()(StepRunnerArgs {
            test_function_name: test_function.to_owned(),
            tla_tests_filepath: resource_path(tla_tests_filename),
            tla_config_filepath: resource_path(tla_config_filename),
            expect: expect.to_owned(),
            modelator_runtime: ModelatorRuntime::default()
                .model_checker_runtime(model_checker_runtime.to_model_checker_runtime()),
        }) {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        },
    }
}

/// Loads the .json files registered in test_batch_resources and creates test batches
fn load_test_batches() -> Result<Vec<Box<TestBatch>>, IntegrationTestError> {
    let mut ret: Vec<Box<TestBatch>> = Vec::new();
    for resource_bundle in test_batch_resources() {
        let config = TestBatchConfig::load(resource_bundle.config_filename)?;

        let batch = Box::new(TestBatch {
            config,
            step_runner: resource_bundle.step_runner,
        });

        ret.push(batch);
    }
    Ok(ret)
}
