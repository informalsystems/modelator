pub mod common;
mod resource;

use clap::Clap;
use common::*;
use resource::numbers;
use shlex;

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
            config_filename: "IBC_ics02.json",
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

/// Take the cmd string and split it to mimic the result of std::env::args_os()
fn mimic_os_args(cmd: &str) -> Vec<String> {
    // Delegate to a crate because parsing command line strings is non trivial
    shlex::split(cmd).unwrap()
}

fn run_single_test(batch: &TestBatch, test: &Test) -> Result<(), modelator::Error> {
    match test {
        Test::Cli { cmd, expect_status } => {
            let os_args = mimic_os_args(cmd);
            let cli_app = modelator::cli::App::try_parse_from(os_args)?;
            let result = cli_app.run();
            let actual_status = serde_json::to_string(&result.status).unwrap();
            // The actual status is a double quoted string
            assert_eq!(format!("\"{}\"", expect_status), actual_status);
            Ok(())
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
        // TODO: here will be Test::EventRunner
    }
}

/// Loads the .json files registered in test_batch_resources and creates test batches
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
