/// Conversion from TLA traces to JSON.
mod json;

use crate::artifact::{JsonTrace, TlaConfigFile, TlaFile, TlaTrace};
use crate::Error;
use serde_json::Value as JsonValue;
use std::path::PathBuf;
// #[modelator::module]
pub struct Tla;

impl Tla {
    // #[modelator::method]
    pub fn tla_trace_to_json_trace(tla_trace: TlaTrace) -> Result<JsonTrace, Error> {
        tracing::debug!("Tla::tla_trace_to_json_trace:\n{:#?}", tla_trace);
        let states: Vec<JsonValue> = tla_trace
            .into_iter()
            .map(|state| json::state_to_json(&state))
            .collect::<Result<_, _>>()?;
        Ok(states.into())
    }

    // #[modelator::method]
    pub fn generate_tests(
        tla_tests_file: TlaFile,
        tla_config_file: TlaConfigFile,
    ) -> Result<Vec<(TlaFile, TlaConfigFile)>, Error> {
        tracing::debug!("Tla::generate_tests {} {}", tla_tests_file, tla_config_file);
        // check that the tla tests file exists
        if !tla_tests_file.path().is_file() {
            return Err(Error::FileNotFound(tla_tests_file.path().clone()));
        }

        // check that the tla cfg file exists
        if !tla_config_file.path().is_file() {
            return Err(Error::FileNotFound(tla_config_file.path().clone()));
        }

        // compute the directory in which the tla tests file is stored
        let mut tla_tests_dir = tla_tests_file.path().clone();
        assert!(tla_tests_dir.pop());

        // compute tla tests module name: it's safe to unwrap because we have
        // already checked that the tests file is indeed a file
        let tla_tests_module_name = tla_tests_file.tla_module_name().unwrap();

        // TODO: retrieve test names from tla tests file
        extract_test_names(&tla_tests_file)?
            .into_iter()
            .map(|test_name| {
                generate_test(
                    &tla_tests_dir,
                    &tla_tests_module_name,
                    &test_name,
                    &tla_config_file,
                )
            })
            .collect()
    }
}

fn extract_test_names(tla_test_file: &TlaFile) -> Result<Vec<String>, Error> {
    let content = std::fs::read_to_string(tla_test_file.path()).map_err(Error::IO)?;
    let test_names = content
        .lines()
        .filter_map(|line| {
            // take the first element in the split
            line.trim().split("==").next()
        })
        .filter_map(|name| {
            let name = name.trim();
            // consider this as a test name if it starts/ends Test
            if name.starts_with("Test") || name.ends_with("Test") {
                Some(name.to_string())
            } else {
                None
            }
        })
        .collect();
    tracing::debug!(
        "test names extracted from {}:\n{:?}",
        tla_test_file,
        test_names
    );
    Ok(test_names)
}

fn generate_test(
    tla_tests_dir: &PathBuf,
    tla_tests_module_name: &str,
    test_name: &str,
    tla_config_file: &TlaConfigFile,
) -> Result<(TlaFile, TlaConfigFile), Error> {
    let test_module_name = format!("{}_{}", tla_tests_module_name, test_name);
    let invariant = format!("{}Neg", test_name);

    // create tla module where the test is negated
    let test_module = genereate_test_module(
        tla_tests_module_name,
        test_name,
        &test_module_name,
        &invariant,
    );
    // create test config with negated test as an invariant
    let test_config = generate_test_config(tla_config_file, &invariant)?;

    // write test module to test module file
    let test_module_file = tla_tests_dir.join(format!("{}.tla", test_module_name));
    std::fs::write(&test_module_file, test_module).map_err(Error::IO)?;

    // write test config to test config file
    let test_config_file = tla_tests_dir.join(format!("{}.cfg", test_module_name));
    std::fs::write(&test_config_file, test_config).map_err(Error::IO)?;

    Ok((test_module_file.into(), test_config_file.into()))
}

fn genereate_test_module(
    tla_tests_module_name: &str,
    test_name: &str,
    test_module_name: &str,
    invariant: &str,
) -> String {
    format!(
        r#"
---------- MODULE {} ----------

EXTENDS {}

{} == ~{}

===============================
"#,
        test_module_name, tla_tests_module_name, invariant, test_name
    )
}

fn generate_test_config(tla_config_file: &TlaConfigFile, invariant: &str) -> Result<String, Error> {
    let tla_config = std::fs::read_to_string(tla_config_file.path()).map_err(Error::IO)?;
    Ok(format!(
        r#"
{}
INVARIANT {}
"#,
        tla_config, invariant
    ))
}
