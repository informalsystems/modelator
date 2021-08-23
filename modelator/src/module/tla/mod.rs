/// Conversion from TLA traces to JSON.
mod json;

use crate::artifact::{JsonTrace, TlaConfigFile, TlaFile, TlaTrace};
use crate::Error;
use serde_json::Value as JsonValue;
use std::path::Path;

/// `modelator`'s TLA module.
#[derive(Debug, Clone, Copy)]
pub struct Tla;

impl Tla {
    /// Convert a [TlaTrace] into a [JsonTrace].
    ///
    /// # Examples
    ///
    /// ```ignore
    /// TODO: ignoring because of https://github.com/informalsystems/modelator/issues/47
    /// use modelator::artifact::{TlaFile, TlaConfigFile};
    /// use modelator::module::{Tla, Tlc};
    /// use modelator::Options;
    /// use std::convert::TryFrom;
    ///
    /// let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
    /// let tla_config_file = "tests/integration/tla/Numbers.cfg";
    /// let tla_tests_file = TlaFile::try_from(tla_tests_file).unwrap();
    /// let tla_config_file = TlaConfigFile::try_from(tla_config_file).unwrap();
    ///
    /// let mut tests = Tla::generate_tests(tla_tests_file, tla_config_file).unwrap();
    /// let (tla_test_file, tla_test_config_file) = tests.pop().unwrap();
    /// let options = Options::default();
    /// let tla_trace = Tlc::test(tla_test_file, tla_test_config_file, &options).unwrap();
    /// let json_trace = Tla::tla_trace_to_json_trace(tla_trace).unwrap();
    /// println!("{:?}", json_trace);
    /// ```
    pub fn tla_trace_to_json_trace(tla_trace: TlaTrace) -> Result<JsonTrace, Error> {
        tracing::debug!("Tla::tla_trace_to_json_trace:\n{}", tla_trace);
        let states: Vec<JsonValue> = tla_trace
            .into_iter()
            .map(|state| json::state_to_json(&state))
            .collect::<Result<_, _>>()?;
        Ok(states.into())
    }

    /// Generate TLA+ test and config files given a [TlaFile] containing TLA+
    /// test assertions and a [TlaConfigFile].
    ///
    /// # Examples
    ///
    /// ```ignore
    /// TODO: ignoring because of https://github.com/informalsystems/modelator/issues/47
    /// use modelator::artifact::{TlaFile, TlaConfigFile};
    /// use modelator::module::Tla;
    /// use modelator::Options;
    /// use std::convert::TryFrom;
    ///
    /// let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
    /// let tla_config_file = "tests/integration/tla/Numbers.cfg";
    /// let tla_tests_file = TlaFile::try_from(tla_tests_file).unwrap();
    /// let tla_config_file = TlaConfigFile::try_from(tla_config_file).unwrap();
    /// let mut tests = Tla::generate_tests(tla_tests_file, tla_config_file).unwrap();
    /// println!("{:?}", tests);
    /// ```
    pub fn generate_tests(
        tla_tests_file: TlaFile,
        tla_config_file: TlaConfigFile,
    ) -> Result<Vec<(TlaFile, TlaConfigFile)>, Error> {
        tracing::debug!("Tla::generate_tests {} {}", tla_tests_file, tla_config_file);

        // compute the directory in which the tla tests file is stored
        let mut tla_tests_dir = tla_tests_file.path().clone();
        assert!(tla_tests_dir.pop());

        // compute tla tests module name: it's safe to unwrap because we have
        // already checked that the tests file is indeed a file
        let tla_tests_module_name = tla_tests_file.tla_module_name().unwrap();

        // retrieve test names from tla tests file
        let test_names = extract_test_names(&tla_tests_file)?;

        // check if no test was found
        if test_names.is_empty() {
            return Err(Error::NoTestFound(tla_tests_file.path().to_path_buf()));
        }

        // generate a tla test file and config for each test name found
        test_names
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
    let content = std::fs::read_to_string(tla_test_file.path())?;
    let test_names = content
        .lines()
        .filter_map(|line| {
            // take the first element in the split
            line.trim().split("==").next()
        })
        .filter_map(|name| {
            let name = name.trim();
            // consider this as a test name if:
            // - it starts/ends Test
            // - it's not commented out
            let is_test = name.starts_with("Test") || name.ends_with("Test");
            let is_commented_out = name.starts_with("\\*") || name.starts_with("(*");
            if is_test && !is_commented_out {
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
    tla_tests_dir: &Path,
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
    std::fs::write(&test_module_file, test_module)?;

    // write test config to test config file
    let test_config_file = tla_tests_dir.join(format!("{}.cfg", test_module_name));
    std::fs::write(&test_config_file, test_config)?;

    // create tla file and tla config file
    use std::convert::TryFrom;
    let test_module_file = TlaFile::try_from(test_module_file)?;
    let test_config_file = TlaConfigFile::try_from(test_config_file)?;
    Ok((test_module_file, test_config_file))
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
    let tla_config = std::fs::read_to_string(tla_config_file.path())?;
    Ok(format!(
        r#"
{}
INVARIANT {}
"#,
        tla_config, invariant
    ))
}
