/// Conversion from TLA traces to JSON.
mod json;

use crate::artifact::{Artifact, JsonTrace, TlaConfigFile, TlaFile, TlaTrace};
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

        let tla_tests_module_name = tla_tests_file.module_name();

        // retrieve test names from tla tests file
        let test_names = extract_test_names(tla_tests_file.file_contents_backing())?;

        tracing::debug!(
            "test names extracted from {}:\n{:?}",
            tla_tests_file,
            test_names
        );

        // check if no test was found
        if test_names.is_empty() {
            return Err(Error::NoTestFound(tla_tests_file.module_name().to_string()));
        }

        // generate a tla test file and config for each test name found
        test_names
            .into_iter()
            .map(|test_name| generate_test(tla_tests_module_name, &test_name, &tla_config_file))
            .collect()
    }
}

fn extract_test_names(tla_tests_file_content: &str) -> Result<Vec<String>, Error> {
    //TODO: Error is never returned here so why type it
    let test_names = tla_tests_file_content
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

    Ok(test_names)
}

fn generate_test(
    tla_tests_file_name: &str,
    test_name: &str,
    tla_config_file: &TlaConfigFile,
) -> Result<(TlaFile, TlaConfigFile), Error> {
    // TODO: it would be better to separate logic from IO steps
    // split into 2 funs and also use artifacts:
    // instead of writing the files and reading artifacts from them,
    // create the artifacts and write the files
    let test_module_name = format!("{}_{}", tla_tests_file_name, test_name);
    let negated_test_name = format!("{}Neg", test_name);

    // create tla module where the test is negated
    let test_module = generate_test_module(
        &test_module_name,
        tla_tests_file_name,
        &negated_test_name,
        test_name,
    );
    // create test config with negated test as an invariant
    let test_config = generate_test_config(tla_config_file.content(), &negated_test_name)?;

    //TODO: make temp dir

    // write test module to test module file
    let test_module_file = tla_tests_file_dir.join(format!("{}.tla", test_module_name));
    std::fs::write(&test_module_file, test_module)?;

    // write test config to test config file
    let test_config_file = tla_tests_file_dir.join(format!("{}.cfg", test_module_name));
    std::fs::write(&test_config_file, test_config)?;

    // create tla file and tla config file
    use std::convert::TryFrom;
    let test_module_file = TlaFile::try_read_from_file(test_module_file)?;
    let test_config_file = TlaConfigFile::try_read_from_file(test_config_file)?;
    Ok((test_module_file, test_config_file))
}

fn generate_test_module(
    module_name: &str,
    file_to_extend: &str,
    negated_test_name: &str,
    test_name: &str,
) -> String {
    format!(
        r#"
---------- MODULE {} ----------

EXTENDS {}

{} == ~{}

===============================
"#,
        module_name, file_to_extend, negated_test_name, test_name
    )
}

fn generate_test_config(tla_config_file_content: &str, invariant: &str) -> Result<String, Error> {
    Ok(format!(
        r#"
{}
INVARIANT {}
"#,
        tla_config_file_content, invariant
    ))
}
