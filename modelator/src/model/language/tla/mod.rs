use lazy_static::lazy_static;
use regex::Regex;
/// Conversion from TLA traces to JSON.
mod json;

use crate::artifact::{
    tla_file, Artifact, ArtifactCreator, JsonTrace, TlaConfigFile, TlaFile, TlaFileSuite, TlaTrace,
};
use crate::model::language::tla;
use crate::Error;
use serde_json::Value as JsonValue;
use std::path::Path;

/// `modelator`'s TLA module.
#[derive(Debug, Clone, Copy)]
pub struct Tla;

pub struct TlaTest {
    pub file_suite: TlaFileSuite,
    pub name: String,
}

impl Tla {
    /// Convert a [`TlaTrace`] into a [`JsonTrace`].
    ///
    /// # Examples
    /// ```ignore
    /// use modelator::artifact::TlaFileSuite;
    /// use modelator::model::{language::Tla, checker::Tlc};
    /// use modelator::ModelatorRuntime;
    /// use std::convert::TryFrom;
    ///
    /// let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
    /// let tla_config_file = "tests/integration/tla/Numbers.cfg";
    /// let tla_suite = TlaFileSuite::from_tla_and_config_paths(tla_tests_file, tla_config_file).unwrap();
    ///
    /// let mut tests = Tla::generate_tests(&tla_suite).unwrap();
    /// let test_tla_suite = tests.pop().unwrap();
    /// let runtime = ModelatorRuntime::default();
    /// let (tla_trace, _) = Tlc::test(&test_tla_suite, &runtime).unwrap();
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

    /// Generate TLA+ test and config files given a [`TlaFile`] containing TLA+
    /// test assertions and a [`TlaConfigFile`].
    ///
    /// # Examples
    /// ```ignore
    /// use modelator::artifact::TlaFileSuite;
    /// use modelator::model::language::Tla;
    /// use std::convert::TryFrom;
    ///
    /// let tla_tests_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
    /// let tla_config_file = "tests/integration/tla/Numbers.cfg";
    /// let tla_suite = TlaFileSuite::from_tla_and_config_paths(tla_tests_file, tla_config_file).unwrap();
    /// let mut tests = Tla::generate_tests(&tla_suite).unwrap();
    /// println!("{:?}", tests);
    /// ```
    pub fn generate_tests(tla_file_suite: &TlaFileSuite) -> Result<Vec<TlaTest>, Error> {
        tracing::debug!(
            "Tla::generate_tests {} {}",
            tla_file_suite.tla_file,
            tla_file_suite.tla_config_file
        );

        let tla_tests_module_name = tla_file_suite.tla_file.module_name();

        // retrieve test names from tla tests file
        let test_names = Self::extract_test_names(tla_file_suite.tla_file.file_contents_backing())?;

        tracing::debug!(
            "test names extracted from {}:\n{:?}",
            tla_file_suite.tla_file,
            test_names
        );

        // check if no test was found
        if test_names.is_empty() {
            return Err(Error::NoTestFound(tla_tests_module_name.to_string()));
        }

        // generate a tla test file and config for each test name found
        test_names
            .into_iter()
            .map(|test_name| {
                Ok(TlaTest {
                    name: test_name.clone(),
                    file_suite: Self::generate_test(&test_name, tla_file_suite)?,
                })
            })
            .collect()
    }

    /// Generate test names from a tla file
    pub fn extract_test_names(content: &str) -> Result<Vec<String>, Error> {
        let names = extract_operator_names(content)?;
        Ok(names
            .iter()
            .filter_map(|name| {
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
            .collect())
    }

    /// Generate test tla file and config for a testname
    pub fn generate_test(
        test_name: &str,
        tla_file_suite: &TlaFileSuite,
    ) -> Result<TlaFileSuite, Error> {
        let tla_tests_file_name = tla_file_suite.tla_file.module_name();
        let test_module_name = format!("{}_{}", tla_tests_file_name, test_name);
        let negated_test_name = format!("{}Neg", test_name);
        let view_operator =
            extract_view_operator(test_name, tla_file_suite.tla_file.file_contents_backing())?;

        // create tla module where the test is negated
        let test_module = generate_test_module(
            &test_module_name,
            tla_tests_file_name,
            &negated_test_name,
            test_name,
            &view_operator,
        );
        // create test config with negated test as an invariant
        let test_config =
            generate_test_config(tla_file_suite.tla_config_file.content(), &negated_test_name);

        let test_module_file = TlaFile::from_string(&test_module)?;
        let mut test_config_file = TlaConfigFile::from_string(&test_config)?;
        test_config_file.set_path(std::path::Path::new(&format!(
            "{}_{}.cfg",
            tla_tests_file_name, test_name
        )));

        let collected = {
            let mut dependencies = tla_file_suite.dependency_tla_files.clone();
            dependencies.push(tla_file_suite.tla_file.clone());
            dependencies
        };

        Ok(TlaFileSuite {
            tla_file: test_module_file,
            tla_config_file: test_config_file,
            dependency_tla_files: collected,
        })
    }
}

/// Returns a list of operator names
fn extract_operator_names(tla_file_contents: &str) -> Result<Vec<String>, Error> {
    let cnt_operators = tla_file_contents.match_indices("==").count();
    lazy_static! {
        // Match '<identifier><whitespace>=='
        static ref RE: Regex = Regex::new(r"([a-zA-Z0-9_]*)\s*==").unwrap();
    }
    let ret: Vec<String> = RE
        .captures_iter(tla_file_contents)
        .filter_map(|caps| caps.get(0))
        .map(|m| m.as_str().to_owned())
        .map(|s| s.trim_end_matches('=').trim().to_owned())
        .collect();

    match ret.len() == cnt_operators {
        true => Ok(ret),
        false => Err(Error::TlaOperatorNameParseError(
            tla_file_contents.to_owned(),
        )),
    }
}

/// Scan the contents of the tla file to try to find an operator named
/// '<test_name>View'. If none is found then use an operator named 'View', if found.
/// If no operator is found then returns None.
fn extract_view_operator(
    test_name: &str,
    tla_file_contents: &str,
) -> Result<Option<String>, Error> {
    let operators = extract_operator_names(tla_file_contents)?;
    Ok(operators.iter().fold(None, |acc, s| -> Option<String> {
        // If the operator is a test specific view then use it
        if *s == format!("{}View", test_name) {
            Some(s.clone())
        }
        // If a test specific view has already been found then use it
        else if acc.is_some() && acc != Some("View".to_owned()) {
            acc
        }
        // Otherwise if a View has been found then use it
        else if s == "View" {
            Some("View".to_owned())
        } else {
            acc
        }
    }))
}

fn generate_test_module(
    module_name: &str,
    file_to_extend: &str,
    negated_test_name: &str,
    test_name: &str,
    // String representing operators which will define a View projection which can be used by Apalache
    // Format `<operator name> == ...`
    view_operator: &Option<String>,
) -> String {
    format!(
        r#"
---------- MODULE {} ----------
EXTENDS {}
{} == ~{}
{}
===============================
"#,
        module_name,
        file_to_extend,
        negated_test_name,
        test_name,
        match view_operator {
            Some(name) => format!("ViewForTestNeg == {}", name),
            _ => "".to_owned(),
        }
    )
}

fn generate_test_config(tla_config_file_content: &str, invariant: &str) -> String {
    format!(
        r#"
{}
INVARIANT {}
"#,
        tla_config_file_content, invariant
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_operator_names() {
        let content = r#"
    My0Op==123
    My1Op == 123
    My2Op
        == 123

      My3Op
        ==
        123
        
My4Op

        ==

        123
        
    My5Op_==123
    _My6Op==123
   My_7Op==123
        "#;
        let expect = vec![
            "My0Op", "My1Op", "My2Op", "My3Op", "My4Op", "My5Op_", "_My6Op", "My_7Op",
        ];
        let res = extract_operator_names(content);
        match res {
            Ok(v) => assert_eq!(expect, v),
            Err(_) => assert!(false),
        };
    }

    #[test]
    fn test_extract_view_name() {
        // Has no view
        {
            let content = r#"
                    MyTest == 123
                    "#;
            let res = extract_view_operator("MyTest", content).unwrap();
            assert_eq!(None, res);
        }

        // Has no specialized view
        {
            let content = r#"
            View == 123
            MyTest == 123
            "#;
            let expect = Some("View".to_owned());
            let res = extract_view_operator("MyTest", content).unwrap();
            assert_eq!(expect, res);
        }

        // Has specialized view
        {
            let content = r#"
            View == 123
            MyTestView == 123
            MyTest == 123
            "#;
            let expect = Some("MyTestView".to_owned());
            let res = extract_view_operator("MyTest", content).unwrap();
            assert_eq!(expect, res);
        }
    }

    #[test]
    fn test_extract_test_names() {
        let content = r#"
    My0Test==123
    My1Test == 123
    My2Test
        == 123

      My3Test
        ==
        123Test
        
My4Test

        ==

        Test123
        
        "#;
        let expect = vec!["My0Test", "My1Test", "My2Test", "My3Test", "My4Test"];
        let res = Tla::extract_test_names(content);
        match res {
            Ok(v) => assert_eq!(expect, v),
            Err(_) => assert!(false),
        };
    }
}
