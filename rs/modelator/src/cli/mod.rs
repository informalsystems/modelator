use std::collections::BTreeMap;
use std::env;
use std::fmt::write;
use std::path::PathBuf;
use std::str::FromStr;
// CLI output.
pub(crate) mod output;

#[warn(dead_code, unused)]
use crate::artifact::{Artifact, JsonTrace, TlaFile, TlaFileSuite, TlaTrace};
use crate::model::checker::ModelChecker;
use crate::Error;
use clap::{crate_authors, crate_description, crate_license, crate_name, crate_version};
use clap::{AppSettings, ArgEnum, ArgSettings, ColorChoice, Parser, Subcommand, ValueHint};
use serde_json::{json, Value as JsonValue};
use std::path::Path;

/// Re-exports.
pub use output::{CliOutput, CliStatus};

/// Parse TLA+ files with Apalache.
#[derive(Debug, Parser)]
#[clap(color = ColorChoice::Auto)]
pub struct ParseCli {
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
    /// Whether or not to write the output file
    #[clap(long)]
    write: bool,
}

impl ParseCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = crate::ModelatorRuntime::default();
        let tla_file = TlaFileSuite::from_tla_path(&self.tla_module)?;
        let res = crate::model::checker::Apalache::parse(&tla_file, &runtime)?;
        tracing::debug!("Apalache::parse output {}", res.0);
        if self.write {
            write_parsed_tla_file_to_file(&res.0)
        } else {
            Ok(json!({
                "tla_file_content": res.0.as_string(),
            }))
        }
    }
}

#[derive(Debug, Parser)]
/// List the tests in a TLA file
pub struct TestListCli {
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
}

impl TestListCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let tla_file_suite = TlaFileSuite::from_tla_path(&self.tla_module)?;
        let tests = crate::model::language::Tla::extract_test_names(
            tla_file_suite.tla_file.file_contents_backing(),
        )
        .and_then(|names| {
            if names.is_empty() {
                Err(Error::NoTestFound(
                    tla_file_suite.tla_file.module_name().into(),
                ))
            } else {
                Ok(names)
            }
        })?;
        tracing::debug!("Tla::extract_test_names output {:?}", &tests);
        Ok(json!(tests))
    }
}

/// Test models with Apalache/TLC
#[derive(Debug, Parser)]
#[clap(color = ColorChoice::Auto)]
pub struct TraceCli {
    /// test name
    #[clap(short, long, default_value = "@all")]
    test: String,
    // TODO: derive ArgEnum for ModelChecker enum
    /// Checker name
    #[clap(short, long, possible_values = &["apalache", "tlc"], default_value = "apalache")]
    model_checker: ModelChecker,
    /// output format
    #[clap(short, long, arg_enum, default_value = "json")]
    format: OutputFormat,
    /// The maximum number of traces to generate for a single test.
    #[clap(short, long, default_value = "1")]
    num_traces: usize,
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
    /// TLA+ config file with CONSTANTS, INIT and NEXT.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_config: PathBuf,
    /// Whether or not to write output files
    #[clap(long)]
    write: bool,
}

impl TraceCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = {
            let mut runtime = crate::ModelatorRuntime::default();
            runtime.model_checker_runtime.traces_per_test = self.num_traces;
            runtime
        };

        let tla_file_suite =
            TlaFileSuite::from_tla_and_config_paths(&self.tla_module, &self.tla_config)?;

        let test_names: Vec<String> = crate::model::language::Tla::extract_test_names(
            tla_file_suite.tla_file.file_contents_backing(),
        )?
        .into_iter()
        .filter(|test_name| allow_test_name(test_name, &self.test))
        .collect();

        if test_names.is_empty() {
            return Err(Error::NoTestFound(format!(
                "No test found in {}. [tla module name: {}, test pattern: {}]",
                tla_file_suite.tla_file.module_name(),
                tla_file_suite.tla_file.module_name(),
                &self.test
            )));
        };

        let test_results = test_names
            .iter()
            .map(|test_name| {
                // Create the intermediary file suite to run a single test
                let input_artifacts =
                    crate::model::language::Tla::generate_test(test_name, &tla_file_suite)?;

                // Model check the test and collect traces
                let mut traces = match self.model_checker {
                    ModelChecker::Apalache => {
                        crate::model::checker::Apalache::test(&input_artifacts, &runtime)?
                    }
                    ModelChecker::Tlc => {
                        crate::model::checker::Tlc::test(&input_artifacts, &runtime)?
                    }
                }
                .0; // Ignores returned stdout

                if traces.len() < self.num_traces {
                    return Err(Error::LessNumberOfTracesFound(traces.len()));
                }

                traces.iter_mut().for_each(|trace| {
                    trace.extends_module_name =
                        Some(input_artifacts.tla_file.module_name().to_string());
                });

                // Write each trace and get a result containing json information
                traces
                    .into_iter()
                    .enumerate()
                    .map(|(i, trace)| {
                        let file_name_to_write =
                            format!("{}{}", input_artifacts.tla_file.module_name(), i);
                        match self.format {
                            OutputFormat::Json => {
                                let json_trace =
                                    crate::model::language::Tla::tla_trace_to_json_trace(trace)?;
                                tracing::debug!(
                                    "Tla::tla_trace_to_json_trace output {}",
                                    json_trace
                                );
                                if self.write {
                                    write_json_trace_to_file(&file_name_to_write, &json_trace)
                                } else {
                                    Ok(json!({
                                        "json_trace_content": json_trace.states
                                    }))
                                }
                            }
                            OutputFormat::Tla => {
                                if self.write {
                                    write_tla_trace_to_file(&file_name_to_write, &trace)
                                } else {
                                    Ok(json!({
                                        "tla_trace_content": trace.states
                                    }))
                                }
                            }
                        }
                    })
                    .collect::<Result<Vec<_>, Error>>()
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let res = test_names
            .iter()
            .cloned()
            .zip(test_results)
            .collect::<BTreeMap<String, Vec<JsonValue>>>();

        Ok(json!(res))
    }
}

#[derive(Parser, Debug)]
enum Module {
    /// Parse TLA+ files.
    Parse(ParseCli),
    /// Extract test names from tla file
    List(TestListCli),
    /// Generate TLA+ traces using model checker.
    Trace(TraceCli),
}

impl Module {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = crate::ModelatorRuntime::default();
        runtime.setup()?;

        match self {
            Self::Parse(parse_cli) => parse_cli.run(),
            Self::List(testlist_cli) => testlist_cli.run(),
            Self::Trace(trace_cli) => trace_cli.run(),
        }
    }
}

/// A struct that generates a CLI for `modelator` using [`clap`].
#[derive(Parser, Debug)]
#[clap(
    name = crate_name!(),
    author,
    about,
    version,
    setting = AppSettings::InferSubcommands
)]
#[clap(color = ColorChoice::Auto)]
pub struct App {
    #[clap(subcommand)]
    module: Module,
}
impl App {
    /// The top cli arg handler
    pub fn run(&self) -> CliOutput {
        CliOutput::with_result(self.module.run())
    }
}

#[derive(Debug, Clone, ArgEnum)]
enum OutputFormat {
    Tla,
    Json,
}

fn allow_test_name(test_name: &str, pattern: &str) -> bool {
    if pattern.to_ascii_lowercase() == "@all" {
        true
    } else {
        // TODO: add regex pattern
        test_name == pattern
    }
}

fn json_list_generated_tests(test_files: Vec<(PathBuf, PathBuf)>) -> Result<JsonValue, Error> {
    let json_array = test_files
        .into_iter()
        .map(|(tla, cfg)| {
            json!({
                "tla_file": tla.into_os_string().into_string().unwrap(),
                "tla_config_file": cfg.into_os_string().into_string().unwrap()
            })
        })
        .collect();
    Ok(JsonValue::Array(json_array))
}

fn write_parsed_tla_file_to_file(tla_file: &TlaFile) -> Result<JsonValue, Error> {
    // Apalache changes the module name in the output file so we use it directly here.
    let file_name = format!("{}.tla", tla_file.module_name());
    let path = Path::new(&file_name);
    tla_file.try_write_to_file(path)?;
    Ok(json!({
        "tla_filepath": crate::util::absolute_path(path),
    }))
}

fn write_tla_trace_to_file(test_name: &str, tla_trace: &TlaTrace) -> Result<JsonValue, Error> {
    let file_name = format!("trace_{}.tla", test_name);
    let path = Path::new(&file_name);
    tla_trace.try_write_to_file(path)?;
    Ok(json!({
        "tla_trace_filepath": crate::util::absolute_path(&path),
    }))
}

fn write_json_trace_to_file(test_name: &str, json_trace: &JsonTrace) -> Result<JsonValue, Error> {
    let file_name = format!("trace_{}.json", test_name);
    let path = Path::new(&file_name);
    json_trace.try_write_to_file(path)?;
    Ok(json!({
        "json_trace_filepath": crate::util::absolute_path(&path),
    }))
}
