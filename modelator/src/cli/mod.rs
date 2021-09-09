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
use clap::{AppSettings, ArgEnum, ArgSettings, Clap, Subcommand, ValueHint};
use serde_json::{json, Value as JsonValue};
use std::path::Path;

/// Re-exports.
pub use output::{CliOutput, CliStatus};

/// Parse TLA+ files with Apalache.
#[derive(Debug, Clap)]
#[clap(setting = AppSettings::ColoredHelp)]
pub struct ParseCli {
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
}

impl ParseCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = crate::ModelatorRuntime::default();
        let tla_file = TlaFileSuite::from_tla_path(&self.tla_module)?;
        let res = crate::model::checker::Apalache::parse(&tla_file, &runtime)?;
        tracing::debug!("Apalache::parse output {}", res.0);
        write_parsed_tla_file_to_file(&res.0)
    }
}

/// Parse TLA+ files with Apalache.
#[derive(Debug, Clap)]
#[clap(setting = AppSettings::ColoredHelp)]
pub struct TestListCli {
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
}

impl TestListCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let tla_file = TlaFileSuite::from_tla_path(&self.tla_module)?;
        let tests = crate::model::language::Tla::extract_test_names(&tla_file);
        tracing::debug!("Tla::extract_test_names output {:?}", &tests);
        Ok(json!(tests))
    }
}

/// Test models with Apalache/TLC
#[derive(Debug, Clap)]
#[clap(setting = AppSettings::ColoredHelp)]
pub struct TraceCli {
    /// test name
    #[clap(short, long, default_value = "@all")]
    test: String,
    /// TODO: derive ArgEnum for ModelChecker enum
    /// Checker name
    #[clap(short, long, possible_values = &["apalache", "tlc"], default_value = "apalache")]
    model_checker: ModelChecker,
    /// output format
    #[clap(short, long, arg_enum, default_value = "json")]
    format: OutputFormat,
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
    /// TLA+ config file with CONSTANTS, INIT and NEXT.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_config: PathBuf,
    /// The number of traces to generate for a single test.
    #[clap(long)]
    num_traces: i32,
}

impl TraceCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = {
            let mut runtime = crate::ModelatorRuntime::default();
            runtime.model_checker_runtime.traces_per_test = self.num_traces;
            runtime
        };

        let file_suite =
            TlaFileSuite::from_tla_and_config_paths(&self.tla_module, &self.tla_config)?;

        let test_names = crate::model::language::Tla::extract_test_names(&file_suite)
            .into_iter()
            .filter(|test_name| allow_test_name(test_name, &self.test));

        let mut res: BTreeMap<String, Result<Vec<JsonValue>, Error>> = BTreeMap::new();

        for test_name in test_names {
            // Create the intermediary file suite to run a single test
            let input_artifacts =
                crate::model::language::Tla::generate_test(&test_name, &file_suite)?;

            // Model check the test and collect traces
            let traces = {
                let mut traces = match self.model_checker {
                    ModelChecker::Apalache => {
                        crate::model::checker::Apalache::test(&input_artifacts, &runtime)?
                    }
                    ModelChecker::Tlc => {
                        crate::model::checker::Tlc::test(&input_artifacts, &runtime)?
                    }
                }
                .0;
                for test in traces.iter_mut() {
                    test.extends_module_name =
                        Some(input_artifacts.tla_file.module_name().to_string());
                }
                traces
            };

            // Convert each trace to json
            let trace_write_results: Result<Vec<JsonValue>, Error> = traces
                .into_iter()
                .enumerate()
                .map(|(i, trace)| {
                    let write_file_name =
                        format!("{}{}", input_artifacts.tla_file.module_name(), i);
                    match self.format {
                        OutputFormat::Json => {
                            let json_trace =
                                crate::model::language::Tla::tla_trace_to_json_trace(trace)?;
                            tracing::debug!("Tla::tla_trace_to_json_trace output {}", json_trace);
                            write_json_trace_to_file(&write_file_name, &json_trace)
                        }
                        OutputFormat::Tla => write_tla_trace_to_file(&write_file_name, &trace),
                    }
                })
                .collect();

            res.insert(test_name, trace_write_results);
        }

        Ok(json!(res))
    }
}

#[derive(Clap, Debug)]
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
        // setup modelator
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
#[derive(Clap, Debug)]
#[clap(
    name = crate_name!(),
    author,
    about,
    version,
    setting = AppSettings::ColoredHelp,
    setting = AppSettings::InferSubcommands
)]
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

#[derive(Debug, ArgEnum)]
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
    let path = Path::new(tla_file.module_name());
    tla_file.try_write_to_file(path)?;
    Ok(json!({
        "tla_file": crate::util::absolute_path(path),
    }))
}

fn write_tla_trace_to_file(test_name: &str, tla_trace: &TlaTrace) -> Result<JsonValue, Error> {
    // TODO: hardcoded!
    let file_name = format!("trace_{}.tla", test_name);
    let path = Path::new(&file_name);
    tla_trace.try_write_to_file(path)?;
    Ok(json!({
        "tla_trace_file": crate::util::absolute_path(&path),
    }))
}

fn write_json_trace_to_file(test_name: &str, json_trace: &JsonTrace) -> Result<JsonValue, Error> {
    // TODO: hardcoded!
    let file_name = format!("trace_{}.json", test_name);
    let path = Path::new(&file_name);
    json_trace.try_write_to_file(path)?;
    Ok(json!({
        "json_trace_file": crate::util::absolute_path(&path),
    }))
}
