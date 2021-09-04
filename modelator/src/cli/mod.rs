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
use clap::{AppSettings, ArgSettings, Clap, Subcommand, ValueHint, ArgEnum};
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
    /// Checker name
    #[clap(short, long, possible_values = &["apalache", "tlc"], default_value = "apalache")]
    model_checker: ModelChecker,
    /// test name
    #[clap(short, long, arg_enum, default_value = "json")]
    format: OutputFormat,
    /// TLA+ file with test cases.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_module: PathBuf,
    /// TLA+ config file with CONSTANTS, INIT and NEXT.
    #[clap(parse(from_os_str), value_hint = ValueHint::FilePath)]
    tla_config: PathBuf,
}

impl TraceCli {
    fn run(&self) -> Result<JsonValue, Error> {
        let runtime = crate::ModelatorRuntime::default();

        let file_suite =
            TlaFileSuite::from_tla_and_config_paths(&self.tla_module, &self.tla_config)?;
        let test_names = crate::model::language::Tla::extract_test_names(&file_suite);

        let resp = test_names
            .into_iter()
            .filter(|test_name| allow_test_name(test_name, &self.test))
            .map(|test_name| {
                let input_artifacts =
                    crate::model::language::Tla::generate_test(&test_name, &file_suite)?;
                let res = {
                    let mut ret = match self.model_checker {
                        ModelChecker::Apalache => {
                            crate::model::checker::Apalache::test(&input_artifacts, &runtime)?
                        }
                        ModelChecker::Tlc => {
                            crate::model::checker::Tlc::test(&input_artifacts, &runtime)?
                        }
                    };
                    ret.0.extends_module_name =
                        Some(input_artifacts.tla_file.module_name().to_string());
                    ret
                };
                tracing::debug!("Apalache::test output {}", res.0);

                match self.format {
                    OutputFormat::Json => {
                        let json_trace =
                            crate::model::language::Tla::tla_trace_to_json_trace(res.0)?;
                        tracing::debug!("Tla::tla_trace_to_json_trace output {}", json_trace);
                        write_json_trace_to_file(
                            input_artifacts.tla_file.module_name(),
                            &json_trace,
                        )
                    }
                    OutputFormat::Tla => {
                        write_tla_trace_to_file(input_artifacts.tla_file.module_name(), &res.0)
                    }
                }
            })
            .collect::<Result<Vec<JsonValue>, _>>()?;

        Ok(json!(resp))
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
#[clap(name = crate_name!(), author, about, version)]
#[clap(setting = AppSettings::ColoredHelp, setting = AppSettings::InferSubcommands)]
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
    // The parsed file is a TLA+ module with the same module name as the passed input module.
    // Therefore we provide another name for the output.
    let name = format!("{}Parsed.tla", tla_file.module_name());
    let path = Path::new(&name);
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
