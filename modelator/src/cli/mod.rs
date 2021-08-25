// CLI output.
pub(crate) mod output;

use crate::artifact::{Artifact, JsonTrace, TlaConfigFile, TlaFile, TlaTrace};
use crate::Error;
use clap::{AppSettings, Clap, Subcommand};
use serde_json::{json, Value as JsonValue};
use std::path::Path;

/// A struct that generates a CLI for `modelator` using [`clap`].
#[derive(Clap, Debug)]
#[clap(name = "modelator")]
#[clap(setting = AppSettings::DisableHelpSubcommand)]
pub struct CliOptions {
    #[clap(subcommand)]
    subcommand: Modules,
}

#[derive(Debug, Subcommand)]
enum Modules {
    /// Generate TLA+ test cases and parse TLA+ traces.
    #[clap(subcommand)]
    Tla(TlaMethods),
    /// Generate TLA+ traces using Apalache.
    #[clap(subcommand)]
    Apalache(ApalacheMethods),
    /// Generate TLA+ traces using TLC.
    #[clap(subcommand)]
    Tlc(TlcMethods),
}

#[derive(Debug, Subcommand)]
#[clap(setting = AppSettings::DisableHelpSubcommand)]
enum TlaMethods {
    /// Generate TLA+ tests.
    GenerateTests {
        /// TLA+ file with test cases.
        tla_file: String,
        /// TLA+ config file with CONSTANTS, INIT and NEXT.
        tla_config_file: String,
    },
    /// Convert a TLA+ trace to a JSON trace.
    TlaTraceToJsonTrace {
        /// File with a TLA+ trace produced by the Apalache or TLC modules.
        tla_trace_file: String,
    },
}

#[derive(Debug, Subcommand)]
#[clap(setting = AppSettings::DisableHelpSubcommand)]
enum ApalacheMethods {
    /// Generate TLA+ trace from a TLA+ test.
    Test {
        /// TLA+ file generated by the generate-test method in the TLA module.
        tla_file: String,
        /// TLA+ config file generated by the generate-test method in the TLA module.
        tla_config_file: String,
    },
    /// Parse a TLA+ file.
    Parse {
        /// TLA+ file to be parsed.
        tla_file: String,
    },
}

#[derive(Debug, Subcommand)]
#[clap(setting = AppSettings::DisableHelpSubcommand)]
enum TlcMethods {
    /// Generate TLA+ trace from a TLA+ test.
    Test {
        /// TLA+ file generated by the generate-test method in the TLA module.
        tla_file: String,
        /// TLA+ config file generated by the generate-test method in the TLA module.
        tla_config_file: String,
    },
}

impl CliOptions {
    /// Function that runs `modelator` given the parameters in the [CliOptions].
    pub fn run(self) -> output::CliOutput {
        let result = self.subcommand.run();
        output::CliOutput::with_result(result)
    }
}

impl Modules {
    fn run(self) -> Result<JsonValue, Error> {
        // setup modelator
        let options = crate::Options::default();
        crate::setup(&options)?;

        // run the subcommand
        match self {
            Self::Tla(options) => options.run(),
            Self::Apalache(options) => options.run(),
            Self::Tlc(options) => options.run(),
        }
    }
}

impl TlaMethods {
    fn run(self) -> Result<JsonValue, Error> {
        match self {
            Self::GenerateTests {
                tla_file,
                tla_config_file,
            } => Self::generate_tests(tla_file, tla_config_file),
            Self::TlaTraceToJsonTrace { tla_trace_file } => {
                Self::tla_trace_to_json_trace(tla_trace_file)
            }
        }
    }

    fn generate_tests(
        tla_file_path: String,
        tla_config_file_path: String,
    ) -> Result<JsonValue, Error> {
        use std::convert::TryFrom;
        let tla_file = TlaFile::try_from(tla_file_path)?;
        let tla_config_file = TlaConfigFile::try_from(tla_config_file_path)?;
        let tests = crate::module::Tla::generate_tests(tla_file, tla_config_file)?;
        tracing::debug!("Tla::generate_tests output {:#?}", tests);

        json_list_generated_tests(tests)
    }

    fn tla_trace_to_json_trace(tla_trace_file: String) -> Result<JsonValue, Error> {
        // parse tla trace
        let tla_trace_file = Path::new(&tla_trace_file);
        if !tla_trace_file.is_file() {
            return Err(Error::FileNotFound(tla_trace_file.to_path_buf()));
        }
        let tla_trace = std::fs::read_to_string(&tla_trace_file)?.parse()?;

        let json_trace = crate::module::Tla::tla_trace_to_json_trace(tla_trace)?;
        tracing::debug!("Tla::tla_trace_to_json_trace output {}", json_trace);

        write_json_trace_to_file(json_trace)
    }
}

impl ApalacheMethods {
    fn run(self) -> Result<JsonValue, Error> {
        match self {
            Self::Test {
                tla_file,
                tla_config_file,
            } => Self::test(tla_file, tla_config_file),
            Self::Parse { tla_file } => Self::parse(tla_file),
        }
    }

    fn test(tla_file_path: String, tla_config_file_path: String) -> Result<JsonValue, Error> {
        let options = crate::Options::default();
        use std::convert::TryFrom;
        let tla_file = TlaFile::try_from(tla_file_path)?;
        let tla_config_file = TlaConfigFile::try_from(tla_config_file_path)?;
        let tla_trace = {
            let mut ret = crate::module::Apalache::test(&tla_file, &tla_config_file, &options)?;
            ret.extends_module_name = Some(tla_file.file_name().to_string());
            ret
        };
        tracing::debug!("Apalache::test output {}", tla_trace);
        write_tla_trace_to_file(tla_trace)
    }

    fn parse(tla_file: String) -> Result<JsonValue, Error> {
        let options = crate::Options::default();
        use std::convert::TryFrom;
        let tla_file = TlaFile::try_from(tla_file)?;
        let tla_file_parsed = crate::module::Apalache::parse(tla_file, &options)?;
        tracing::debug!("Apalache::parse output {}", tla_file_parsed);

        parsed_tla_file(tla_file_parsed)
    }
}

impl TlcMethods {
    fn run(self) -> Result<JsonValue, Error> {
        match self {
            Self::Test {
                tla_file,
                tla_config_file,
            } => Self::test(tla_file, tla_config_file),
        }
    }

    fn test(tla_file_path: String, tla_config_file_path: String) -> Result<JsonValue, Error> {
        let options = crate::Options::default();
        use std::convert::TryFrom;
        let tla_file = TlaFile::try_from(tla_file_path)?;
        let tla_config_file = TlaConfigFile::try_from(tla_config_file_path)?;
        let tla_trace = {
            let mut ret = crate::module::Tlc::test(&tla_file, &tla_config_file, &options)?;
            ret.extends_module_name = Some(tla_file.file_name().to_string());
            ret
        };
        tracing::debug!("Tlc::test output {}", tla_trace);
        write_tla_trace_to_file(tla_trace)
    }
}

#[allow(clippy::unnecessary_wraps)]
fn json_list_generated_tests(tests: Vec<(TlaFile, TlaConfigFile)>) -> Result<JsonValue, Error> {
    let json_array_entry = |tla_file: TlaFile, tla_config_file: TlaConfigFile| {
        json!({
            "tla_file": format!("{}", tla_file),
            "tla_config_file": format!("{}", tla_config_file),
        })
    };
    let json_array = tests
        .into_iter()
        .map(|(tla_file, tla_config_file)| json_array_entry(tla_file, tla_config_file))
        .collect();
    Ok(JsonValue::Array(json_array))
}

fn write_tla_trace_to_file(tla_trace: TlaTrace) -> Result<JsonValue, Error> {
    // TODO: hardcoded!
    let path = Path::new("trace.tla");
    tla_trace.try_write_to_file(path)?;
    Ok(json!({
        "tla_trace_file": crate::util::absolute_path(&path),
    }))
}

fn write_json_trace_to_file(json_trace: JsonTrace) -> Result<JsonValue, Error> {
    // TODO: hardcoded!
    let path = Path::new("trace.json");
    json_trace.try_write_to_file(path)?;
    Ok(json!({
        "json_trace_file": crate::util::absolute_path(&path),
    }))
}

#[allow(clippy::unnecessary_wraps)]
fn parsed_tla_file(tla_file_parsed: TlaFile) -> Result<JsonValue, Error> {
    Ok(json!({
        "tla_file": format!("{}", tla_file_parsed),
    }))
}
