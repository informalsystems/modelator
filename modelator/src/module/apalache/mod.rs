/// Parsing of Apalache's counterexample file.
mod counterexample;

use crate::artifact::{TlaConfigFile, TlaFile, TlaTrace};
use crate::{jar, Error, Options};
use std::path::Path;
use std::process::Command;

// #[modelator::module]
pub struct Apalache;

impl Apalache {
    // #[modelator::method]
    pub fn test(
        tla_file: TlaFile,
        tla_config_file: TlaConfigFile,
        options: &Options,
    ) -> Result<TlaTrace, Error> {
        tracing::debug!(
            "Apalache::test {} {} {:?}",
            tla_file,
            tla_config_file,
            options
        );
        // create apalache command
        let mut cmd = cmd(tla_file.path(), tla_config_file.path(), options);

        // start apalache
        // TODO: add timeout
        let output = cmd.output().map_err(Error::io)?;

        // get apalache stdout and stderr
        let stdout = crate::util::cmd_output_to_string(&output.stdout);
        let stderr = crate::util::cmd_output_to_string(&output.stderr);
        tracing::debug!("Apalache stdout:\n{}", stdout);
        tracing::debug!("Apalache stderr:\n{}", stderr);

        match (stdout.is_empty(), stderr.is_empty()) {
            (false, true) => {
                // apalache writes all its output to the stdout

                // save apalache log
                std::fs::write(&options.model_checker_options.log, &stdout).map_err(Error::io)?;

                // check if a failure has occurred
                if stdout.contains("EXITCODE: ERROR") {
                    return Err(Error::ApalacheFailure(stdout));
                }
                assert!(
                    stdout.contains("EXITCODE: OK"),
                    "[modelator] unexpected Apalache stdout"
                );

                // convert apalache counterexample to a trace
                let counterexample_path = Path::new("counterexample.tla");
                if counterexample_path.is_file() {
                    let counterexample =
                        std::fs::read_to_string(counterexample_path).map_err(Error::io)?;
                    tracing::debug!("Apalache counterexample:\n{}", counterexample);
                    counterexample::parse(counterexample)
                } else {
                    panic!("[modelator] expected to find Apalache's counterexample.tla file")
                }
            }
            _ => {
                panic!("[modelator] unexpected Apalache's stdout/stderr combination")
            }
        }
    }
}

fn cmd<P: AsRef<Path>>(tla_file: P, tla_config_file: P, options: &Options) -> Command {
    let apalache = jar::Jar::Apalache.file(&options.dir);

    let mut cmd = Command::new("java");

    // compute the directory where the tla file is, so that it can be added as
    // a tla library
    if let Some(tla_file_dir) = tla_file.as_ref().parent() {
        cmd
            // set tla library
            .arg(format!("-DTLA-Library={}", tla_file_dir.to_string_lossy()));
    }
    cmd
        // set jar
        .arg("-jar")
        .arg(format!("{}", apalache.as_path().to_string_lossy()))
        .arg("check")
        // set tla config file
        .arg(format!(
            "--config={}",
            tla_config_file.as_ref().to_string_lossy()
        ))
        // set tla file
        .arg(tla_file.as_ref());

    tracing::warn!(
        "the following workers option was ignored since apalache is single-threaded: {:?}",
        options.model_checker_options.workers
    );

    // show command being run
    tracing::debug!("{}", crate::util::cmd_show(&cmd));
    cmd
}
