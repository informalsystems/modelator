/// Parsing of TLC's output.
mod output;

use crate::artifact::{TlaConfigFile, TlaFile, TlaTrace};
use crate::{jar, Error, ModelCheckerWorkers, Options};
use std::path::Path;
use std::process::Command;

// #[modelator::module]
pub struct Tlc;

impl Tlc {
    // #[modelator::method]
    pub fn test(
        tla_file: TlaFile,
        tla_config_file: TlaConfigFile,
        options: &Options,
    ) -> Result<TlaTrace, Error> {
        tracing::debug!("Tlc::test {} {} {:?}", tla_file, tla_config_file, options);

        // check java and its version
        crate::util::check_java_version()?;

        // create tlc command
        let mut cmd = test_cmd(tla_file.path(), tla_config_file.path(), options);

        // start tlc
        // TODO: add timeout
        let output = cmd.output().map_err(Error::io)?;

        // get tlc stdout and stderr
        let stdout = crate::util::cmd_output_to_string(&output.stdout);
        let stderr = crate::util::cmd_output_to_string(&output.stderr);
        tracing::debug!("TLC stdout:\n{}", stdout);
        tracing::debug!("TLC stderr:\n{}", stderr);

        match (stdout.is_empty(), stderr.is_empty()) {
            (false, true) => {
                // if stderr is empty, but the stdout is not, then no error has
                // occurred

                // save tlc log
                std::fs::write(&options.model_checker_options.log, &stdout).map_err(Error::io)?;
                tracing::debug!(
                    "TLC log written to {}",
                    crate::util::absolute_path(&options.model_checker_options.log)
                );

                // remove tlc 'states' folder. on each run, tlc creates a new folder
                // inside the 'states' folder named using the current date with a
                // second precision (e.g. 'states/21-03-04-16-42-04'). if we happen
                // to run tlc twice in the same second, tlc fails when trying to
                // create this folder for the second time. we avoid this problem by
                // simply removing the parent folder 'states' after every tlc run
                // compute the directory in which the tla tests file is stored
                let states_dir = if tla_file.path().is_absolute() {
                    // if the tla file passed as input to TLC is an absolute
                    // path, then TLC creates the 'states' directory in the same
                    // directory as the tla file
                    let mut tla_dir = tla_file.path().clone();
                    assert!(tla_dir.pop());
                    tla_dir.join("states")
                } else {
                    // otherwise, it creates the 'states' directory in the
                    // current directory
                    Path::new("states").to_path_buf()
                };
                tracing::debug!(
                    "removing TLC directory: {:?}",
                    crate::util::absolute_path(&states_dir)
                );
                std::fs::remove_dir_all(states_dir).map_err(Error::io)?;

                // convert tlc output to traces
                let mut traces = output::parse(stdout, &options.model_checker_options)?;

                // check if no trace was found
                if traces.is_empty() {
                    return Err(Error::NoTraceFound(
                        options.model_checker_options.log.clone(),
                    ));
                }

                // at most one trace should have been found
                assert_eq!(
                    traces.len(),
                    1,
                    "[modelator] unexpected number of traces in TLC's log"
                );
                Ok(traces.pop().unwrap())
            }
            (true, false) => {
                // if stdout is empty, but the stderr is not, return an error
                Err(Error::TLCFailure(stderr))
            }
            _ => {
                panic!("[modelator] unexpected TLC's stdout/stderr combination")
            }
        }
    }
}

fn test_cmd<P: AsRef<Path>>(tla_file: P, tla_config_file: P, options: &Options) -> Command {
    let tla2tools = jar::Jar::Tla.file(&options.dir);
    let community_modules = jar::Jar::CommunityModules.file(&options.dir);

    let mut cmd = Command::new("java");
    cmd
        // set classpath
        .arg("-cp")
        .arg(format!(
            "{}:{}",
            tla2tools.as_path().to_string_lossy(),
            community_modules.as_path().to_string_lossy(),
        ))
        // set tla file
        .arg("tlc2.TLC")
        .arg(tla_file.as_ref())
        // set tla config file
        .arg("-config")
        .arg(tla_config_file.as_ref())
        // set "-tool" flag, which allows easier parsing of TLC's output
        .arg("-tool")
        // set the number of TLC's workers
        .arg("-workers")
        .arg(workers(options));

    // show command being run
    tracing::debug!("{}", crate::util::cmd_show(&cmd));
    cmd
}

fn workers(options: &Options) -> String {
    match options.model_checker_options.workers {
        ModelCheckerWorkers::Auto => "auto".to_string(),
        ModelCheckerWorkers::Count(count) => count.to_string(),
    }
}
