/// Parsing of TLC's output.
mod output;

use crate::artifact::{
    tla_file, try_write_to_dir, Artifact, ArtifactCreator, ModelCheckerStdout, TlaConfigFile,
    TlaFile, TlaFileSuite, TlaTrace,
};
use crate::cache::TlaTraceCache;
use crate::{jar, model::checker::ModelCheckerWorkers, Error, ModelatorRuntime};
use std::path::Path;
use std::process::Command;

/// `modelator`'s TLC module.
#[derive(Debug, Clone, Copy)]
pub struct Tlc;

impl Tlc {
    /// TODO: ignoring because of <https://github.com/informalsystems/modelator/issues/47>
    ///
    /// Generate a TLA+ trace given a [TlaFile] and a [TlaConfigFile] produced
    /// by [crate::model::language::Tla::generate_tests].
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
    /// println!("{:?}", tla_trace);
    /// ```
    pub fn test(
        tla_file_suite: &TlaFileSuite,
        options: &ModelatorRuntime,
    ) -> Result<(TlaTrace, ModelCheckerStdout), Error> {
        let tla_file = &tla_file_suite.tla_file;
        let tla_config_file = &tla_file_suite.tla_config_file;
        tracing::debug!("Tlc::test {} {} {:?}", tla_file, tla_config_file, options);

        // TODO: disabling cache for now; see https://github.com/informalsystems/modelator/issues/46
        // load cache and check if the result is cached
        // let mut cache = TlaTraceCache::new(runtime)?;
        // let cache_key = TlaTraceCache::key(&tla_file, &tla_config_file)?;
        // if let Some(value) = cache.get(&cache_key)? {
        //     return Ok(value);
        // }

        let tdir = tempfile::tempdir()?;

        try_write_to_dir(&tdir, tla_file_suite)?;

        // create tlc command
        let mut cmd = test_cmd(
            &tdir,
            tla_file.file_name(),
            tla_config_file.filename(),
            options,
        );

        // start tlc
        // TODO: add timeout
        let output = cmd.output()?;

        // get tlc stdout and stderr
        let stdout = crate::util::cmd_output_to_string(&output.stdout);
        let stderr = crate::util::cmd_output_to_string(&output.stderr);
        tracing::debug!("TLC stdout:\n{}", stdout);
        tracing::debug!("TLC stderr:\n{}", stderr);

        match (stdout.is_empty(), stderr.is_empty()) {
            (false, true) => {
                let tlc_log = ModelCheckerStdout::from_string(&stdout)?;

                let mut traces = output::parse(stdout, &options.model_checker_runtime)?;

                // check if no trace was found
                if traces.is_empty() {
                    return Err(Error::NoTestTraceFound(
                        //TODO: this will have to be changed to reflect new in-memory log
                        options.model_checker_runtime.log.clone(),
                    ));
                }

                // at most one trace should have been found
                assert_eq!(
                    traces.len(),
                    1,
                    "[modelator] unexpected number of traces in TLC's log"
                );
                let trace = traces.pop().unwrap();

                // TODO: disabling cache for now; see https://github.com/informalsystems/modelator/issues/46
                // cache trace and then return it
                //cache.insert(cache_key, &trace)?;
                Ok((trace, tlc_log))
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

fn test_cmd<P: AsRef<Path>>(
    temp_dir: &tempfile::TempDir,
    tla_file: P,
    tla_config_file_path: P,
    runtime: &ModelatorRuntime,
) -> Command {
    let tla2tools = jar::Jar::Tla.path(&runtime.dir);
    let community_modules = jar::Jar::CommunityModules.path(&runtime.dir);

    let mut cmd = Command::new("java");
    cmd.current_dir(temp_dir)
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
        .arg(tla_config_file_path.as_ref())
        // set "-tool" flag, which allows easier parsing of TLC's output
        .arg("-tool")
        // set the number of TLC's workers
        .arg("-workers")
        .arg(workers(runtime));

    // show command being run
    tracing::debug!("{}", crate::util::cmd_show(&cmd));
    cmd
}

fn workers(runtime: &ModelatorRuntime) -> String {
    match runtime.model_checker_runtime.workers {
        ModelCheckerWorkers::Auto => "auto".to_string(),
        ModelCheckerWorkers::Count(count) => count.to_string(),
    }
}
