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
    /// Generate a TLA+ trace given a [`TlaFile`] and a [`TlaConfigFile`] produced
    /// by [`crate::model::language::Tla::generate_tests`].
    ///
    /// # Examples
    /// ```ignore
    /// use modelator::artifact::TlaFileSuite;
    /// use modelator::model::{language::Tla, checker::Tlc};
    /// use modelator::ModelatorRuntime;
    /// use std::convert::TryFrom;
    ///
    /// let tla_tests_file = "tests/integration/resource/NumbersAMaxBMinTest.tla";
    /// let tla_config_file = "tests/integration/resource/Numbers.cfg";
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
        runtime: &ModelatorRuntime,
    ) -> Result<(Vec<TlaTrace>, ModelCheckerStdout), Error> {
        let tla_file = &tla_file_suite.tla_file;
        let tla_config_file = &tla_file_suite.tla_config_file;
        tracing::debug!("Tlc::test {} {} {:?}", tla_file, tla_config_file, runtime);

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
            runtime,
        );

        // start tlc
        let output = cmd.output()?;

        // get tlc stdout and stderr
        let stdout = crate::util::cmd_output_to_string(&output.stdout);
        let stderr = crate::util::cmd_output_to_string(&output.stderr);
        tracing::debug!("TLC stdout:\n{}", stdout);
        tracing::debug!("TLC stderr:\n{}", stderr);

        match (stdout.is_empty(), stderr.is_empty()) {
            (true, true) => {
                panic!("[modelator] stdout and stderr from TLC both empty")
            }
            (false, true) => {
                let tlc_log = ModelCheckerStdout::from_string(&stdout)?;

                let mut traces = output::parse_traces(&stdout, &runtime.model_checker_runtime)?;

                traces.truncate(runtime.model_checker_runtime.traces_per_test);

                // check if no trace was found
                if traces.is_empty() {
                    return Err(Error::NoTestTraceFound(
                        //TODO: this will have to be changed to reflect new in-memory log
                        runtime.model_checker_runtime.log.clone(),
                    ));
                }

                // TODO: disabling cache for now; see https://github.com/informalsystems/modelator/issues/46
                // cache trace and then return it
                //cache.insert(cache_key, &trace)?;
                Ok((traces, tlc_log))
            }
            _ => {
                // stderr not empty
                Err(Error::TLCFailure(stderr))
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

    let path_seperator_char = match std::path::MAIN_SEPARATOR {
        '/' => ":",
        '\\' => ";",
        // use unreachable_unchecked
        _ => unreachable!("should not be reachable"),
    };

    let mut cmd = Command::new("java");
    cmd.current_dir(temp_dir)
        // set classpath
        .arg("-cp")
        .arg(
            [
                tla2tools.as_path().to_string_lossy(),
                community_modules.as_path().to_string_lossy(),
            ]
            .join(path_seperator_char),
        )
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

    if 1 < runtime.model_checker_runtime.traces_per_test {
        // Allow TLC to continue model checking after violating the test invariant
        // NOTE: currently, limiting the number of tests generated or halting when exploring
        // an unbounded state space is not supported.
        cmd.arg("-continue");
        tracing::warn!(
            r#"Generating multiple traces per test when using TLC can result in
TLC not terminating if the state space is unbounded."#
        );
    }

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
