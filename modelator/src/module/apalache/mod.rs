/// Apalache Error
pub(crate) mod error_message;
use error_message::ErrorMessage;

/// Parsing of Apalache's counterexample file.
mod counterexample;

use crate::artifact::{Artifact, TlaConfigFile, TlaFile, TlaTrace};
use crate::cache::TlaTraceCache;
use crate::module::apalache;
use crate::{jar, Error, Options};
use std::path::Path;
use std::process::Command;

/// `modelator`'s Apalache module.
#[derive(Debug, Clone, Copy)]
pub struct Apalache;

impl Apalache {
    /// TODO: ignoring because of <https://github.com/informalsystems/modelator/issues/47>
    ///
    /// Generate a TLA+ trace given a [TlaFile] and a [TlaConfigFile] produced
    /// by [crate::module::Tla::generate_tests].
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use modelator::artifact::{TlaFile, TlaConfigFile};
    /// use modelator::module::{Tla, Apalache};
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
    /// let tla_trace = Apalache::test(tla_test_file, tla_test_config_file, &options).unwrap();
    /// println!("{:?}", tla_trace);
    /// ```
    pub fn test(
        tla_file: &TlaFile,
        tla_config_file: &TlaConfigFile,
        options: &Options,
    ) -> Result<TlaTrace, Error> {
        // TODO: this method currently just uses the paths of the files so no need for whole artifact objects!

        tracing::debug!(
            "Apalache::test {} {} {:?}",
            tla_file,
            tla_config_file,
            options
        );

        // TODO: disabling cache for now; see https://github.com/informalsystems/modelator/issues/46
        // load cache and check if the result is cached
        // let mut cache = TlaTraceCache::new(options)?;
        // let cache_key = TlaTraceCache::key(&tla_file, &tla_config_file)?;
        // if let Some(value) = cache.get(&cache_key)? {
        //     return Ok(value);
        // }

        // create apalache test command
        let cmd = test_cmd(tla_file.path(), tla_config_file.path(), options);

        // run apalache
        run_apalache(cmd, options)?;

        // convert apalache counterexample to a trace
        let counterexample_path = Path::new("counterexample.tla");
        if counterexample_path.is_file() {
            use std::convert::TryFrom;
            let counterexample: TlaFile = TlaFile::try_read_from_file(counterexample_path)?;
            tracing::debug!("Apalache counterexample:\n{}", counterexample);
            let trace = counterexample::parse(counterexample.content())?;

            // TODO: disabling cache for now; see https://github.com/informalsystems/modelator/issues/46
            // cache trace and then return it
            //cache.insert(cache_key, &trace)?;
            Ok(trace)
        } else {
            panic!("[modelator] expected to find Apalache's counterexample.tla file")
        }
    }

    /// TODO: ignoring because of <https://github.com/informalsystems/modelator/issues/47>.
    ///
    /// Runs Apalache's `parse` command, returning the [TlaFile] produced by
    /// Apalache.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use modelator::artifact::TlaFile;
    /// use modelator::module::Apalache;
    /// use modelator::Options;
    /// use std::convert::TryFrom;
    ///
    /// let tla_file = "tests/integration/tla/NumbersAMaxBMinTest.tla";
    /// let tla_file = TlaFile::try_from(tla_file).unwrap();
    ///
    /// let options = Options::default();
    /// let mut tla_parsed_file = Apalache::parse(tla_file, &options).unwrap();
    /// println!("{:?}", tla_parsed_file);
    /// ```
    pub fn parse(tla_file: TlaFile, options: &Options) -> Result<TlaFile, Error> {
        tracing::debug!("Apalache::parse {} {:?}", tla_file, options);

        // compute the directory in which the tla file is stored
        let tla_file_dir = {
            let mut ret = tla_file.path().to_path_buf();
            assert!(ret.pop());
            ret
        };

        let tla_file_name = tla_file.file_name();

        // compute the output tla file
        let tla_parsed_file_full_path = tla_file_dir.join(format!("{}Parsed.tla", tla_file_name));

        // create apalache parse command
        let cmd = parse_cmd(tla_file.path(), &tla_parsed_file_full_path, options);

        // run apalache
        run_apalache(cmd, options)?;

        // create tla file
        use std::convert::TryFrom;
        let tla_parsed_file = TlaFile::try_from(tla_parsed_file_full_path)?;
        Ok(tla_parsed_file)
    }
}

fn run_apalache(mut cmd: Command, options: &Options) -> Result<String, Error> {
    // start apalache
    // TODO: add timeout
    let output = cmd.output()?;

    // get apalache stdout and stderr
    let stdout = crate::util::cmd_output_to_string(&output.stdout);
    let stderr = crate::util::cmd_output_to_string(&output.stderr);
    tracing::debug!("Apalache stdout:\n{}", stdout);
    tracing::debug!("Apalache stderr:\n{}", stderr);

    match (stdout.is_empty(), stderr.is_empty()) {
        (false, true) => {
            // apalache writes all its output to the stdout

            // save apalache log
            //TODO: probably better to return the log in memory and write it somewhere else
            std::fs::write(&options.model_checker_options.log, &stdout)?;

            // check if a failure has occurred
            if stdout.contains("EXITCODE: ERROR") {
                return Err(Error::ApalacheFailure(apalache::ErrorMessage::new(&stdout)));
            }
            assert!(
                stdout.contains("EXITCODE: OK"),
                "[modelator] unexpected Apalache stdout"
            );
            Ok(stdout)
        }
        _ => {
            panic!("[modelator] unexpected Apalache's stdout/stderr combination")
        }
    }
}

fn test_cmd<P: AsRef<Path>>(tla_file: P, tla_config_file: P, options: &Options) -> Command {
    let mut cmd = apalache_start_cmd(&tla_file, options);
    cmd.arg("check")
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

fn parse_cmd<P: AsRef<Path>>(tla_file: P, output_file: P, options: &Options) -> Command {
    let mut cmd = apalache_start_cmd(&tla_file, options);
    cmd.arg("parse")
        // set tla output file
        .arg(format!(
            "--output={}",
            output_file.as_ref().to_string_lossy()
        ))
        // set tla file
        .arg(tla_file.as_ref());

    // show command being run
    tracing::debug!("{}", crate::util::cmd_show(&cmd));
    cmd
}

fn apalache_start_cmd<P: AsRef<Path>>(tla_file: P, options: &Options) -> Command {
    let apalache = jar::Jar::Apalache.path(&options.dir);

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
        .arg(format!("{}", apalache.as_path().to_string_lossy()));
    cmd
}
