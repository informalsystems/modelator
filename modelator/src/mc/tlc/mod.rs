/// Parsing of TLC's output.
mod output;

use super::trace::Trace;
use super::util;
use crate::{jar, Error, Options, Workers};
use tokio::process::Command;

pub(crate) async fn run(options: &Options) -> Result<Vec<Trace>, Error> {
    // create tlc command
    let mut cmd = cmd(options);

    // start tlc
    // TODO: add timeout
    let output = cmd.output().await.map_err(Error::IO)?;

    // get tlc stdout and stderr
    let stdout = util::output_to_string(&output.stdout);
    let stderr = util::output_to_string(&output.stderr);
    tracing::debug!("TLC stdout:\n{}", stdout);
    tracing::debug!("TLC stderr:\n{}", stderr);

    match (stdout.is_empty(), stderr.is_empty()) {
        (false, true) => {
            // if stderr is empty, but the stdout is not, then no error has
            // occurred

            // save tlc log
            tokio::fs::write(&options.log, &stdout)
                .await
                .map_err(Error::IO)?;

            // remove tlc 'states' folder: this avoids a TLC error when we're are
            // able to run TLC twice in the same second, and the folders created
            // inside the 'states' folder are named using the current date with a
            // second precision (e.g. 'states/21-03-04-16-42-04')
            tokio::fs::remove_dir("states").await.map_err(Error::IO)?;

            // convert tlc output to counterexamples
            output::parse(stdout, &options)
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

fn cmd(options: &Options) -> Command {
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
        .arg(&options.model_file)
        // set "-tool" flag, which allows easier parsing of TLC's output
        .arg("-tool")
        // set the number of TLC's workers
        .arg("-workers")
        .arg(workers(options.workers));

    // show command being run
    let pretty = format!("{:?}", cmd).replace("\"", "");
    let pretty = pretty.trim_start_matches("Command { std:");
    let pretty = pretty.trim_end_matches(", kill_on_drop: false }");
    tracing::debug!("{}", pretty);

    cmd
}

fn workers(workers: Workers) -> String {
    match workers {
        Workers::Auto => "auto".to_string(),
        Workers::Count(count) => count.to_string(),
    }
}
