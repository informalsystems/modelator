/// Parsing of TLC's output.
mod output;

use super::trace::Trace;
use super::util;
use crate::{jar, Error};
use std::path::{Path, PathBuf};
use tokio::process::Command;

pub(crate) struct TlcOptions {
    pub tla_file: PathBuf,
    pub all_counterexamples: bool,
    pub workers: String,
    pub log: PathBuf,
}

pub(crate) async fn run<P: AsRef<Path>>(
    modelator_dir: P,
    options: TlcOptions,
) -> Result<Vec<Trace>, Error> {
    // create tlc command
    let mut cmd = cmd(&modelator_dir, &options);

    // start tlc
    let child = cmd.spawn().map_err(Error::IO)?;

    // TODO: add timeout
    let output = child.wait_with_output().await.map_err(Error::IO)?;

    // save tlc log
    let stdout = util::output_to_string(&output.stdout);
    tokio::fs::write(options.log, &stdout)
        .await
        .map_err(Error::IO)?;

    // convert tlc output to counterexamples
    output::parse(stdout)
}

fn cmd<P: AsRef<Path>>(modelator_dir: P, options: &TlcOptions) -> Command {
    let tla2tools = jar::Jar::Tla.file(&modelator_dir);
    let community_modules = jar::Jar::CommunityModules.file(&modelator_dir);
    let mut cmd = Command::new("java");
    cmd
        // set classpath
        .arg("-cp")
        .arg(format!(
            "{:?}:{:?}",
            tla2tools.as_path(),
            community_modules.as_path()
        ))
        // set tla file
        .arg("tlc2.TLC")
        .arg(&options.tla_file)
        // set "-tool" flag, which allows easier parsing of TLC's output
        .arg("-tool")
        // set the number of TLC's workers
        .arg("-workers")
        .arg(&options.workers);

    // maybe set "-continue" flag
    if options.all_counterexamples {
        cmd.arg("-continue");
    }
    cmd
}
