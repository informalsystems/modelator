use std::path::PathBuf;
use std::process::Command;

pub(crate) fn cmd_output_to_string(output: &[u8]) -> String {
    String::from_utf8_lossy(output).to_string()
}

pub(crate) fn cmd_show(cmd: &Command) -> String {
    let cmd = format!("{:?}", cmd).replace("\"", "");
    let cmd = cmd.trim_start_matches("Command { std:");
    let cmd = cmd.trim_end_matches(", kill_on_drop: false }");
    cmd.to_owned()
}

pub(crate) fn absolute_path(path: &PathBuf) -> String {
    match path.canonicalize() {
        Ok(path) => path.to_string_lossy().to_string(),
        Err(e) => panic!("[modelator] couldn't compute absolute path: {:?}", e),
    }
}
