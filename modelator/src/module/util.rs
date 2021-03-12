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
