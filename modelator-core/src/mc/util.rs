pub(crate) fn output_to_string(output: &Vec<u8>) -> String {
    String::from_utf8_lossy(output).to_string()
}
