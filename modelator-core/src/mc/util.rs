pub(crate) fn output_to_string(output: &Vec<u8>) -> String {
    String::from_utf8_lossy(output).to_string()
}

pub(crate) fn random_string() -> String {
    use rand::Rng;
    rand::thread_rng()
        .sample_iter(&rand::distributions::Alphanumeric)
        .take(42)
        .map(char::from)
        .collect()
}
