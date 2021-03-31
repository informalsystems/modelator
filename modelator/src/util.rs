use crate::Error;
use serde::de::DeserializeOwned;
use std::collections::HashSet;
use std::path::Path;
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

pub(crate) fn check_file_existence<P: AsRef<Path>>(path: P) -> Result<(), Error> {
    let path = path.as_ref();
    if path.is_file() {
        Ok(())
    } else {
        Err(Error::FileNotFound(path.to_path_buf()))
    }
}

pub(crate) fn absolute_path<P: AsRef<Path>>(path: P) -> String {
    match path.as_ref().canonicalize() {
        Ok(path) => path.to_string_lossy().to_string(),
        Err(e) => panic!("[modelator] couldn't compute absolute path: {:?}", e),
    }
}

/// Tries to parse a string as the given type
pub fn parse_from_str<T: DeserializeOwned>(input: &str) -> Result<T, Error> {
    serde_json::from_str(input).map_err(|e| Error::ParseError(e.to_string()))
}

/// Tries to parse a Json Value as the given type
pub fn parse_from_value<T: DeserializeOwned>(input: serde_json::Value) -> Result<T, Error> {
    serde_json::from_value(input).map_err(|e| Error::ParseError(e.to_string()))
}

pub(crate) fn read_dir<P: AsRef<Path>>(path: P) -> Result<HashSet<String>, Error> {
    let mut file_names = HashSet::new();
    let files = std::fs::read_dir(path).map_err(Error::io)?;
    for file in files {
        // for each file in the modelator directory, check if it is a jar
        let file_name = file
            .map_err(Error::io)?
            .file_name()
            .into_string()
            .map_err(Error::InvalidUnicode)?;
        assert!(file_names.insert(file_name));
    }
    Ok(file_names)
}

pub(crate) mod digest {
    use super::*;
    use sha2::Digest;
    use std::collections::BTreeSet;

    pub(crate) fn digest_files(paths: BTreeSet<String>) -> Result<sha2::Sha256, Error> {
        let mut digest = sha2::Sha256::default();
        for path in paths {
            digest_file(path, &mut digest)?;
        }
        Ok(digest)
    }

    pub(crate) fn encode(digest: sha2::Sha256) -> String {
        hex::encode(digest.finalize())
    }

    fn digest_file(path: String, digest: &mut sha2::Sha256) -> Result<(), Error> {
        let file = std::fs::File::open(path).map_err(Error::io)?;
        let mut reader = std::io::BufReader::new(file);

        let mut buffer = [0; 1024];
        loop {
            use std::io::Read;
            let count = reader.read(&mut buffer).map_err(Error::io)?;
            if count == 0 {
                break;
            }
            digest.update(&buffer[..count]);
        }

        Ok(())
    }
}
