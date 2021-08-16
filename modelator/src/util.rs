use crate::Error;
use std::collections::HashSet;
use std::fs::copy;
use std::path::{Path, PathBuf};
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

/// Copies all files with the given extension in the same directory as the given file into another directory
/// Returns the new path for the main file
pub(crate) fn copy_files_into<P: AsRef<Path>, Q: AsRef<Path>>(
    ext: &str,
    file: P,
    dir: Q,
) -> Result<PathBuf, Error> {
    let files = list_files(ext, &file)?;
    let dir = PathBuf::from(dir.as_ref());
    if !dir.is_dir() || !dir.exists() {
        return Err(Error::IO(
            "Can't copy files: destination directory doesn't exist".to_string(),
        ));
    }
    for file in files {
        if let Some(file_name) = file.file_name() {
            let dest = dir.join(file_name);
            copy(file, dest).map_err(Error::io)?;
        }
    }
    // it is OK to unwrap, as the file has been checked before
    Ok(dir.join(file.as_ref().file_name().unwrap()))
}

/// Lists all files with the given extension in the same directory as the given file
/// Returns error if the given file doesn't exist, or is not a TLA+ file
fn list_files<P: AsRef<Path>>(ext: &str, file: P) -> Result<Vec<PathBuf>, Error> {
    // Checks that the given path points to an existing TLA+ file
    let is_ext = |f: &Path| {
        f.extension()
            .map_or("".to_owned(), |x| x.to_string_lossy().to_string())
            == ext
    };
    let file = file.as_ref();
    if !file.exists() || !is_ext(file) {
        return Err(Error::IO(format!("File doesn't exist: {}", file.display())));
    }
    // The parent directory of the file
    let dir = file.parent().map_or(PathBuf::from("./"), |p| {
        if p.to_string_lossy().is_empty() {
            PathBuf::from("./")
        } else {
            p.to_path_buf()
        }
    });
    // Collect all files with the same extension in this directory
    let files = std::fs::read_dir(dir)
        .map_err(Error::io)?
        .flatten()
        .filter(|dir_entry| {
            dir_entry
                .file_type()
                .map(|file_type| file_type.is_file())
                .unwrap_or_default()
        })
        .map(|dir_entry| dir_entry.path())
        .filter(|file_path| is_ext(file_path))
        .collect();
    Ok(files)
}
