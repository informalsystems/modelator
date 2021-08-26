use super::Artifact;
use crate::{Error, ModelCheckerOptions};
use core::result::Result::Err;
use std::convert::TryFrom;
use std::fs;
use std::path::{Path, PathBuf};

/// `modelator`'s artifact representing a TLA+ file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlaFile {
    /// TODO: file_contents backing strings are to be removed
    file_contents_backing: String,
    /// Module name
    module_name: String,
}

impl Artifact for TlaFile {
    /// Create a new instance from a file content string.
    fn new(s: &str) -> Result<Self, Error> {
        match module_name(s) {
            Err(_) => Err(Error::MissingTlaFileModuleName(s.to_string())),
            Ok(name) => Ok(TlaFile {
                file_contents_backing: s.to_string(),
                module_name: name.to_string(),
            }),
        }
    }

    /// Returns a string representation.

    fn as_string(&self) -> &str {
        // TODO: will use explicit data to generate a repr
        &self.file_contents_backing
    }
}

impl std::fmt::Display for TlaFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            crate::util::absolute_path(&self.file_contents_backing)
        )
    }
}

struct ModuleNameParseError;

fn module_name(file_content: &str) -> Result<String, ModuleNameParseError> {
    let substr = "MODULE";
    for line in file_content.split('\n').into_iter() {
        if line.contains(substr) {
            let segments = line.split_whitespace().collect::<Vec<&str>>();
            if segments.len() != 4 {
                return Err(ModuleNameParseError);
            }
            return Ok(segments[3].to_string());
        } else if !line.trim().is_empty() {
            // Line not whitespace but also does not contain module name
            // -> invalid TLA file.
            return Err(ModuleNameParseError);
        }
    }
    Err(ModuleNameParseError)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_parse() {
        let s = "\n---------- MODULE moduleName ----------\n42";
        match module_name(s) {
            Ok(m) => assert_eq!(m, "moduleName"),
            _ => assert!(false),
        };
    }
}
