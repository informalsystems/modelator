use super::{Artifact, ArtifactCreator};
use crate::{Error, ModelCheckerOptions};
use core::result::Result::Err;
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

impl TlaFile {
    /// Returns the module name of the TLA file
    pub fn module_name(&self) -> &str {
        &self.module_name
    }

    /// Returns a base filename {module_name}.tla
    pub fn file_name(&self) -> String {
        format!("{}.tla", &self.module_name)
    }

    /// Returns raw file contents (string value that it was initialized with)
    /// NOTE: will likely change as our internal repr improves
    pub fn file_contents_backing(&self) -> &str {
        &self.file_contents_backing
    }
}

impl ArtifactCreator for TlaFile {
    /// Create a new instance from a file content string.
    fn from_string(s: &str) -> Result<Self, Error> {
        match module_name(s) {
            Err(_) => Err(Error::MissingTlaFileModuleName(s.to_string())),
            Ok(name) => Ok(TlaFile {
                file_contents_backing: s.to_string(),
                module_name: name,
            }),
        }
    }
}

impl Artifact for TlaFile {
    fn as_string(&self) -> String {
        // TODO: will use explicit data to generate a repr
        self.file_contents_backing.clone()
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

#[derive(Debug, PartialEq, Eq)]
struct ModuleNameParseError;

fn module_name(file_content: &str) -> Result<String, ModuleNameParseError> {
    let substr = "MODULE";
    for line in file_content.split('\n').into_iter() {
        if line.contains(substr) {
            let segments = line.split_whitespace().collect::<Vec<&str>>();
            if segments.len() != 4 {
                return Err(ModuleNameParseError);
            }
            return Ok(segments[2].to_string());
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
        assert_eq!(module_name(s), Ok("moduleName".into()));
    }
}
