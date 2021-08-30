use super::{Artifact, ArtifactCreator};
use crate::Error;

/// Ultra-basic wrapper around stdout of model checker execution
/// NOTE: This is a stand in and will be changed soon.
pub struct ModelCheckerStdout {
    backing_str: String,
}

impl ModelCheckerStdout {
    fn new(s: &str) -> ModelCheckerStdout {
        ModelCheckerStdout {
            backing_str: s.to_string(),
        }
    }
}

impl std::fmt::Display for ModelCheckerStdout {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.backing_str)?;
        Ok(())
    }
}

impl ArtifactCreator for ModelCheckerStdout {
    fn from_string(s: &str) -> Result<Self, Error> {
        Ok(ModelCheckerStdout::new(s))
    }
}

impl Artifact for ModelCheckerStdout {
    fn as_string(&self) -> String {
        self.backing_str.clone()
    }
}
