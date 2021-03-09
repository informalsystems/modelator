use crate::Artifact;
use std::{fmt::Display, path::Path};

use super::ArtifactFormat;

pub(crate) type TLAState = String;

#[derive(Debug)]
pub(crate) struct Trace {
    pub states: Vec<TLAState>,
}

impl Trace {
    pub(crate) fn new() -> Self {
        Self { states: Vec::new() }
    }

    pub(crate) fn add(&mut self, state: TLAState) {
        self.states.push(state);
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

impl Display for Trace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for state in &self.states {
            write!(f, "{}\n\n", state)?;
        }
        Ok(())
    }
}

impl Artifact for Trace {
    fn name(&self) -> &'static str {
        "State trace from model checking"
    }

    fn typ(&self) -> &'static str {
        "trace"
    }

    fn from_string(s: &str) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn from_file(f: &Path) -> Result<Self, crate::Error>
    where
        Self: Sized,
    {
        todo!()
    }

    fn formats(&self) -> Vec<ArtifactFormat> {
        vec![ArtifactFormat::TLC, ArtifactFormat::JSON]
    }

    fn to_file(&self, f: &Path, format: super::ArtifactFormat) -> Result<(), crate::Error> {
        todo!()
    }
}
