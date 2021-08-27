use super::tla_config_file::TlaConfigFile;
use super::tla_file::TlaFile;
use super::{Artifact, ArtifactCreator};
use crate::Error;

// An in-memory representation of all the resources needed to perform model checking
// Includes the main .tla and .cfg files as well as depended on (via EXTENDS) .tla files.
pub struct TlaFileSuite {
    pub tla_file: TlaFile,
    pub tla_config_file: TlaConfigFile,
    pub dependency_tla_files: Vec<TlaFile>,
}

fn gather_dependencies<P: AsRef<std::path::Path>>(tla_file: P) -> Result<Vec<TlaFile>, Error> {
    todo!();
}

impl TlaFileSuite {
    // Gather all model checking resources from a main .tla and .cfg file
    pub fn from_tla_and_config_paths<P: AsRef<std::path::Path>>(
        tla_file_path: P,
        config_file_path: P,
    ) -> Result<TlaFileSuite, Error> {
        let tla_file = TlaFile::try_read_from_file(tla_file_path)?;
        let tla_config_file = TlaConfigFile::try_read_from_file(config_file_path)?;
        let dependencies = gather_dependencies(tla_file_path)?;
        Ok(TlaFileSuite {
            tla_file,
            tla_config_file,
            dependency_tla_files: dependencies,
        })
    }
}

impl<'a> IntoIterator for &'a TlaFileSuite {
    type Item = Box<&'a dyn Artifact>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut ret: Vec<Self::Item> = Vec::new();
        for f in self.dependency_tla_files.clone() {
            ret.push(Box::new(&f));
        }
        ret.push(Box::new(&self.tla_file));
        ret.push(Box::new(&self.tla_config_file));
        ret.into_iter()
    }
}
