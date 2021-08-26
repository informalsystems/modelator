use super::tla_config_file::TlaConfigFile;
use super::tla_file::TlaFile;
use super::Artifact;

pub struct ModelCheckingTestArgs {
    tla_target_file: TlaFile,
    tla_config_file: TlaConfigFile,
    dependency_tla_files: Vec<TlaFile>,
}

//NEXT: Should implement some kind of iterator or collection access for model checking test args
// ALso need to go back over existing artifacts and split them off into ArtifactCreator impl
impl IntoIterator for ModelCheckingTestArgs {
    type Item = Box<dyn Artifact>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut ret: Vec<Box<dyn Artifact>> = Vec::new();
        for f in self.dependency_tla_files.clone() {
            ret.push(Box::new(f));
        }
        ret.push(Box::new(self.tla_target_file.clone()));
        ret.push(Box::new(self.tla_config_file.clone()));
        ret
    }
}
