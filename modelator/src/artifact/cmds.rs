use super::tla_config_file::TlaConfigFile;
use super::tla_file::TlaFile;
use super::Artifact;

pub struct ModelCheckingTestArgs {
    tla_target_file: TlaFile,
    tla_config_file: TlaConfigFile,
    dependency_tla_files: Vec<TlaFile>,
}

impl<'a> IntoIterator for &'a ModelCheckingTestArgs {
    type Item = Box<&'a dyn Artifact>;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        let mut ret: Vec<Self::Item> = Vec::new();
        for f in self.dependency_tla_files.clone() {
            ret.push(Box::new(&f));
        }
        ret.push(Box::new(&self.tla_target_file));
        ret.push(Box::new(&self.tla_config_file));
        ret.into_iter()
    }
}
