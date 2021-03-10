use crate::error::Error;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

const TLA_VERSION: &str = "1.8.0";
const COMMUNITY_MODULES_VERSION: &str = "202102040137";

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Jar {
    Tla,
    CommunityModules,
}

impl Jar {
    pub(crate) fn file<P: AsRef<Path>>(&self, modelator_dir: P) -> PathBuf {
        let file_name = match self {
            Self::Tla => "tla2tools.jar",
            Self::CommunityModules => "CommunityModules.jar",
        };
        modelator_dir.as_ref().join(file_name)
    }

    fn from<F: AsRef<str>>(file_name: F) -> Self {
        let file_name = file_name.as_ref();
        match file_name {
            "tla2tools.jar" => Self::Tla,
            "CommunityModules.jar" => Self::CommunityModules,
            _ => panic!("[modelator] unexpected jar file: {}", file_name),
        }
    }

    fn link(&self) -> String {
        match self {
            Self::Tla => format!(
                "https://github.com/tlaplus/tlaplus/releases/download/v{}/tla2tools.jar",
                TLA_VERSION
            ),
            Self::CommunityModules => format!(
                "https://github.com/tlaplus/CommunityModules/releases/download/{}/CommunityModules.jar",
                COMMUNITY_MODULES_VERSION
            ),
        }
    }

    fn download<P: AsRef<Path>>(&self, modelator_dir: P) -> Result<(), Error> {
        let modelator_dir = modelator_dir.as_ref();
        // compute jar link and file where it should be stored
        let link = self.link();
        let file = self.file(&modelator_dir);

        // download jar
        let response = reqwest::blocking::get(&link).map_err(Error::Reqwest)?;
        let jar = response.bytes().map_err(Error::Reqwest)?;
        std::fs::write(file, jar).map_err(Error::IO)?;
        Ok(())
    }

    fn all() -> Vec<Self> {
        vec![Self::Tla, Self::CommunityModules]
    }
}

pub(crate) fn download_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<(), Error> {
    // get all existing jars
    let existing_jars = existing_jars(&modelator_dir)?;
    // download all jars that do not exist yet
    for jar in Jar::all() {
        if !existing_jars.contains(&jar) {
            jar.download(&modelator_dir)?;
        }
    }
    Ok(())
}

fn existing_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<Jar>, Error> {
    let mut existing_jars = HashSet::new();
    // read files the modelator directory
    let files = std::fs::read_dir(modelator_dir).map_err(Error::IO)?;
    for file in files {
        // for each file in the modelator directory, check if it is a jar
        let file_name = file
            .map_err(Error::IO)?
            .file_name()
            .into_string()
            .map_err(Error::InvalidUnicode)?;
        if file_name.ends_with(".jar") {
            // if the file is a jar, then save it as already downloaded
            existing_jars.insert(Jar::from(&file_name));
        }
    }
    assert!(
        existing_jars.len() <= 3,
        "[modelator] at most 3 jar files should have been downloaded"
    );
    Ok(existing_jars)
}
