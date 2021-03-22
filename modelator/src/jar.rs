use crate::error::Error;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

pub const TLA_JAR: &str = "tla2tools-v1.8.0.jar";
pub const TLA_JAR_BYTES: &[u8] = include_bytes!("../jars/tla2tools-v1.8.0.jar");

pub const COMMUNITY_MODULES_JAR: &str = "CommunityModules-202103092123.jar";
pub const COMMUNITY_MODULES_JAR_BYTES: &[u8] =
    include_bytes!("../jars/CommunityModules-202103092123.jar");

pub const APALACHE_JAR: &str = "apalache-v0.11.0.jar";
pub const APALACHE_JAR_BYTES: &[u8] = include_bytes!("../jars/apalache-v0.11.0.jar");

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Jar {
    Tla,
    CommunityModules,
    Apalache,
}

impl Jar {
    pub(crate) fn file<P: AsRef<Path>>(&self, modelator_dir: P) -> PathBuf {
        let file_name = match self {
            Self::Tla => TLA_JAR,
            Self::CommunityModules => COMMUNITY_MODULES_JAR,
            Self::Apalache => APALACHE_JAR,
        };
        modelator_dir.as_ref().join(file_name)
    }

    fn from<F: AsRef<str>>(file_name: F) -> Self {
        let file_name = file_name.as_ref();
        match file_name {
            TLA_JAR => Self::Tla,
            COMMUNITY_MODULES_JAR => Self::CommunityModules,
            APALACHE_JAR => Self::Apalache,
            _ => panic!("[modelator] unexpected jar file: {}", file_name),
        }
    }

    fn write<P: AsRef<Path>>(&self, modelator_dir: P) -> Result<(), Error> {
        let modelator_dir = modelator_dir.as_ref();
        // compute file where the jar should be stored
        let file = self.file(&modelator_dir);

        // get jar bytes and write them to the file
        let bytes = match self {
            Self::Tla => TLA_JAR_BYTES,
            Self::CommunityModules => COMMUNITY_MODULES_JAR_BYTES,
            Self::Apalache => APALACHE_JAR_BYTES,
        };
        std::fs::write(file, bytes).map_err(Error::io)?;
        Ok(())
    }

    fn all() -> Vec<Self> {
        vec![Self::Tla, Self::CommunityModules, Self::Apalache]
    }
}

pub(crate) fn write_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<(), Error> {
    // get all existing jars
    let existing_jars = existing_jars(&modelator_dir)?;
    // download all jars that do not exist yet
    for jar in Jar::all() {
        if !existing_jars.contains(&jar) {
            jar.write(&modelator_dir)?;
        }
    }
    Ok(())
}

fn existing_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<Jar>, Error> {
    let mut existing_jars = HashSet::new();
    // read files the modelator directory
    let files = std::fs::read_dir(modelator_dir).map_err(Error::io)?;
    for file in files {
        // for each file in the modelator directory, check if it is a jar
        let file_name = file
            .map_err(Error::io)?
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
