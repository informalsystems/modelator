use crate::error::Error;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

// The minimum java version supported by Apalache is Java 8:
// https://apalache.informal.systems/docs/apalache/system-reqs.html
// TLC doesn't seem to have such requirement.
const MIN_JAVA_VERSION: usize = 8;

pub const TLA_JAR: &str = "tla2tools-v1.8.0.jar";
pub const COMMUNITY_MODULES_JAR: &str = "CommunityModules-202103092123.jar";
pub const APALACHE_JAR: &str = "apalache-v0.11.0.jar";

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub(crate) enum Jar {
    Tla,
    CommunityModules,
    Apalache,
}

impl Jar {
    pub(crate) fn path<P: AsRef<Path>>(&self, modelator_dir: P) -> PathBuf {
        modelator_dir.as_ref().join(self.file_name())
    }

    fn file_name(&self) -> &str {
        match self {
            Self::Tla => TLA_JAR,
            Self::CommunityModules => COMMUNITY_MODULES_JAR,
            Self::Apalache => APALACHE_JAR,
        }
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

    fn link(&self) -> String {
        format!(
            "https://github.com/informalsystems/modelator/raw/main/modelator/jars/{}",
            self.file_name()
        )
    }

    fn download<P: AsRef<Path>>(&self, modelator_dir: P) -> Result<(), Error> {
        let modelator_dir = modelator_dir.as_ref();
        // compute file where the jar should be stored
        let path = self.path(&modelator_dir);

        // download the jar
        let response = ureq::get(&self.link()).call().map_err(Error::ureq)?;
        let mut reader = response.into_reader();

        // write jar bytes to the file
        let file = std::fs::File::create(path).map_err(Error::io)?;
        let mut file_writer = std::io::BufWriter::new(file);
        std::io::copy(&mut reader, &mut file_writer).map_err(Error::io)?;
        Ok(())
    }

    fn all() -> Vec<Self> {
        vec![Self::Tla, Self::CommunityModules, Self::Apalache]
    }
}

pub(crate) fn download_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<(), Error> {
    // get all existing jars
    let existing_jars = existing_jars(&modelator_dir)?;
    // download all jars that do not exist yet
    let mut check_java = false;
    for jar in Jar::all() {
        if !existing_jars.contains(&jar) {
            jar.download(&modelator_dir)?;
            check_java = true;
        }
    }
    // if we have downloaded the jar(s) for the first time, check that we have a
    // compatible version of java
    if check_java {
        check_java_version()?;
    }
    Ok(())
}

fn existing_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<Jar>, Error> {
    let mut existing_jars = HashSet::new();
    // read files the modelator directory
    for file_name in crate::util::read_dir(modelator_dir)? {
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

fn check_java_version() -> Result<(), Error> {
    let mut cmd = Command::new("java");
    cmd.arg("-XshowSettings:all").arg("--version");
    // show command being run
    tracing::debug!("{}", crate::util::cmd_show(&cmd));

    match cmd.output() {
        Ok(output) => {
            let stderr = crate::util::cmd_output_to_string(&output.stderr);
            let mut versions: Vec<_> = stderr
                .lines()
                .filter(|line| line.trim().starts_with("java.specification.version ="))
                .collect();
            tracing::debug!("java version {:?}", versions);

            assert_eq!(
                versions.len(),
                1,
                "[modelator] expected at most one 'java.specification.version'"
            );

            // it's okay to unwrap as we have already asserted that the version exists
            let version_parts: Vec<_> = versions.pop().unwrap().split('=').collect();
            assert_eq!(
                version_parts.len(),
                2,
                "[modelator] unexpected 'java.specification.version' format"
            );
            let version_number: usize = version_parts[1]
                .trim()
                .parse()
                .expect("[modelator] unexpected 'java.specification.version' format");

            if version_number < MIN_JAVA_VERSION {
                Err(Error::MinimumJavaVersion(version_number, MIN_JAVA_VERSION))
            } else {
                Ok(())
            }
        }
        Err(err) => {
            tracing::debug!("error checking Java version: {}", err);
            Err(Error::MissingJava)
        }
    }
}
