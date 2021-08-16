use crate::error::Error;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

// The minimum java version supported by Apalache is Java 8:
// https://apalache.informal.systems/docs/apalache/system-reqs.html
// TLC doesn't seem to have such requirement.
const MIN_JAVA_VERSION: usize = 8;

pub(crate) const TLA_JAR: &str = "tla2tools-v1.8.0.jar";
pub(crate) const COMMUNITY_MODULES_JAR: &str = "CommunityModules-202103092123.jar";
pub(crate) const APALACHE_JAR: &str = "apalache-v0.11.0.jar";
pub(crate) const JARS_CHECKSUM: &str =
    "55b7131eff44ef1c27bb8733a5b117ab9a327a3d41bdab26bce56dd193dc1f13";

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
            "https://github.com/informalsystems/modelator/raw/main/jars/{}",
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
    // compute jars that are missing
    let missing_jars: HashSet<_> = Jar::all()
        .into_iter()
        .filter(|jar| !existing_jars.contains(jar))
        .collect();

    if !missing_jars.is_empty() {
        // download missing jars
        println!("[modelator] Downloading model-checkers... ");
        for jar in missing_jars {
            jar.download(&modelator_dir)?;
        }
        println!("[modelator] Done!");

        // if we have downloaded the jar(s) for the first time, check that we have a
        // compatible version of java
        check_java_version()?;

        // if we have downloaded the jar(s) for the first time, check that the
        // checksums match
        if !check_checksums(&modelator_dir)? {
            eprintln!("[modelator] Checksum of downloaded jars does not match the expected. Will try again!");

            // delete modelator dir and create it again
            std::fs::remove_dir_all(&modelator_dir).map_err(Error::io)?;
            std::fs::create_dir(&modelator_dir).map_err(Error::io)?;

            // try to download jars again
            return download_jars(modelator_dir);
        }
    }
    Ok(())
}

fn existing_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<Jar>, Error> {
    let existing_jars: HashSet<_> = list_jars(modelator_dir)?
        .into_iter()
        .map(|file_name| Jar::from(&file_name))
        .collect();
    assert!(
        existing_jars.len() <= 3,
        "[modelator] at most 3 jar files should have been downloaded"
    );
    Ok(existing_jars)
}

fn list_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<String>, Error> {
    let mut jars = HashSet::new();
    // read files the modelator directory
    for file_name in crate::util::read_dir(modelator_dir)? {
        if file_name.ends_with(".jar") {
            // if the file is a jar, then save it as already downloaded
            jars.insert(file_name);
        }
    }
    Ok(jars)
}

fn check_checksums<P: AsRef<Path>>(modelator_dir: P) -> Result<bool, Error> {
    let files_to_hash = list_jars(&modelator_dir)?
        .into_iter()
        .map(|filename| modelator_dir.as_ref().to_path_buf().join(filename))
        .map(|path| crate::util::absolute_path(&path))
        .collect();
    let digest = crate::util::digest::digest_files(files_to_hash)?;
    let hash = crate::util::digest::encode(digest);
    tracing::debug!("jars checksum: {} | expected: {}", hash, JARS_CHECKSUM);
    Ok(hash == JARS_CHECKSUM)
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
