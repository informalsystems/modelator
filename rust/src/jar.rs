use crate::error::Error;
use crate::model::language::Tla;
use std::collections::{HashMap, HashSet};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use sha2::Digest;

// The minimum java version supported by Apalache is Java 8:
// https://apalache.informal.systems/docs/apalache/system-reqs.html
// TLC doesn't seem to have such requirement.
const MIN_JAVA_VERSION: usize = 8;

lazy_static::lazy_static! {
    /// This is an example for using doc comment attributes
    static ref TLA_JAR: TlaJar = TlaJar::latest();
    static ref COMMUNITY_MODULES_JAR: CommunityModuleJar = CommunityModuleJar::latest();
    static ref APALACHE_JAR: ApalacheJar = ApalacheJar::latest();
}

trait Asset {
    fn template_link() -> &'static str;
    fn template_name() -> &'static str;
    fn version_with_hash() -> Vec<(&'static str, &'static str)>;
    fn download_and_save<W: Write>(&self, _: W) -> Result<(), Error>;
    fn latest() -> Self;

    fn version(&self) -> &str;

    fn latest_version() -> &'static str {
        Self::version_with_hash()[0].0
    }

    fn file_name(&self) -> String {
        Self::template_name().replace("{VERSION}", self.version())
    }
    fn valid<P: AsRef<Path>>(&self, path: P) -> Result<bool, Error> {
        if self.is_present(&path) {
            let expected_hash = self.get_hash();
            match expected_hash.as_ref() {
                "SKIP" => Ok(true),
                _ => Ok(self.get_hash() == self.sha256sum(&path)?),
            }
        } else {
            Ok(false)
        }
    }
    fn get_hash(&self) -> String {
        Self::version_with_hash()
            .iter()
            .find(|(v, _)| v == &self.version())
            .unwrap()
            .1
            .into()
    }
    fn file_path<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        path.as_ref().to_path_buf().join(self.file_name())
    }
    fn is_present<P: AsRef<Path>>(&self, path: P) -> bool {
        self.file_path(path).is_file()
    }
    fn link(&self) -> String {
        Self::template_link().replace("{VERSION}", self.version())
    }
    fn sha256sum<P: AsRef<Path>>(&self, path: P) -> Result<String, Error> {
        let mut digest = sha2::Sha256::default();
        let file = std::fs::File::open(self.file_path(path))?;
        let mut reader = std::io::BufReader::new(file);

        let mut buffer = [0; 1024];
        loop {
            use std::io::Read;
            let count = reader.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            digest.update(&buffer[..count]);
        }

        Ok(hex::encode(digest.finalize()))
    }
    fn prepare<P: AsRef<Path>>(&self, path: P) -> Result<(), Error> {
        if self.valid(&path)? {
            Ok(())
        } else {
            let writer = BufWriter::new(std::fs::File::create(self.file_path(&path))?);
            self.download_and_save(writer)?;
            if self.valid(&path)? {
                Ok(())
            } else {
                Err(Error::IO("problem downloading assets".into()))
            }
        }
    }
}

struct TlaJar {
    version: String,
}

impl Asset for TlaJar {
    fn template_link() -> &'static str {
        "https://github.com/tlaplus/tlaplus/releases/download/v{VERSION}/tla2tools.jar"
    }

    fn template_name() -> &'static str {
        "tla2tools.jar"
    }

    fn version_with_hash() -> Vec<(&'static str, &'static str)> {
        vec![(
            "1.8.0",
            "d7d491946f62c9b2606e7b0ff0d3db88739b16204f23410ea4fba2db6fb6cc38",
        )]
    }

    fn download_and_save<W: Write>(&self, writer: W) -> Result<(), Error> {
        println!("Fetching {} from {}", self.file_name(), self.link());
        // download the jar
        let response = ureq::get(&self.link()).call()?;
        let mut reader = response.into_reader();

        // write jar bytes to the file
        let mut file_writer = std::io::BufWriter::new(writer);
        std::io::copy(&mut reader, &mut file_writer)?;
        Ok(())
    }

    fn version(&self) -> &str {
        self.version.as_ref()
    }

    fn latest() -> Self {
        Self {
            version: Self::latest_version().into(),
        }
    }
}

struct CommunityModuleJar {
    version: String,
}

impl Asset for CommunityModuleJar {
    fn template_link() -> &'static str {
        "https://github.com/tlaplus/CommunityModules/releases/download/{VERSION}/CommunityModules-{VERSION}.jar"
    }
    fn template_name() -> &'static str {
        "CommunityModules-{VERSION}.jar"
    }

    fn version_with_hash() -> Vec<(&'static str, &'static str)> {
        vec![(
            "202112070657",
            "92b162418d2bafbe58016d47896847c9dd771ff230d6474fdec9049068559b3b",
        )]
    }

    fn download_and_save<W: Write>(&self, writer: W) -> Result<(), Error> {
        println!("Fetching {} from {}", self.file_name(), self.link());
        // download the jar
        let response = ureq::get(&self.link()).call()?;
        let mut reader = response.into_reader();

        // write jar bytes to the file
        let mut file_writer = std::io::BufWriter::new(writer);
        std::io::copy(&mut reader, &mut file_writer)?;
        Ok(())
    }

    fn version(&self) -> &str {
        self.version.as_ref()
    }

    fn latest() -> Self {
        Self {
            version: Self::latest_version().into(),
        }
    }
}

struct ApalacheJar {
    version: String,
}

impl Asset for ApalacheJar {
    fn template_link() -> &'static str {
        "https://github.com/informalsystems/apalache/releases/download/v{VERSION}/apalache.zip"
    }

    fn template_name() -> &'static str {
        "apalache-pkg-{VERSION}-full.jar"
    }

    fn version_with_hash() -> Vec<(&'static str, &'static str)> {
        vec![(
            "0.18.0",
            "26610a5c73ba25f40e6af9854dbd1c4e2fcffd9d89c549f3fcdd90c4e04bbd4a",
        )]
    }

    fn download_and_save<W: Write>(&self, writer: W) -> Result<(), Error> {
        println!("Fetching {} from {}", self.file_name(), self.link());
        // download the zip
        let response = ureq::get(&self.link()).call()?;
        let mut cursor = std::io::Cursor::new(Vec::new());
        std::io::copy(&mut response.into_reader(), &mut cursor)?;

        // extract zip
        let mut archive = zip::ZipArchive::new(cursor).unwrap();
        let mut reader = archive
            .by_name(&format!(
                "mod-distribution/target/apalache-pkg-{}-full.jar",
                self.version()
            ))
            .map_err(|_| Error::IO("failed to extract".into()))?;
        // write jar bytes to the file
        let mut file_writer = std::io::BufWriter::new(writer);
        std::io::copy(&mut reader, &mut file_writer)?;
        Ok(())
    }

    fn version(&self) -> &str {
        self.version.as_ref()
    }

    fn latest() -> Self {
        Self {
            version: Self::latest_version().into(),
        }
    }
}

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

    fn file_name(&self) -> String {
        match self {
            Self::Tla => TLA_JAR.file_name(),
            Self::CommunityModules => COMMUNITY_MODULES_JAR.file_name(),
            Self::Apalache => APALACHE_JAR.file_name(),
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
        let response = ureq::get(&self.link()).call()?;
        let mut reader = response.into_reader();

        // write jar bytes to the file
        let file = std::fs::File::create(path)?;
        let mut file_writer = std::io::BufWriter::new(file);
        std::io::copy(&mut reader, &mut file_writer)?;
        Ok(())
    }

    const fn all() -> [Self; 3] {
        [Self::Tla, Self::CommunityModules, Self::Apalache]
    }
}

// We can't use TryFrom<AsRef<str>> because of the following
// https://github.com/rust-lang/rust/issues/50133
impl<'a> TryFrom<&'a str> for Jar {
    type Error = &'a str;
    fn try_from(file_name: &'a str) -> Result<Self, Self::Error> {
        if file_name == TLA_JAR.file_name() {
            Ok(Self::Tla)
        } else if file_name == COMMUNITY_MODULES_JAR.file_name() {
            Ok(Self::CommunityModules)
        } else if file_name == APALACHE_JAR.file_name() {
            Ok(Self::Apalache)
        } else {
            Err(file_name)
        }
    }
}

// pub(crate) fn download_jars_if_necessary<P: AsRef<Path>>(modelator_dir: P) -> Result<(), Error> {
//     // get all existing jars
//     let existing_jars = existing_jars(&modelator_dir)?;
//     // compute jars that are missing
//     let missing_jars: HashSet<_> = Jar::all()
//         .into_iter()
//         .filter(|jar| !existing_jars.contains(jar))
//         .collect();

//     if !missing_jars.is_empty() {
//         // download missing jars
//         println!(
//             "[modelator] Downloading model-checkers at \"{}\"...",
//             modelator_dir.as_ref().to_string_lossy()
//         );
//         for jar in missing_jars {
//             jar.download(&modelator_dir)?;
//         }
//         println!("[modelator] Done!");

//         // if we have downloaded the jar(s) for the first time, check that we have a
//         // compatible version of java
//         check_java_version()?;

//         // if we have downloaded the jar(s) for the first time, check that the
//         // checksums match
//         if !checksums_correct(&modelator_dir)? {
//             eprintln!("[modelator] Checksum of downloaded jars does not match the expected. Will try again!");

//             // delete modelator dir and create it again
//             std::fs::remove_dir_all(&modelator_dir)?;
//             std::fs::create_dir(&modelator_dir)?;

//             // try to download jars again
//             return download_jars_if_necessary(modelator_dir);
//         }
//     }
//     Ok(())
// }

pub(crate) fn prepare_modelator_data_dir<P: AsRef<Path>>(modelator_dir: P) -> Result<(), Error> {
    TLA_JAR.prepare(&modelator_dir)?;
    COMMUNITY_MODULES_JAR.prepare(&modelator_dir)?;
    APALACHE_JAR.prepare(&modelator_dir)?;
    Ok(())
}

fn existing_jars<P: AsRef<Path>>(modelator_dir: P) -> Result<HashSet<Jar>, Error> {
    let existing_jars: HashSet<_> = list_jars(&modelator_dir)?
        .into_iter()
        .flat_map(|file_name| match file_name.as_str().try_into() {
            Ok(jar) => Some(Ok(jar)),
            Err(file_name) => {
                match std::fs::remove_file(modelator_dir.as_ref().to_path_buf().join(file_name)) {
                    Err(e) => Some(Err(Error::IO(format!("IO error: {:?}", e)))),
                    _ => None,
                }
            }
        })
        .collect::<Result<_, Error>>()?;
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

// fn checksums_correct<P: AsRef<Path>>(modelator_dir: P) -> Result<bool, Error> {
//     let files_to_hash = list_jars(&modelator_dir)?
//         .into_iter()
//         .map(|filename| modelator_dir.as_ref().to_path_buf().join(filename))
//         .map(|path| crate::util::absolute_path(&path))
//         .collect();
//     let digest = crate::util::digest::digest_files(files_to_hash)?;
//     let hash = crate::util::digest::encode(digest);
//     tracing::debug!("jars checksum: {} | expected: {}", hash, JARS_CHECKSUM);
//     Ok(hash == JARS_CHECKSUM)
// }

fn check_java_version() -> Result<(), Error> {
    let mut cmd = Command::new("java");
    cmd.arg("-XshowSettings:all").arg("-version");
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
                .split('.')
                .last()
                .unwrap()
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
