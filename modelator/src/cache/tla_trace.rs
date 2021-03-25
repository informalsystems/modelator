use super::Cache;
use crate::artifact::{TlaConfigFile, TlaFile, TlaTrace};
use crate::{Error, Options};
use sha2::Digest;
use std::collections::BTreeSet;

pub(crate) struct TlaTraceCache {
    cache: Cache,
}

impl TlaTraceCache {
    pub(crate) fn new(options: &Options) -> Result<Self, Error> {
        let cache = Cache::new(options)?;
        Ok(Self { cache })
    }

    #[allow(clippy::ptr_arg)]
    pub(crate) fn get(&self, key: &String) -> Result<Option<TlaTrace>, Error> {
        self.cache.get(&key)?.map(|value| value.parse()).transpose()
    }

    pub(crate) fn insert(&mut self, key: String, tla_trace: &TlaTrace) -> Result<(), Error> {
        let value = tla_trace.to_string();
        self.cache.insert(key, value)
    }

    pub(crate) fn key(
        tla_file: &TlaFile,
        tla_config_file: &TlaConfigFile,
    ) -> Result<String, Error> {
        tracing::debug!("TlaTraceKey:key {} {}", tla_file, tla_config_file);

        // get all tla files in the same directory
        let mut tla_dir = tla_file.path().clone();
        assert!(tla_dir.pop());

        let files_to_hash = crate::util::read_dir(&tla_dir)?
            .into_iter()
            .filter(|filename| filename.ends_with(".tla"))
            // compute full path
            .map(|filename| tla_dir.join(filename))
            // also hash the tla config file
            .chain(std::iter::once(tla_config_file.path().clone()))
            .map(|path| crate::util::absolute_path(&path))
            // sort files so that the hash is deterministic
            .collect();

        tracing::debug!("files to hash: {:?}", files_to_hash);
        let mut digest = hash_files(files_to_hash)?;

        // also add the absolute path of the tla file to the digest; this makes
        // sure that two tla tests files living in the same directory and using
        // the same tla configuration (which we shouldn't happen when using
        // `modelator::module::tla::generate_tests`) will have different hashes
        digest.update(&crate::util::absolute_path(&tla_file.path()));

        let hash = hex::encode(digest.finalize());
        tracing::debug!("computed hash: {}", hash);
        Ok(hash)
    }
}

fn hash_files(paths: BTreeSet<String>) -> Result<sha2::Sha256, Error> {
    let mut digest = sha2::Sha256::default();
    for path in paths {
        hash_file(path, &mut digest)?;
    }
    Ok(digest)
}

fn hash_file(path: String, digest: &mut sha2::Sha256) -> Result<(), Error> {
    let file = std::fs::File::open(path).map_err(Error::io)?;
    let mut reader = std::io::BufReader::new(file);

    let mut buffer = [0; 1024];
    loop {
        use std::io::Read;
        let count = reader.read(&mut buffer).map_err(Error::io)?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }

    Ok(())
}
