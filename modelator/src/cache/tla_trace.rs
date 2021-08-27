use super::Cache;
use crate::artifact::{TlaConfigFile, TlaFile, TlaTrace};
use crate::{Error, Options};

pub(crate) struct TlaTraceCache {
    cache: Cache,
}

impl TlaTraceCache {
    pub(crate) fn new(options: &Options) -> Result<Self, Error> {
        let cache = Cache::new(options)?;
        Ok(Self { cache })
    }

    #[allow(clippy::ptr_arg)]
    pub(crate) fn get(&self, _key: &String) -> Result<Option<TlaTrace>, Error> {
        todo!()
        /*
        TODO: This is disabled as it is using the old system of implicit pathing and must be reworked a bit.
        It it not the highest priority for 0.3.0
        self.cache.get(key)?.map(|value| value.parse()).transpose()
        */
    }

    pub(crate) fn insert(&mut self, key: String, tla_trace: &TlaTrace) -> Result<(), Error> {
        // TODO: this to_string is Display trait's, but maybe we want our own repr.
        let value = tla_trace.to_string();
        self.cache.insert(key, value)
    }

    pub(crate) fn key(
        _tla_file: &TlaFile,
        _tla_config_file: &TlaConfigFile,
    ) -> Result<String, Error> {
        todo!();
        /*
        TODO: This is disabled as it is using the old system of implicit pathing and must be reworked a bit.
        It it not the highest priority for 0.3.0


        tracing::debug!("TlaTraceKey:key {} {}", tla_file, tla_config_file);

        // get all tla files in the same directory
        let mut tla_dir = tla_file.path().to_path_buf();
        assert!(tla_dir.pop());

        let files_to_hash = crate::util::read_dir(&tla_dir)?
            .into_iter()
            .filter(|filename| filename.ends_with(".tla"))
            // compute full path
            .map(|filename| tla_dir.join(filename))
            // also hash the tla config file
            .chain(std::iter::once(tla_config_file.path().to_path_buf()))
            .map(|path| crate::util::absolute_path(&path))
            // sort files so that the hash is deterministic
            .collect();

        tracing::debug!("files to hash: {:?}", files_to_hash);
        let mut digest = crate::util::digest::digest_files(files_to_hash)?;

        // also add the absolute path of the tla file to the digest; this makes
        // sure that two tla tests files living in the same directory and using
        // the same tla configuration (which we shouldn't happen when using
        // `modelator::module::tla::generate_tests`) will have different hashes
        use sha2::Digest;
        digest.update(&crate::util::absolute_path(&tla_file.path()));

        let hash = crate::util::digest::encode(digest);
        tracing::debug!("computed hash: {}", hash);
        Ok(hash)


        */
    }
}
