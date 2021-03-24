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

    pub(crate) fn get(
        &self,
        tla_file: &TlaFile,
        tla_config_file: &TlaConfigFile,
        options: &Options,
    ) -> Result<Option<TlaTrace>, Error> {
        let key = Self::cache_key(tla_file, tla_config_file, options)?;
        self.cache.get(&key)?.map(|value| value.parse()).transpose()
    }

    pub(crate) fn insert(
        &mut self,
        tla_file: &TlaFile,
        tla_config_file: &TlaConfigFile,
        tla_trace: &TlaTrace,
        options: &Options,
    ) -> Result<(), Error> {
        let key = Self::cache_key(tla_file, tla_config_file, options)?;
        let value = tla_trace.to_string();
        self.cache.insert(key, value)
    }

    fn cache_key(
        tla_file: &TlaFile,
        tla_config_file: &TlaConfigFile,
        options: &Options,
    ) -> Result<String, Error> {
        // parse tla file
        let tla_parsed_file = crate::module::Apalache::parse(tla_file.clone(), options)?;

        // read both the tla parsed file and the tla config file
        let tla_parsed = std::fs::read_to_string(tla_parsed_file.path()).map_err(Error::io)?;
        let tla_config = std::fs::read_to_string(tla_config_file.path()).map_err(Error::io)?;

        // combine both and hash them
        let combined = tla_parsed + &tla_config;
        let hash = sha256::digest(&combined);
        Ok(hash)
    }
}
