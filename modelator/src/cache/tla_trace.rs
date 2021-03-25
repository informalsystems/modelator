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
        options: &Options,
    ) -> Result<String, Error> {
        // parse tla file
        let tla_parsed_file = crate::module::Apalache::parse(tla_file.clone(), options)?;

        // read both the tla parsed file and the tla config file
        let tla_parsed = std::fs::read_to_string(tla_parsed_file.path()).map_err(Error::io)?;
        let tla_config = std::fs::read_to_string(tla_config_file.path()).map_err(Error::io)?;

        // cleanup tla parse file
        std::fs::remove_file(tla_parsed_file.path())
            .expect("[modelator] it should be possible to remove tla parsed file just created");

        // combine both and hash them
        let combined = tla_parsed + &tla_config;
        let hash = sha256::digest(&combined);
        Ok(hash)
    }
}
