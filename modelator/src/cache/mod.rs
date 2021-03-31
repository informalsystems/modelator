// cache for `TlaTrace`s.
mod tla_trace;

// Re-exports;
pub(crate) use tla_trace::TlaTraceCache;

use crate::{Error, Options};
use std::collections::HashSet;
use std::path::PathBuf;

pub(crate) struct Cache {
    cache_dir: PathBuf,
    cached_keys: HashSet<String>,
}

impl Cache {
    pub(crate) fn new(options: &Options) -> Result<Self, Error> {
        // create cache dir (if it doesn't exist)
        let cache_dir = options.dir.join("cache");
        std::fs::create_dir_all(&cache_dir).map_err(Error::io)?;

        // read files the cache directory
        let cached_keys = crate::util::read_dir(&cache_dir)?;

        Ok(Self {
            cache_dir,
            cached_keys,
        })
    }

    #[allow(clippy::ptr_arg)]
    pub(crate) fn get(&self, key: &String) -> Result<Option<String>, Error> {
        let value = if self.cached_keys.contains(key) {
            // if this key is cached, read it from disk
            let path = self.key_path(key);
            let value = std::fs::read_to_string(path).map_err(Error::io)?;
            Some(value)
        } else {
            None
        };
        Ok(value)
    }

    pub(crate) fn insert(&mut self, key: String, value: String) -> Result<(), Error> {
        // for each key, there exists at most one value; so we panic in case
        // we're trying insert a key already cached
        assert!(
            !self.cached_keys.contains(&key),
            "[modelator] trying to cache a key already cached"
        );

        // write the value associated with this key to disk
        let path = self.key_path(&key);
        std::fs::write(path, value).map_err(Error::io)?;

        // mark the key as cached
        self.cached_keys.insert(key);
        Ok(())
    }

    #[allow(clippy::ptr_arg)]
    fn key_path(&self, key: &String) -> PathBuf {
        self.cache_dir.join(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_works() {
        let modelator_dir = "cache_works";
        let options = Options::default().dir(modelator_dir);

        // create cache
        let mut cache = Cache::new(&options).unwrap();

        let key_a = "A".to_string();
        let value_a = "some value for A".to_string();
        let key_b = "B".to_string();

        // at the beginning, no key is cached
        assert!(cache.get(&key_a).unwrap().is_none());
        assert!(cache.get(&key_b).unwrap().is_none());

        // cache key A
        cache.insert(key_a.clone(), value_a.clone()).unwrap();

        // now key A is cached
        assert_eq!(cache.get(&key_a).unwrap(), Some(value_a.clone()));
        assert!(cache.get(&key_b).unwrap().is_none());

        // start a new cache a check that it reads the cached keys from disk
        let cache = Cache::new(&options).unwrap();
        assert_eq!(cache.get(&key_a).unwrap(), Some(value_a));
        assert!(cache.get(&key_b).unwrap().is_none());

        // cleanup
        std::fs::remove_dir_all(modelator_dir).unwrap();
    }
}
