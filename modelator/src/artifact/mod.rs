pub(crate) mod json_trace;
pub(crate) mod tla_cfg_file;
pub(crate) mod tla_file;
pub(crate) mod tla_trace;

// Re-exports.
pub use json_trace::JsonTrace;
pub use tla_cfg_file::TlaConfigFile;
pub use tla_file::TlaFile;
pub use tla_trace::TlaTrace;

use serde::de::DeserializeOwned;
use serde::Serialize;

/// Artifacts should be able to serialized (into a string/file) and deserialized
/// (from string/file).
pub trait Artifact: Serialize + DeserializeOwned {}

// TODO: Assert that all artifacts implement the above trait.
//       Maybe also require: Debug, Clone, PartialEq, Eq