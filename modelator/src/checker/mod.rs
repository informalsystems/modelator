// TLC module.
mod tlc;

// Apalache module.
mod apalache;

/// Modelator's options.
mod options;

// Re-exports.
pub use apalache::{error::ApalacheError, Apalache};
pub use options::{ModelChecker, ModelCheckerOptions, ModelCheckerWorkers, CheckerBuilder};
pub use tlc::Tlc;
