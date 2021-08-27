// TLC module.
mod tlc;

// Apalache module.
mod apalache;

/// Modelator's options.
mod model_checker;

// Re-exports.
pub use apalache::{error::ApalacheError, Apalache};
pub use model_checker::{ModelChecker, ModelCheckerRuntime, ModelCheckerWorkers, ModelatorRuntime};
pub use tlc::Tlc;
