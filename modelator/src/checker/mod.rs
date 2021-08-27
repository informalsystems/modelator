// TLC module.
mod tlc;

// Apalache module.
pub(crate) mod apalache;

// Re-exports.
pub use apalache::{error_message::ErrorMessage, Apalache};
pub use tlc::Tlc;
