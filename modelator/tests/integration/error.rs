use crate::common::{Test, TestBatchConfig};
use thiserror::Error;

/// Set of possible errors that can occur when running an integration test
#[derive(Error, Debug)]
pub enum IntegrationTestError {
    /// An error in the integration test is itself incorrectly specified
    #[error("The integration test is itself incorrectly specified: {0}")]
    FaultyTest(String),

    /// An error in the case the expected value is wrong
    #[error("Unexpected value from running test: expect {0}, actual {1}")]
    ExpectedValueMismatch(String, String),

    /// An error in the case that modelator returns an error
    #[error("Modelator returned an error: {0}")]
    Modelator(#[from] modelator::Error),

    /// An error in the case that clap returns an error
    #[error("Clap returned an error: {0}")]
    Clap(#[from] clap::Error),

    /// An error in the case that serde returns an error
    #[error("Serde returned an error: {0}")]
    Serde(#[from] serde_json::Error),
}

#[derive(Error, Debug)]
#[error(
    "Test '{0}' in batch '{1}' failed. [name:{2}, batch_name:{3}, description:{4}] Error: {5}",
    test.name,
    batch_config.name,
    test.name,
    batch_config.name,
    batch_config.description,
    error_str
)]
pub struct IntegrationTestFailure {
    pub error_str: String,
    pub test: Test,
    pub batch_config: TestBatchConfig,
}
