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
    Modelator(modelator::Error),

    /// An error in the case that clap returns an error
    #[error("Clap returned an error: {0}")]
    Clap(clap::Error),

    /// An error in the case that serde returns an error
    #[error("Serde returned an error: {0}")]
    Serde(serde_json::Error),
}
