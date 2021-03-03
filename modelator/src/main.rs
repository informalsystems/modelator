use clap::Clap;
use modelator::{Error, Options};

#[tokio::main]
async fn main() -> Result<(), Error> {
    let _options = Options::new("IBCTests.tla")
        .tlc()
        .workers(modelator::Workers::Auto)
        .test("ICS03ConnectionOpenConfirmOKTest")
        .log("tlc.log");

    // cargo run -- IBCTests.tla -r test,ICS03ConnectionOpenConfirmOKTest
    let options = Options::parse();
    let traces = modelator::traces(options).await?;

    // aggregate all traces into a json array (and each trace into a json array
    // as well)
    let json = serde_json::Value::Array(
        traces
            .into_iter()
            .map(|trace| serde_json::Value::Array(trace.into_iter().collect::<Vec<_>>()))
            .collect::<Vec<_>>(),
    );
    let pretty = serde_json::to_string_pretty(&json).map_err(Error::Serde)?;
    println!("{}", pretty);
    Ok(())
}
