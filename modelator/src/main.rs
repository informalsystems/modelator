use modelator::{Error, Options};

fn main() -> Result<(), Error> {
    let options = Options::default();
    let traces = modelator::traces("IBCTests.tla", "IBCTests.cfg", options)?;

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
