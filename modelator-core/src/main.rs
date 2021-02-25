#[tokio::main]
async fn main() -> Result<(), modelator_core::Error> {
    let traces = modelator_core::run(
        "MC.tla",
        "MC.cfg",
        vec!["inv"],
        modelator_core::Config::default(),
    )
    .await?;
    println!("TRACES:\n{:#?}", traces);
    Ok(())
}
