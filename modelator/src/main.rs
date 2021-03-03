use clap::Clap;
use modelator::Options;

#[tokio::main]
async fn main() -> Result<(), modelator::Error> {
    let _options = Options::new("IBCTests")
        .tlc()
        .workers(modelator::Workers::Auto)
        .test("ICS03ConnectionOpenConfirmOKTest")
        .log("tlc.log");

    let options: Options = Options::parse();

    let traces = modelator::run(options).await?;
    println!("TRACES:\n{:#?}", traces);
    Ok(())
}
