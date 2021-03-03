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

    let trace = modelator::run(options).await?;
    println!("{}", trace.join("\n"));
    Ok(())
}
