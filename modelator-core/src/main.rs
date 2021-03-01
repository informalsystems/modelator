use modelator_core::{Options, Workers};

#[tokio::main]
async fn main() -> Result<(), modelator_core::Error> {
    let options = Options::new("IBCTests")
        .tlc()
        .workers(Workers::Auto)
        .test("ICS03ConnectionOpenConfirmOKTest")
        .log("tlc.log");

    let traces = modelator_core::run(options).await?;
    println!("TRACES:\n{:#?}", traces);
    Ok(())
}
