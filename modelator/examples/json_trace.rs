use modelator::{Error, Options};

fn main() -> Result<(), Error> {
    let options = Options::default();
    let traces = modelator::traces(
        "tests/integration/tla/NumbersAMaxBMinTest.tla",
        "tests/integration/tla/Numbers.cfg",
        options,
    )?;

    traces.into_iter().for_each(|trace| {
        println!("{}", trace);
    });
    Ok(())
}
