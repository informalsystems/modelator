use clap::Clap;

pub fn main() {
    let options = modelator::CliOptions::parse();
    options.run().exit()
}
