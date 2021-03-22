use clap::Clap;
use modelator::CliOptions;

pub fn main() {
    let options = CliOptions::parse();
    options.run().exit()
}
