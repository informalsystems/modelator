use modelator::CliOptions;
use clap::Clap;

pub fn main() {
    let options = CliOptions::parse();
    println!("{:?}", options);
}
