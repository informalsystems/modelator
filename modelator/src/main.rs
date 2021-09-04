use clap::Clap;

pub fn main() {
    let cli_app = modelator::cli::App::parse();
    cli_app.run().exit()
}
