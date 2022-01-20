use clap::Parser;

pub fn main() {
    let cli_app = modelator::cli::App::parse();

    if !cli_app.try_print_completions() {
        cli_app.run().exit()
    }
}
