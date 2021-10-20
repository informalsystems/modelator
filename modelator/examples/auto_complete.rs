use clap::ArgEnum;
use clap::{IntoApp, Parser};
use clap_generate::generate;
use clap_generate::generators::{Bash, Elvish, Fish, PowerShell, Zsh};

#[derive(Debug, Parser)]
struct Cli {
    #[clap(arg_enum)]
    generator: ShellName,
}

#[derive(Debug, Clone, ArgEnum)]
enum ShellName {
    Bash,
    Elvish,
    Fish,
    Powershell,
    Zsh,
}

fn main() {
    let cli = Cli::parse();

    let mut app = modelator::cli::App::into_app();
    let app_name = app.get_name().to_owned();
    eprintln!("Generating completion file for {:?}...", cli.generator);

    match cli.generator {
        ShellName::Bash => generate(Bash, &mut app, app_name, &mut std::io::stdout()),
        ShellName::Elvish => generate(Elvish, &mut app, app_name, &mut std::io::stdout()),
        ShellName::Fish => generate(Fish, &mut app, app_name, &mut std::io::stdout()),
        ShellName::Powershell => generate(PowerShell, &mut app, app_name, &mut std::io::stdout()),
        ShellName::Zsh => generate(Zsh, &mut app, app_name, &mut std::io::stdout()),
    }
}
