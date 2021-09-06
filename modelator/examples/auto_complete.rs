use clap::{App, ArgEnum};
use clap::{Clap, IntoApp};
use clap_generate::generators::{Bash, Elvish, Fish, PowerShell, Zsh};
use clap_generate::{generate, Generator};

#[derive(Debug, Clap)]
struct Cli {
    #[clap(arg_enum)]
    generator: ShellName,
}

#[derive(Debug, ArgEnum)]
enum ShellName {
    Bash,
    Elvish,
    Fish,
    Powershell,
    Zsh,
}

fn print_completions<G: Generator>(app: &mut App) {
    generate::<G, _>(app, app.get_name().to_string(), &mut std::io::stdout());
}

fn main() {
    let cli = Cli::parse();

    let mut modelator_app = modelator::cli::App::into_app();
    eprintln!("Generating completion file for {:?}...", cli.generator);
    match cli.generator {
        ShellName::Bash => print_completions::<Bash>(&mut modelator_app),
        ShellName::Elvish => print_completions::<Elvish>(&mut modelator_app),
        ShellName::Fish => print_completions::<Fish>(&mut modelator_app),
        ShellName::Powershell => print_completions::<PowerShell>(&mut modelator_app),
        ShellName::Zsh => print_completions::<Zsh>(&mut modelator_app),
    }
}
