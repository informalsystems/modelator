use clap::AppSettings;
use clap::Clap;

#[derive(Clap)]
#[clap(help_heading = "INPUT")]
pub struct InputOpts {
    #[clap(about = "Path to the input file")]
    pub input: String,
}

#[derive(Clap)]
#[clap(
	global_setting = AppSettings::ColoredHelp,
	global_setting = AppSettings::DeriveDisplayOrder,
)]
struct Opts {
    #[clap(flatten)]
    input: InputOpts,
}

fn main() {
    let _opts: Opts = Opts::parse();
}
