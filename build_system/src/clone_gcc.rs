use std::path::{Path, PathBuf};

use crate::cli::ArgsHandler;
use crate::config::ConfigInfo;
use crate::utils::{git_clone, run_command_with_output};

struct CloneGccArgs {
    out_path: PathBuf,
    config_info: ConfigInfo,
}

impl Default for CloneGccArgs {
    fn default() -> Self {
        Self { out_path: PathBuf::from("./gcc"), config_info: ConfigInfo::default() }
    }
}

pub fn run() -> Result<(), String> {
    let Some(args) = ArgsHandler::<CloneGccArgs>::new("clone-gcc")
        .with_non_empty_arg(
            "--out-path",
            "Location where the GCC repository will be cloned (default: `./gcc`)",
            |obj, arg| {
                obj.out_path = arg.into();
            },
        )
        .with_sub_handler(ConfigInfo::args(), |info| &mut info.config_info)
        .parse_args(std::env::args().skip(2))?
    else {
        return Ok(());
    };

    let result = git_clone("https://github.com/rust-lang/gcc", Some(&args.out_path), false)?;
    if result.ran_clone {
        let gcc_commit = args.config_info.get_gcc_commit()?;
        println!("Checking out GCC commit `{gcc_commit}`...");
        run_command_with_output(
            &[&"git", &"checkout", &gcc_commit],
            Some(Path::new(&result.repo_dir)),
        )?;
    } else {
        println!(
            "There is already a GCC folder in `{}`, leaving things as is...",
            args.out_path.display()
        );
    }
    Ok(())
}
