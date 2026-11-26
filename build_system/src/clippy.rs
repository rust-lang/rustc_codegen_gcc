use std::path::Path;

use crate::cli::ArgsHandler;
use crate::utils::{run_command_with_output, run_tool_and_install_it_if_not_present};

pub fn run<I: Iterator<Item = String>>(args: I) -> Result<(), String> {
    if ArgsHandler::<()>::new("clippy").parse_args(args)?.is_none() {
        return Ok(());
    }

    run_tool_and_install_it_if_not_present(&[
        &"cargo",
        &"clippy",
        &"--all-targets",
        &"--",
        &"-D",
        &"warnings",
    ])?;
    run_command_with_output(
        &[
            &"cargo",
            &"clippy",
            &"--all-targets",
            &"--no-default-features",
            &"--",
            &"-D",
            &"warnings",
        ],
        Some(Path::new(".")),
    )?;
    run_command_with_output(
        &[
            &"cargo",
            &"clippy",
            &"--all-targets",
            &"--manifest-path",
            &"build_system/Cargo.toml",
            &"--",
            &"-D",
            &"warnings",
        ],
        Some(Path::new(".")),
    )?;
    Ok(())
}
