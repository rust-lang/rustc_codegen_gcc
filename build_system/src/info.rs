use std::collections::HashMap;

use crate::cli::ArgsHandler;
use crate::config::ConfigInfo;
use crate::utils::{run_command_with_env, setup_rustc_folder};

#[derive(Default)]
struct Info {
    show_gcc_path: bool,
    llvm_commit: bool,
    config: ConfigInfo,
}

fn show_llvm_commit() -> Result<(), String> {
    let env: HashMap<String, String> = std::env::vars().collect();
    let rust_dir_path = setup_rustc_folder(&env)?;

    let commit = String::from_utf8(
        run_command_with_env(
            &[&"git", &"rev-parse", &"HEAD:src/llvm-project"],
            Some(&rust_dir_path),
            None,
        )?
        .stdout,
    )
    .map_err(|error| format!("Invalid `git rev-parse HEAD:src/llvm-project` output: {error:?}"))?;
    println!("LLVM commit: {commit}");
    Ok(())
}

pub fn run() -> Result<(), String> {
    let Some(mut info) = ArgsHandler::<Info>::new("info")
        .with_flag("--show-gcc-path", "Display the path where gcc will be located", |obj| {
            obj.show_gcc_path = true;
        })
        .with_flag("--llvm-commit", "Display the LLVM submodule commit rustc is using", |obj| {
            obj.llvm_commit = true;
        })
        .with_sub_handler(ConfigInfo::args(), |info| &mut info.config)
        .parse_args(std::env::args().skip(2))?
    else {
        return Ok(());
    };

    info.config.no_download = true;

    if info.show_gcc_path {
        info.config.setup_gcc_path()?;
        if let Some(gcc_path) = info.config.gcc_path {
            println!("GCC path: {gcc_path}");
        }
    }
    if info.llvm_commit {
        show_llvm_commit()?;
    }
    Ok(())
}
