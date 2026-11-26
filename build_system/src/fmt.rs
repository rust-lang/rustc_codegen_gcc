use std::ffi::OsStr;
use std::path::Path;

use crate::cli::ArgsHandler;
use crate::utils::{run_command_with_output, run_tool_and_install_it_if_not_present, walk_dir};

pub fn run<I: Iterator<Item = String>>(args: I) -> Result<(), String> {
    if let Some(check) = ArgsHandler::<bool>::new("fmt")
        .with_flag("--check", "Pass `--check` argument to `cargo fmt` commands", |check| {
            *check = true
        })
        .parse_args(args)?
    {
        let cmd: &[&dyn AsRef<OsStr>] =
            if check { &[&"cargo", &"fmt", &"--check"] } else { &[&"cargo", &"fmt"] };

        run_tool_and_install_it_if_not_present(cmd)?;
        run_command_with_output(cmd, Some(Path::new("build_system")))?;
        run_command_with_output(cmd, Some(Path::new("build_system/asm-tester")))?;

        run_rustfmt_recursively("tests/run", check)
    } else {
        Ok(())
    }
}

fn run_rustfmt_recursively<P>(dir: P, check: bool) -> Result<(), String>
where
    P: AsRef<Path>,
{
    walk_dir(
        dir,
        &mut |dir| run_rustfmt_recursively(dir, check),
        &mut |file_path| {
            if file_path.extension().filter(|ext| ext == &OsStr::new("rs")).is_some() {
                let rustfmt_cmd: &[&dyn AsRef<OsStr>] = if check {
                    &[&"rustfmt", &"--check", &file_path]
                } else {
                    &[&"rustfmt", &file_path]
                };

                run_command_with_output(rustfmt_cmd, Some(Path::new(".")))
            } else {
                Ok(())
            }
        },
        true,
    )
}
