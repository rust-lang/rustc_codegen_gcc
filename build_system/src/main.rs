use std::{env, process};

mod abi_test;
mod build;
mod clean;
mod cli;
mod clippy;
mod clone_gcc;
mod config;
mod fmt;
mod fuzz;
mod info;
mod prepare;
mod rust_tools;
mod rustc_info;
mod test;
mod todo;
mod utils;
const BUILD_DIR: &str = "build";

enum Command {
    Cargo,
    Clean,
    Clippy,
    CloneGcc,
    Prepare,
    Build,
    Rustc,
    Test,
    Info,
    Fmt,
    Fuzz,
    AbiTest,
    CheckTodo,
}

fn main() {
    if env::var("RUST_BACKTRACE").is_err() {
        unsafe {
            env::set_var("RUST_BACKTRACE", "1");
        }
    }

    let mut args = std::env::args().skip(1);

    match cli::CommandsHandler::<Command>::new("[command] [options]")
        .with_command("cargo", "Executes a cargo command", Command::Cargo)
        .with_command("clean", "Cleans the build directory, removing all compiled files and artifacts", Command::Clean)
        .with_command("clippy", "Runs clippy", Command::Clippy)
        .with_command("clone-gcc", "Clones the GCC compiler from a specified source", Command::CloneGcc)
        .with_command("prepare", "Prepares the environment for building, including fetching dependencies and setting up configurations", Command::Prepare)
        .with_command("build", "Compiles the project", Command::Build)
        .with_command("rustc", "Compiles the program using the GCC compiler", Command::Rustc)
        .with_command("test",  "Runs tests for the project", Command::Test)
        .with_command("info",  "Displays information about the build environment and project configuration", Command::Info)
        .with_command("fmt", "Runs rustfmt", Command::Fmt)
        .with_command("fuzz", "Fuzzes `cg_gcc` using `rustlantis`", Command::Fuzz)
        .with_command("abi-test", "Runs the abi-cafe test suite on the codegen, checking for ABI compatibility with LLVM", Command::AbiTest)
        .with_command("check-todo", "Checks todo in the project", Command::CheckTodo)
        .parse_args(&mut args)
    {
        Ok(Some(command)) => {
            if let Err(e) = match command {
                Command::Cargo => rust_tools::run_cargo(args),
                Command::Rustc => rust_tools::run_rustc(args),
                Command::Clean => clean::run(args),
                Command::Prepare => prepare::run(args),
                Command::Build => build::run(args),
                Command::Test => test::run(args),
                Command::Info => info::run(args),
                Command::CloneGcc => clone_gcc::run(args),
                Command::Fmt => fmt::run(args),
                Command::Fuzz => fuzz::run(args),
                Command::AbiTest => abi_test::run(args),
                Command::Clippy => clippy::run(args),
                Command::CheckTodo => todo::run(args),
            } {
                eprintln!("Command failed to run: {e}");
                // CI needs to tell a build system error apart from the test failures some suites expect.
                let exit_code =
                    if e == test::TESTS_FAILED_ERROR { test::TESTS_FAILED_EXIT_CODE } else { 1 };
                process::exit(exit_code);
            }
        }
        Ok(None) => {}
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
