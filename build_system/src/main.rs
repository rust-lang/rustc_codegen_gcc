use std::{env, process};

#[macro_use]
mod macros;
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

    let Some(command) = cli::ArgsHandler::<Command>::new("[command]")
        .with_unique("cargo", "Executes a cargo command", || Command::Cargo)
        .with_unique("clean", "Cleans the build directory, removing all compiled files and artifacts", || Command::Clean)
        .with_unique("clippy", "Runs clippy", || Command::Clippy)
        .with_unique("clone-gcc", "Clones the GCC compiler from a specified source", || Command::CloneGcc)
        .with_unique("prepare", "Prepares the environment for building, including fetching dependencies and setting up configurations", || Command::Prepare)
        .with_unique("build", "Compiles the project", || Command::Build)
        .with_unique("rustc", "Compiles the program using the GCC compiler", || Command::Rustc)
        .with_unique("test",  "Runs tests for the project", || Command::Test)
        .with_unique("info",  "Displays information about the build environment and project configuration", || Command::Info)
        .with_unique("fmt", "Runs rustfmt", || Command::Fmt)
        .with_unique("fuzz", "Fuzzes `cg_gcc` using `rustlantis`", || Command::Fuzz)
        .with_unique("abi-test", "Runs the abi-cafe test suite on the codegen, checking for ABI compatibility with LLVM", || Command::AbiTest)
        .with_unique("check-todo", "Checks todo in the project", || Command::CheckTodo)
        .parse_unique(std::env::args().skip(1)) else {
            return
    };
    if let Err(e) = match command {
        Command::Cargo => rust_tools::run_cargo(),
        Command::Rustc => rust_tools::run_rustc(),
        Command::Clean => clean::run(),
        Command::Prepare => prepare::run(),
        Command::Build => build::run(),
        Command::Test => test::run(),
        Command::Info => info::run(),
        Command::CloneGcc => clone_gcc::run(),
        Command::Fmt => fmt::run(),
        Command::Fuzz => fuzz::run(),
        Command::AbiTest => abi_test::run(),
        Command::Clippy => clippy::run(),
        Command::CheckTodo => todo::run(),
    } {
        eprintln!("Command failed to run: {e}");
        // CI needs to tell a build system error apart from the test failures some suites expect.
        let exit_code =
            if e == test::TESTS_FAILED_ERROR { test::TESTS_FAILED_EXIT_CODE } else { 1 };
        process::exit(exit_code);
    }
}
