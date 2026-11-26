use std::ffi::OsStr;
use std::path::Path;

use crate::cli::ArgsHandler;
use crate::utils::run_command_with_output;

pub fn run<I: Iterator<Item = String>>(args: I) -> Result<(), String> {
    if ArgsHandler::<()>::new("abi-test").parse_args(args)?.is_none() {
        return Ok(());
    }

    // Ensure that we have a cloned version of abi-cafe on hand.
    crate::utils::git_clone(
        "https://github.com/Gankra/abi-cafe.git",
        Some("clones/abi-cafe".as_ref()),
        true,
    )
    .map_err(|err| format!("Git clone failed with message: {err:?}!"))?;
    // Configure abi-cafe to use the exact same rustc version we use - this is crucial.
    // Otherwise, the concept of ABI compatibility becomes meanignless.
    std::fs::copy("rust-toolchain.toml", "clones/abi-cafe/rust-toolchain.toml")
        .expect("Could not copy toolchain configs!");
    // Get the backend path.
    // We will use the *debug* build of the backend - it has more checks enabled.
    let backend_path = std::path::absolute("target/debug/librustc_codegen_gcc.so").unwrap();
    let backend_arg = format!("--add-rustc-codegen-backend=cg_gcc:{}", backend_path.display());
    // Run ABI cafe using cargo.
    let cmd: &[&dyn AsRef<OsStr>] = &[
        &"cargo",
        &"run",
        &"--release",
        &"--",
        &backend_arg,
        // Test rust-LLVM to Rust-GCC calls
        &"--pairs",
        &"rustc_calls_cg_gcc",
        &"--pairs",
        &"cg_gcc_calls_rustc",
        // Test Rust-GCC to C calls
        &"--pairs",
        &"cg_gcc_calls_c",
        &"--pairs",
        &"c_calls_cg_gcc",
    ];
    // Run ABI cafe.
    run_command_with_output(cmd, Some(Path::new("clones/abi-cafe")))?;

    Ok(())
}
