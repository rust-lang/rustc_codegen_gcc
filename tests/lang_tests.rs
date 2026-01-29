#![allow(clippy::uninlined_format_args)]

use std::env::current_dir;
use std::path::{Path, PathBuf};
use std::process::Command;

use lang_tester::LangTester;
use tempfile::TempDir;

fn compile_and_run_cmds(
    compiler_args: Vec<String>,
    test_target: &Option<String>,
    exe: &Path,
) -> Vec<(&'static str, Command)> {
    let mut compiler = Command::new("rustc");
    compiler.args(compiler_args);

    // Test command 2: run `tempdir/x`.
    if test_target.is_some() {
        let mut env_path = std::env::var("PATH").unwrap_or_default();
        // TODO(antoyo): find a better way to add the PATH necessary locally.
        env_path = format!("/opt/m68k-unknown-linux-gnu/bin:{}", env_path);
        compiler.env("PATH", env_path);

        let vm_parent_dir = std::env::var("CG_GCC_VM_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|_| std::env::current_dir().unwrap());
        let vm_dir = "vm";
        let exe_filename = exe.file_name().unwrap();
        let vm_home_dir = vm_parent_dir.join(vm_dir).join("home");
        let vm_exe_path = vm_home_dir.join(exe_filename);
        // FIXME(antoyo): panicking here makes the test pass.
        let inside_vm_exe_path = PathBuf::from("/home").join(exe_filename);
        let mut copy = Command::new("sudo");
        copy.arg("cp");
        copy.args([exe, &vm_exe_path]);

        let mut runtime = Command::new("sudo");
        runtime.args(["chroot", vm_dir, "qemu-m68k-static"]);
        runtime.arg(inside_vm_exe_path);
        runtime.current_dir(vm_parent_dir);
        vec![("Compiler", compiler), ("Copy", copy), ("Run-time", runtime)]
    } else {
        let runtime = Command::new(exe);
        vec![("Compiler", compiler), ("Run-time", runtime)]
    }
}

fn main() {
    let tempdir = TempDir::new().expect("temp dir");
    let current_dir = current_dir().expect("current dir");
    let current_dir = current_dir.to_str().expect("current dir").to_string();

    fn rust_filter(path: &Path) -> bool {
        path.is_file() && path.extension().expect("extension").to_str().expect("to_str") == "rs"
    }

    #[cfg(feature = "master")]
    fn filter(filename: &Path) -> bool {
        rust_filter(filename)
    }

    #[cfg(not(feature = "master"))]
    fn filter(filename: &Path) -> bool {
        if let Some(filename) = filename.to_str()
            && filename.ends_with("gep.rs")
        {
            return false;
        }
        rust_filter(filename)
    }
    // TODO(antoyo): find a way to send this via a cli argument.
    let test_target = std::env::var("CG_GCC_TEST_TARGET").ok();

    LangTester::new()
        .test_dir("tests/run")
        .test_path_filter(filter)
        .test_extract(|path| {
            std::fs::read_to_string(path)
                .expect("read file")
                .lines()
                .skip_while(|l| !l.starts_with("//"))
                .take_while(|l| l.starts_with("//"))
                .map(|l| &l[2..])
                .collect::<Vec<_>>()
                .join("\n")
        })
        .test_cmds(move |path| {
            // Test command 1: Compile `x.rs` into `tempdir/x`.
            let mut exe = PathBuf::new();
            exe.push(&tempdir);
            exe.push(path.file_stem().expect("file_stem"));
            let mut compiler_args = vec![
                format!("-Zcodegen-backend={}/target/debug/librustc_codegen_gcc.so", current_dir),
                "--sysroot".into(),
                format!("{}/build/build_sysroot/sysroot/", current_dir),
                "-C".into(),
                "link-arg=-lc".into(),
                "--extern".into(),
                "mini_core=target/out/libmini_core.rlib".into(),
                "-o".into(),
                exe.to_str().expect("to_str").into(),
                path.to_str().expect("to_str").into(),
            ];

            if let Some(ref target) = test_target {
                compiler_args.extend_from_slice(&["--target".into(), target.into()]);

                let linker = format!("{}-gcc", target);
                compiler_args.push(format!("-Clinker={}", linker));
            }

            if let Some(flags) = option_env!("TEST_FLAGS") {
                for flag in flags.split_whitespace() {
                    compiler_args.push(flag.into());
                }
            }
            let mut debug_args = compiler_args.clone();
            let mut release_args = compiler_args;

            if test_target.is_some() {
                // m68k doesn't have lubsan for now
                debug_args
                    .extend_from_slice(&["-C".to_string(), "llvm-args=sanitize-undefined".into()]);
            } else {
                debug_args.extend_from_slice(&[
                    "-C".to_string(),
                    "llvm-args=sanitize-undefined".into(),
                    "-C".into(),
                    "link-args=-lubsan".into(),
                ]);
            }

            release_args.extend_from_slice(&[
                "-C".into(),
                "opt-level=3".into(),
                "-C".into(),
                "lto=no".into(),
            ]);

            let mut parts = compile_and_run_cmds(debug_args, &test_target, &exe);
            parts.extend(compile_and_run_cmds(release_args, &test_target, &exe));
            parts
        })
        .run();
}
