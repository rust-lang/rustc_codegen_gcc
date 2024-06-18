# GCC codegen backend for Rust (WIP)

[![Chat on IRC](https://img.shields.io/badge/irc.libera.chat-%23rustc__codegen__gcc-blue.svg)](https://web.libera.chat/#rustc_codegen_gcc)
[![Chat on Matrix](https://img.shields.io/badge/matrix.org-%23rustc__codegen__gcc-blue.svg)](https://matrix.to/#/#rustc_codegen_gcc:matrix.org)

This GCC codegen enables the official rustc compiler frontend to leverage GCC as a compiler backend. This is accomplished through interfacing with GCC's [libgccjit](https://gcc.gnu.org/wiki/JIT) library. While libgccjit is primarily intended to be used as an interface to GCC for just-in-time code generation, it can also be used for ahead-of-time compilation, as we do here.

### Goals
* Enable the compilation of Rust code for target platforms supported by GCC, but not LLVM
* Leverage potential GCC optimizations for run-time speed improvement for Rust applications
* Reduce dependence of the Rust ecosystem on LLVM

## Building
### Dependencies
* **[rustup](https://www.rust-lang.org/tools/install)**: The rustup tool is required to build this project using the following instructions; do not rely on a Rust toolchain that may have been provided by your operating system's package manager.
* **[DejaGnu](https://www.gnu.org/software/dejagnu/#downloading)** (optional): Install the DejaGnu testing framework in order to run the libgccjit test suite.

### Building GCC with libgccjit.so
#### On Linux x86-64
When using an x86-64 Linux host to target x86-64 Linux, building `libgccjit.so` is unnecessary -- in that case, a precompiled version may be downloaded automatically. Simply copy the provided `config.example.toml` file to `config.toml` to enable the automatic downloading of `libgccjit.so`.
```bash
$ cp config.example.toml config.toml
```
Now you may skip ahead to [Building rustc_codegen_gcc](#building-rustc_codegen_gcc).

#### Other architectures
If you are on a host arch other than x86-64 Linux or are targetting an arch other than x86-64 Linux, you will need to build a custom GCC with `libgccjit.so`. **At this time, this requires the use of the [rust-lang/gcc](https://github.com/rust-lang/gcc) fork of GCC, which includes patches to libgccjit to enable the use of this codegen.**

Full instructions to build libgccjit are provided in the [libgccjit documentation](https://gcc.gnu.org/onlinedocs/jit/internals/index.html), so check there if you encounter issues, however brief directions for Debian-based Linux follow below. You may need to adapt them to your operating system and package manager. If you need to build a cross-compiler, see [Building a cross-compiler with rustc_codegen_gcc](./doc/cross.md).

```bash
$ git clone https://github.com/rust-lang/gcc gcc-source
$ sudo apt install flex libmpfr-dev libgmp-dev libmpc3 libmpc-dev
$ mkdir gcc-build gcc-install
$ cd gcc-build
$ ../gcc-source/configure \
    --enable-host-shared \
    --enable-languages=jit \
    --enable-checking=release \
    --disable-bootstrap \
    --disable-multilib \
    --prefix=$(pwd)/../gcc-install
$ make -j4
$ make install
```

Notes:
* If you want to run libgccjit tests, you must also add C++ to the enabled languages: `--enable-languages=jit,c++`
* `--enable-host-shared` builds the compiler as position independent code and is required to build libgccjit. This results in a slower compiler; however, if building GCC in multiple passes, `jit` may be built in the first pass with `--enable-host-shared`, with both disabled in subsequent passes.
* `--enable-checking=release` and `--disable-bootstrap` speed up compilation by disabling self-checks and may be omitted.
* `--disable-multilib` is used as libgccjit only supports targeting one arch ABI variant.
* Adjust the `4` in `make -j4` to the number of threads available on your system to speed up compilation.
* Change `make install` to `make install-strip` to remove debug symbols from GCC, including `libgccjit.so`, to save on disk space.

Once the build is complete, one may run libgccjit tests like so (requires DejaGnu to be installed):
```bash
$ make -C gcc check-jit
```
To run one specific test:
```bash
$ make -C gcc check-jit RUNTESTFLAGS="-v -v -v jit.exp=jit.dg/test-asm.cc"
```

Now that you've compiled GCC with libgccjit support, the installed GCC toolchain with `libgccjit.so` can be found in the `gcc-install` directory created above. You will need to provide the path to the specific subdirectory containing `libgccjit.so` to rustc_codegen_gcc. Use the following commands to leave the `gcc-build` directory and find the absolute path within the `gcc-install` directory:
```bash
$ cd ..
$ dirname $(readlink -f `find ./gcc-install -name libgccjit.so`)
```

If desired, you may now delete the `gcc-source` and `gcc-build` directories to reclaim disk space, but keep the `gcc-install` directory.

Then, within the rustc_codegen_gcc repository directory, create a `config.toml` file with the following contents. Replace `[MY PATH]` with the path you found above.
```toml
gcc-path = "[MY PATH]"
```

### Building rustc_codegen_gcc
Now that you have a `config.toml` file set up to use `libgccjit.so`, you can proceed to building the build system and sysroot. `prepare` will retrieve and patch the sysroot source, while `build` will build the sysroot.

```bash
$ ./y.sh prepare
$ ./y.sh build --sysroot --release
```

You may also run the tests:
```bash
$ ./y.sh test --release
```

## Usage
The following example commands are run with `$CG_GCCJIT_DIR` representing the path to your rustc_codegen_gcc directory. 
### Cargo
To invoke `cargo`, run the following example command:
```bash
$ CHANNEL="release" $CG_GCCJIT_DIR/y.sh cargo run
```

You may verify your build is working properly by building a test project:
 ```bash
$ CHANNEL="release" $CG_GCCJIT_DIR/y.sh cargo build --manifest-path $CG_GCCJIT_DIR/tests/hello-world/Cargo.toml
```

Note: If you compiled rustc_codegen_gcc in debug mode (i.e., you didn't pass `--release` to `./y.sh` above), you should use `CHANNEL="debug"` or omit `CHANNEL="release"` completely.

### LTO

To use LTO, you need to set the environment variables `FAT_LTO=1` and `EMBED_LTO_BITCODE=1`, in addition to setting `lto = "fat"` in your project's `Cargo.toml`.
Don't set `FAT_LTO` when compiling the sysroot, though: only set `EMBED_LTO_BITCODE=1`.

Failing to set `EMBED_LTO_BITCODE` will give you the following error: `error: failed to copy bitcode to object file: No such file or directory (os error 2)`.

### rustc

To invoke `rustc` instead of using `cargo`, you can do so with the following example command:

```bash
$ $CG_GCCJIT_DIR/y.sh rustc my_crate.rs
```

Although not recommended, you may manually invoke `rustc` directly. In this example, `$LIBGCCJIT_PATH` represents the path to the directory containing `libgccjit.so`.

```bash
$ LIBRARY_PATH="$LIBGCCJIT_PATH" LD_LIBRARY_PATH="$LIBGCCJIT_PATH" rustc +$(cat $CG_GCCJIT_DIR/rust-toolchain | grep 'channel' | cut -d '=' -f 2 | sed 's/"//g' | sed 's/ //g') -Zcodegen-backend=$CG_GCCJIT_DIR/target/release/librustc_codegen_gcc.so --sysroot $CG_GCCJIT_DIR/build_sysroot/sysroot my_crate.rs
```

## Environment variables

 * _**CG_RUSTFLAGS**_: Send additional flags to rustc. Can be used to build the sysroot without unwinding by setting `CG_RUSTFLAGS=-Cpanic=abort`.
 * _**CG_GCCJIT_VERBOSE**_: Enables verbose output from the GCC driver.
 * _**CG_GCCJIT_DUMP_ALL_MODULES**_: Enables dumping of all compilation modules. When set to "1", a dump is created for each module during compilation and stored in `/tmp/reproducers/`.
 * _**CG_GCCJIT_DUMP_MODULE**_: Enables dumping of a specific module. When set with the module name, e.g., `CG_GCCJIT_DUMP_MODULE=module_name`, a dump of that specific module is created in `/tmp/reproducers/`.
 * _**CG_GCCJIT_DUMP_TO_FILE**_: Dump a C-like representation to `/tmp/gccjit_dumps` and enable debug info in order to debug this C-like representation.
 * _**CG_GCCJIT_DUMP_RTL**_: Dumps RTL (Register Transfer Language) for virtual registers.
 * _**CG_GCCJIT_DUMP_RTL_ALL**_: Dumps all RTL passes.
 * _**CG_GCCJIT_DUMP_TREE_ALL**_: Dumps all tree (GIMPLE) passes.
 * _**CG_GCCJIT_DUMP_IPA_ALL**_: Dumps all Interprocedural Analysis (IPA) passes.
 * _**CG_GCCJIT_DUMP_CODE**_: Dumps the final generated code.
 * _**CG_GCCJIT_DUMP_GIMPLE**_: Dumps the initial GIMPLE representation.
 * _**CG_GCCJIT_DUMP_EVERYTHING**_: Enables dumping of all intermediate representations and passes.
 * _**CG_GCCJIT_KEEP_INTERMEDIATES**_: Keeps intermediate files generated during the compilation process.

## Additional documentation

Additional documentation is available in the [`doc`](./doc) folder:

 * [Building a cross-compiler](./doc/cross.md)
 * [Common errors](./doc/errors.md)
 * [Debugging GCC LTO](./doc/debugging-gcc-lto.md)
 * [Debugging libgccjit](./doc/debugging-libgccjit.md)
 * [Git subtree sync](./doc/subtree.md)
 * [List of useful commands](./doc/tips.md)
 * [Send a patch to GCC](./doc/sending-gcc-patch.md)

## Licensing

While this crate is licensed under a dual Apache/MIT license, it links to `libgccjit` which is under the GPLv3+ and thus, the resulting toolchain (rustc + GCC codegen) will need to be released under the GPL license.

However, programs compiled with `rustc_codegen_gcc` do not need to be released under a GPL license.
