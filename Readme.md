# WIP libgccjit codegen backend for rust

**Despite its name, libgccjit can be used for ahead-of-time compilation, as is used here.**

## Building

**This requires a patched libgccjit in order to work.
The following two patches need to be applied:**

 * https://gcc.gnu.org/pipermail/jit/2020q3/001228.html
 * https://gcc.gnu.org/pipermail/jit/2020q3/001247.html

```bash
$ git clone https://github.com/antoyo/rustc_codegen_gcc.git
$ cd rustc_codegen_gcc
$ ./prepare.sh # download and patch sysroot src and install hyperfine for benchmarking
$ ./test.sh --release
```

## Usage

`$cg_gccjit_dir` is the directory you cloned this repo into in the following instructions.

### Cargo

```bash
$ CHANNEL="release" $cg_gccjit_dir/cargo.sh run
```

If you compiled cg_gccjit in debug mode (aka you didn't pass `--release` to `./test.sh`) you should use `CHANNEL="debug"` instead or omit `CHANNEL="release"` completely.

### Rustc

> You should prefer using the Cargo method.

```bash
$ rustc +$(cat $cg_gccjit_dir/rust-toolchain) -Cpanic=abort -Zcodegen-backend=$cg_gccjit_dir/target/release/librustc_codegen_gcc.so --sysroot $cg_gccjit_dir/build_sysroot/sysroot my_crate.rs
```

## Env vars

<dl>
    <dt>CG_GCCJIT_INCR_CACHE_DISABLED</dt>
    <dd>Don't cache object files in the incremental cache. Useful during development of cg_gccjit
    to make it possible to use incremental mode for all analyses performed by rustc without caching
    object files when their content should have been changed by a change to cg_gccjit.</dd>
    <dt>CG_GCCJIT_DISPLAY_CG_TIME</dt>
    <dd>Display the time it took to perform codegen for a crate</dd>
</dl>
