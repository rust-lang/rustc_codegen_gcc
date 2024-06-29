# Tips

The following shows how to do different random small things we encountered and thought could
be useful.

### How to send arguments to the GCC linker

```
CG_RUSTFLAGS="-Clink-args=-save-temps -v" ../y.sh cargo build
```

### How to see the personality functions in the asm dump

```
CG_RUSTFLAGS="-Clink-arg=-save-temps -v -Clink-arg=-dA" ../y.sh cargo build
```

### How to see the LLVM IR for a sysroot crate

```
cargo build -v --target x86_64-unknown-linux-gnu -Zbuild-std
# Take the command from the output and add --emit=llvm-ir
```

### To prevent the linker from unmangling symbols

Run with:

```
COLLECT_NO_DEMANGLE=1
```

### How to use a custom-build rustc

 * Build the stage2 compiler (`rustup toolchain link debug-current build/x86_64-unknown-linux-gnu/stage2`).
 * Clean and rebuild the codegen with `debug-current` in the file `rust-toolchain`.

### How to use a custom sysroot source path

If you wish to build a custom sysroot, pass the path of your sysroot source to `--sysroot-source` during the `prepare` step, like so:

```
./y.sh prepare --sysroot-source /path/to/custom/source
```

### How to use [mem-trace](https://github.com/antoyo/mem-trace)

`rustc` needs to be built without `jemalloc` so that `mem-trace` can overload `malloc` since `jemalloc` is linked statically, so a `LD_PRELOAD`-ed library won't a chance to intercept the calls to `malloc`.

### How to generate GIMPLE

If you need to check what gccjit is generating (GIMPLE), then take a look at how to
generate it in [gimple.md](./doc/gimple.md).
