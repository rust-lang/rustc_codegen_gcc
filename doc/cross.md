# How to build a cross-compiler with rustc_codegen_gcc

## Building libgccjit

* With **crosstool-ng**: follow the instructions on [this repo](https://github.com/cross-cg-gcc-tools/cross-gcc).
* **Other**: Build a GCC cross-compiler like usual, but add `--enable-languages=jit`, `--enable-host-shared`, and `--disable-multilib` to the `./configure` arguments for pass 1.

## Configuring rustc_codegen_gcc

* Make sure you set the path to the cross-compiling libgccjit in rustc_codegen_gcc's `config.toml`.
* Make sure you have the linker for your target (for instance `m68k-unknown-linux-gnu-gcc`) in your `$PATH`. Currently, the linker name is hardcoded as being `$TARGET-gcc`.
* Use `--cross` during the prepare step so that the sysroot is patched for the cross-compiling case:
  * `./y.sh prepare --cross`

### rustc-supported targets
* If the target is already supported by rustc, use `--target-triple` to specify the target when building the sysroot:
  * `./y.sh build --sysroot --target-triple m68k-unknown-linux-gnu`
* Specify the target when building your project:
  * `./y.sh cargo build --target m68k-unknown-linux-gnu`

### rustc-unsupported targets
* If the target is not yet supported by the Rust compiler, create a [target specification file](https://docs.rust-embedded.org/embedonomicon/custom-target.html). Fake the `arch` specified in your target specification file by replacing it with one that is supported by the Rust compiler. 
* To build the sysroot, use `--target-triple` to specify the real target, and use `--target` to add the **absolute path** to your target specification file:
  * `./y.sh build --sysroot --target-triple m68k-unknown-linux-gnu --target $(pwd)/m68k-unknown-linux-gnu.json`
* Specify the target specification file when building your project:
  * `./y.sh cargo build --target path/to/m68k-unknown-linux-gnu.json`

If you get the error `/usr/bin/ld: unrecognised emulation mode: m68kelf`, make sure you set `gcc-path` (in `config.toml`) to the install directory.
