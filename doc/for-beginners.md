# Enable full `rust-analyzer` support of `cg_gcc` for your editor

## Steps to Follow
1. (Already done in by project.) Add the following lines to `Cargo.toml`
```toml
[package.metadata.rust-analyzer]
rustc_private = true
```
2. Install rust-src with rustup: `rustup component add rust-src`.
   NOTE: Make sure you've switched to the corresponding toolchain as is used by cg_gcc
3. Set the lsp option `rust-analyzer.rustc.source = "discover"` (you can also set it to an explicit path), depending on your editor.
    1. Neovim(nvim-lspconfig):
    ```
    require('lspconfig').rust_analyzer.setup{
      settings = {
        ['rust-analyzer'] = {
          -- add this section
          rustc = {
            source = "discover",
          },
        },
      },
    }
    ```
   2. Emacs: customize `Lsp Rust Analyzer Rustc Source` to the Path `discover`

## FAQ

### Why is this needed?

Without these steps, `rust-analyzer` will NOT import `rustc` related packages to its scope and all rustc related clauses will fail to be analyzed in lsp, and the analyzer will notify you of the missing `rustc_*` packages.

### Why is this NOT needed for `rustc_codegen_llvm` in your `rust-src`?
In the `Cargo.toml` of the `rustc_codegen_llvm`, you may notice the following lines:
```toml
rustc_ast = { path = "../rustc_ast" }
rustc_attr = { path = "../rustc_attr" }
rustc_codegen_ssa = { path = "../rustc_codegen_ssa" }
rustc_data_structures = { path = "../rustc_data_structures" }
rustc_errors = { path = "../rustc_errors" }
rustc_fluent_macro = { path = "../rustc_fluent_macro" }
rustc_fs_util = { path = "../rustc_fs_util" }
rustc_hir = { path = "../rustc_hir" }
rustc_index = { path = "../rustc_index" }
rustc_llvm = { path = "../rustc_llvm" }
rustc_macros = { path = "../rustc_macros" }
rustc_metadata = { path = "../rustc_metadata" }
rustc_middle = { path = "../rustc_middle" }
rustc_query_system = { path = "../rustc_query_system" }
rustc_session = { path = "../rustc_session" }
rustc_span = { path = "../rustc_span" }
rustc_symbol_mangling = { path = "../rustc_symbol_mangling" }
```
They set the paths to the rustc-related packages, solving the problem of `rustc_private` packages.

In theory, it is possible that you use the same workaround as in `rustc_codegen_llvm`.

While the `rustc_codegen_cranelift` uses the same approach as `rustc_codegen_gcc`.

```
[package.metadata.rust-analyzer]
rustc_private = true
```

# Compiling External Project with `rustc_codegen_gcc`

1.  Run the program with (in the root dir of `rustc_codegen_gcc` )(where `--manifest-path` is the path to the `Cargo.toml` of the project to run `cargo` against):

```shell
    ./y.sh cargo --manifest-path="..."
```

or you may as well add this alias in your `.bash_aliases`:


```shell
    alias cargcc="/path/to/rustc_codegen_gcc/y.sh cargo"
```

2.  If std or libcore is needed, then the sysroot should be built first(see `build_system/src/test.rs` for hint.)
