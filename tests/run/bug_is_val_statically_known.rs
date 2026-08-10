// Compiler:
//
// Run-time:
//   status: 0
//   stdout: false

// Reproducer for: `is_val_statically_known` is inverted (codegen-audit-2026-08.md).
// src/intrinsic/mod.rs lowers it as `__builtin_constant_p(x) == 0`, i.e. the OPPOSITE
// of what the intrinsic means, so it returns `true` exactly when the value is NOT known.
// The intrinsic's contract allows a false negative for a constant, but never `true` for a
// runtime value — and the argument count of the program is a runtime value. cg_gcc
// currently prints `true`; this test asserts `false`, so it fails until the bug is fixed.

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::is_val_statically_known;

fn main() {
    let x = std::env::args().count();
    let known = is_val_statically_known(x);
    println!("{}", known);
}
