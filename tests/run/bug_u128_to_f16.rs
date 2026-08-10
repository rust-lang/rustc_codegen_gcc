// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 42 -3 1

// Reproducer for: `u128 as f16` / `i128 as f16` ICE on targets without native 128-bit
// integers (codegen-audit-2026-08.md). `int_to_float_cast` (src/int.rs:937-944) matches
// only Float/Double/FP128 destination kinds; `TypeKind::Half` falls into
// `panic!("cannot cast a non-native integer to type Half")`. The reverse direction
// (`float_to_int_cast`) handles Half by promoting through f32, so only int->f16 is broken.
//
// On x86_64 with native `__int128` this test passes; it reproduces on the CI that builds
// libgccjit without 128-bit integer support (and on any 32-bit target, e.g. m68k), where
// the compile step ICEs. Verified locally by forcing `u128_type_supported = false` in
// src/base.rs: panic at src/int.rs:943.

#![feature(f16)]

use std::hint::black_box;

fn main() {
    let x: u128 = black_box(42);
    let h = x as f16;
    let y: i128 = black_box(-3);
    let h2 = y as f16;
    let back = black_box(1.5f16) as u128;
    println!("{} {} {}", h, h2, back);
}
