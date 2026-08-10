// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 3555

// Reproducer for: `f16::mul_add` is double-rounded (codegen-audit-2026-08.md).
// src/intrinsic/mod.rs lowers `fmaf16` by casting the operands to f32, calling the f32
// `fmaf` builtin, and casting back. The f32 result rounds the exact product-sum to 24 bits
// and the cast rounds again to 11 bits; when the first rounding lands exactly on an f16
// tie point, ties-to-even resolves the wrong way. For the inputs below the exact result is
// 2*2^-34 BELOW the f16 tie point, so correct rounding gives 0x3555, but the f32 fma lands
// on the tie and rounds up to 0x3556. cg_gcc currently prints `3556`; this test asserts
// the correctly rounded result, so it fails until the bug is fixed.

#![feature(f16)]

use std::hint::black_box;

fn main() {
    let a = f16::from_bits(0x4001); // 2.001953125
    let b = f16::from_bits(0x03ff); // subnormal, 1023 * 2^-24
    let c = f16::from_bits(0x3555); // 0.333251953125
    let r = black_box(a).mul_add(black_box(b), black_box(c));
    println!("{:04x}", r.to_bits());
}
