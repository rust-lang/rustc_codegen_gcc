// Compiler:
//
// Run-time:
//   status: 0
//   stdout: [2147483647, -2147483648, 0, 1]

// Reproducer for: `simd_as` float->int does not saturate (codegen-audit-2026-08.md).
// `simd_as` must have scalar `as` semantics (saturate, NaN -> 0), but src/intrinsic/simd.rs
// routes both `simd_cast` and `simd_as` through `convert_vector`, which has C cast semantics
// (out-of-range is left to GCC; NaN and overflow produce wrong lanes). cg_gcc currently
// prints `[-2147483648, -2147483648, -2147483648, 1]`; this test asserts the correct
// saturating result, so it fails until the bug is fixed.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::simd::simd_as;

#[repr(simd)]
#[derive(Copy, Clone)]
struct F32x4([f32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x4([i32; 4]);

fn main() {
    let v = black_box(F32x4([1e10, -1e10, f32::NAN, 1.0]));
    let r: I32x4 = unsafe { simd_as(v) };
    let a: [i32; 4] = unsafe { std::mem::transmute(r) };
    println!("{:?}", a);
}
