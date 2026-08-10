// Compiler:
//
// Run-time:
//   status: 0
//   stdout: [127, 127, 28, 127]
//     [127, 127, 28, 127]
//     [127, -128, 127, -128]

// Reproducer for: signed `simd_saturating_sub` is wrong when rhs contains T::MIN
// (codegen-audit-2026-08.md). The signed path in src/intrinsic/simd.rs implements
// `sat_sub(a, b)` as `sat_add(a, -b)`, and `-(T::MIN)` wraps back to T::MIN, so
// `x.saturating_sub(-128)` computes `x.saturating_add(-128)` instead. cg_gcc currently
// prints `[-128, -28, -128, -128]` for the first line; this test asserts the correct
// result, so it fails until the bug is fixed. The second line is the same computation done
// with scalar `saturating_sub` (correct, for reference), and the third checks that
// `simd_saturating_add` is unaffected.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::simd::{simd_saturating_add, simd_saturating_sub};

#[repr(simd)]
#[derive(Copy, Clone)]
struct I8x4([i8; 4]);

fn main() {
    let a = black_box(I8x4([0, 100, -100, -1]));
    let b = black_box(I8x4([-128, -128, -128, -128]));
    let r: I8x4 = unsafe { simd_saturating_sub(a, b) };
    let v: [i8; 4] = unsafe { std::mem::transmute(r) };
    println!("{:?}", v);

    let expected: Vec<i8> =
        [0i8, 100, -100, -1].iter().map(|x| x.saturating_sub(-128)).collect();
    println!("{:?}", expected);

    let c = black_box(I8x4([100, -100, 127, -128]));
    let d = black_box(I8x4([100, -100, 1, -1]));
    let r2: I8x4 = unsafe { simd_saturating_add(c, d) };
    let v2: [i8; 4] = unsafe { std::mem::transmute(r2) };
    println!("{:?}", v2);
}
