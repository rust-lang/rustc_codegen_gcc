// Compiler:
//
// Run-time:
//   status: 0
//   stdout: [42, -2]

// Reproducer for: `simd_gather` dereferences masked-off lanes (codegen-audit-2026-08.md,
// existing issue rust-lang/rustc_codegen_gcc#640). The lowering in src/intrinsic/simd.rs
// loads every lane and only THEN selects by the mask, so a disabled lane holding a null
// (or otherwise invalid) pointer crashes. Lane 1 is masked off and null here: a correct
// backend must not touch it and prints `[42, -2]`; cg_gcc currently dies with SIGSEGV.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::simd::simd_gather;

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x2([i32; 2]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct P2([*const i32; 2]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct M2([i32; 2]);

fn main() {
    let x = 42i32;
    let pointers = black_box(P2([&x as *const i32, std::ptr::null()]));
    let default = I32x2([-1, -2]);
    let mask = black_box(M2([-1, 0]));
    let r: I32x2 = unsafe { simd_gather(default, pointers, mask) };
    let a: [i32; 2] = unsafe { std::mem::transmute(r) };
    println!("{:?}", a);
}
