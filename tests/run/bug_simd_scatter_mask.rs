// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 7

// Reproducer for: `simd_scatter` accesses masked-off lanes (codegen-audit-2026-08.md,
// existing issue rust-lang/rustc_codegen_gcc#640). The lowering in src/intrinsic/simd.rs
// reads the current values of ALL lanes (a gather with the inverted mask) and then writes
// every lane, so a disabled lane holding a null pointer is both read and written. Lane 1
// is masked off and null here: a correct backend must not touch it, writes 7 through
// lane 0 and prints `7`; cg_gcc currently dies with SIGSEGV.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::simd::simd_scatter;

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x2([i32; 2]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct P2([*mut i32; 2]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct M2([i32; 2]);

fn main() {
    let mut y = 0i32;
    let values = I32x2([7, 8]);
    let pointers = black_box(P2([&mut y as *mut i32, std::ptr::null_mut()]));
    let mask = black_box(M2([-1, 0]));
    unsafe { simd_scatter(values, pointers, mask) };
    println!("{}", y);
}
