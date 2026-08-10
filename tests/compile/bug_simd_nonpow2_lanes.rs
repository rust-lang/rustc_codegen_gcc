// Compiler:
//   status: 0

// Reproducer for: any non-power-of-two SIMD lane count ICEs (codegen-audit-2026-08.md).
// rustc accepts `#[repr(simd)]` (and `std::simd::Simd`) for any lane count in 1..=64, but
// src/type_of.rs:76 forwards the exact count to `gcc_jit_type_get_vector`, which requires
// a power of two: `libgccjit.so: error: gcc_jit_type_get_vector: num_units not a power of
// two: 3`, followed by a rustc panic. cg_llvm compiles and runs this program fine (prints
// `11 22 33`). This ICE also masks several latent non-power-of-two bugs (vector_reduce
// lane duplication, shuffle length-extension, 9..24-lane bitmask truncation/OOB — see the
// report), so fixing it should come with fixes for those.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics::simd::simd_add;

#[repr(simd)]
#[derive(Copy, Clone)]
struct I32x3([i32; 3]);

fn main() {
    let a = black_box(I32x3([1, 2, 3]));
    let b = black_box(I32x3([10, 20, 30]));
    let r: I32x3 = unsafe { simd_add(a, b) };
    let p = &r as *const I32x3 as *const i32;
    unsafe { println!("{} {} {}", *p, *p.add(1), *p.add(2)) };
}
