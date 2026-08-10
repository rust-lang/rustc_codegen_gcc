// Compiler:
//   status: 0

// Reproducer for: `simd_arith_offset` is unimplemented and ICEs (codegen-audit-2026-08.md).
// No handler exists in src/intrinsic/simd.rs, so it falls through to the terminal
// `unimplemented!("simd {}", name)`. The intrinsic is reached by ordinary `std::simd`
// pointer-vector arithmetic (`Simd<*const T, N>::wrapping_add/wrapping_offset` calls it),
// so any portable-simd code doing pointer math ICEs. cg_llvm implements it as a vector GEP
// and runs this program fine.

#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::simd::simd_arith_offset;

#[repr(simd)]
#[derive(Copy, Clone)]
struct PtrX4([*const u32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
struct UsizeX4([usize; 4]);

fn main() {
    unsafe {
        let data = [10u32, 11, 12, 13, 14, 15, 16, 17];
        let base = data.as_ptr();
        let pointers = PtrX4([base; 4]);
        let offsets = UsizeX4([0, 2, 4, 6]);
        let shifted: PtrX4 = simd_arith_offset(pointers, offsets);
        let shifted_array: [*const u32; 4] = std::mem::transmute(shifted);
        let values: Vec<u32> = shifted_array.iter().map(|&pointer| *pointer).collect();
        println!("{:?}", values);
    }
}
