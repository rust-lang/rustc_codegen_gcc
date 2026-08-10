// Compiler:
//
// Run-time:
//   status: 0
//   stdout: wide = 112233445566778899aabbccddeeff00

// Reproducer for: `unaligned_volatile_load` ignores its alignment (codegen-audit-2026-08.md).
// The intrinsic arm passes `Align::ONE`, but `volatile_load` (src/builder.rs, "FIXME(antoyo):
// set alignment") drops it and dereferences through a naturally-aligned `volatile T*`. For a
// `#[repr(C, packed)]` u128 field GCC then assumes 16-byte alignment and, at -O3 on x86_64,
// emits an ALIGNED 16-byte vector load at base+1 -> SIGSEGV in the release pass of this
// test suite (the debug pass happens to survive because no aligned vector access is chosen).
// This test asserts the correct value and a clean exit, so it fails until the bug is fixed.

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::hint::black_box;
use std::intrinsics;

#[repr(C, packed)]
struct Packed {
    byte: u8,
    wide: u128,
}

fn main() {
    let packed = Packed { byte: 0xA5, wide: 0x1122_3344_5566_7788_99AA_BBCC_DDEE_FF00 };
    let packed = black_box(&packed);
    let wide = unsafe { intrinsics::unaligned_volatile_load(std::ptr::addr_of!(packed.wide)) };
    println!("wide = {:032x}", wide);
}
