// Compiler:
//
// Run-time:
//   status: 0
//   stdout: AlignedU64 { x: 1234605616436508484 } take=3703816849309525457

// Reproducer for: `ArgAbi::store` with `PassMode::Cast` copies `layout.size` bytes out of a
// scratch slot that is only `cast.size` bytes big (codegen-audit-2026-08.md). On x86-64 SysV
// a `#[repr(C, align(16))] struct { x: u64 }` (size 16) is classified as a single `i64`
// (8 bytes), and src/intrinsic/mod.rs memcpys 16 bytes from the 8-byte scratch — an
// out-of-bounds read. cg_llvm copies `min(cast size, layout size)` instead. At -O0 GCC's
// own `memcpy reading 16 bytes from a region of size 8` diagnostic is escalated into a
// rustc panic, so the DEBUG pass of this test currently fails to even compile; at -O3 it
// compiles and runs (the over-read lands in padding). The test asserts a successful build
// and the correct values, so it fails until the bug is fixed.

use std::hint::black_box;

#[repr(C, align(16))]
#[derive(Copy, Clone, PartialEq, Debug)]
struct AlignedU64 {
    x: u64,
}

extern "C" fn make_aligned(x: u64) -> AlignedU64 {
    AlignedU64 { x: black_box(x) }
}

extern "C" fn take_aligned(value: AlignedU64, extra: u64) -> u64 {
    black_box(value).x.wrapping_mul(3).wrapping_add(extra)
}

fn main() {
    let made = make_aligned(black_box(0x1122_3344_5566_7744));
    println!("{:?} take={}", made, take_aligned(made, black_box(5)));
}
