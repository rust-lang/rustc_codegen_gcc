// Compiler:
//   status: 0

// Reproducer for: the `prefetch_*` intrinsics ICE (codegen-audit-2026-08.md).
// src/intrinsic/mod.rs reaches `unimplemented!()` for `prefetch_read_data` (and the other
// three prefetch variants), so compiling a call panics with "not implemented". cg_llvm
// lowers them to `llvm.prefetch`. A prefetch is a pure hint — GCC has
// `__builtin_prefetch` — and executing it is harmless.

#![feature(core_intrinsics)]
#![allow(internal_features)]

fn main() {
    let data = [1u8; 64];
    unsafe { core::intrinsics::prefetch_read_data::<_, 1>(data.as_ptr()) };
    println!("ok {}", data[0]);
}
