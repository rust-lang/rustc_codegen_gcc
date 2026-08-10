// Compiler:
//   status: 0

// Reproducer for: the `breakpoint` intrinsic ICEs (codegen-audit-2026-08.md).
// src/intrinsic/mod.rs has `sym::breakpoint => unimplemented!()`, so compiling a call to
// `core::arch::breakpoint()` (a stable-track API, feature `breakpoint`) panics with
// "not implemented". cg_llvm compiles it fine. The call is guarded so it never executes;
// only compiling it is the point.

#![feature(breakpoint)]

fn main() {
    if std::env::args().count() > 100 {
        core::arch::breakpoint();
    }
    println!("ok");
}
