// Compiler:
//   env-var: CG_GCCJIT_DUMP_GIMPLE=1
//   status: 0
//   stderr:
//     ...
//     ..., 0, 4, 2);
//     ...

// GIMPLE test (in the spirit of rustc's LLVM IR codegen tests) for:
// `compare_exchange(success: Release, failure: Acquire)` drops the Release ordering
// (codegen-audit-2026-08.md). src/builder.rs picks the memmodel pair by taking the MAX of
// the two ordering DISCRIMINANTS, but Release and Acquire are incomparable in the ordering
// lattice, so the success order collapses to Acquire: the emitted call is
// `__atomic_compare_exchange_4 (..., 0, 2, 2)` (success=ACQUIRE, failure=ACQUIRE), losing
// the release barrier on the successful store. GCC requires failure <= success, so the
// correct strengthening is success=ACQ_REL: `(..., 0, 4, 2)` — which is what this test's
// stderr pattern asserts on the initial-GIMPLE dump (GCC memmodels: RELAXED=0 CONSUME=1
// ACQUIRE=2 RELEASE=3 ACQ_REL=4 SEQ_CST=5; the `0` before them is the weak-CAS flag).
// x86-TSO makes release stores free, so this is not runtime-observable on x86_64 — hence
// a GIMPLE test. The intrinsic is called directly so the code is monomorphized in this
// crate (`AtomicU32::compare_exchange` itself would be codegenned into libstd instead).

#![feature(core_intrinsics)]
#![allow(internal_features)]

use std::intrinsics::AtomicOrdering;

fn main() {
    let mut value = 1u32;
    let (previous, swapped) = unsafe {
        std::intrinsics::atomic_cxchg::<
            u32,
            { AtomicOrdering::Release },
            { AtomicOrdering::Acquire },
        >(&mut value, 1, 2)
    };
    println!("{} {} {}", previous, swapped, value);
}
