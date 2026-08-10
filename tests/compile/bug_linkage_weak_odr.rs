// Compiler:
//   status: 0

// Reproducer for: `#[linkage = "weak_odr"]` on a function ICEs (codegen-audit-2026-08.md).
// `linkage_to_gcc` (src/base.rs:61-67) has `unimplemented!()` arms for WeakODR — and also
// for Linkonce, LinkonceODR and Common, which fail the same way — so predefining the
// function panics with "not implemented". All of these compile and run under cg_llvm.
// The related WeakAny case does not ICE but drops the weak binding; that is covered by
// tests/run/bug_linkage_weak.rs.

#![feature(linkage)]

#[linkage = "weak_odr"]
#[no_mangle]
pub extern "C" fn my_func() -> u32 {
    7
}

fn main() {
    println!("{}", my_func());
}
