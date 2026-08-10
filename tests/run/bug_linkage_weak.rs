// Compiler:
//
// Run-time:
//   status: 0
//   stdout: provider via C = 999

// Reproducer for: `#[linkage = "weak"]` emits a STRONG (GLOBAL) symbol instead of a WEAK
// one (codegen-audit-2026-08.md). `linkage_to_gcc` in src/base.rs maps `WeakAny` to
// `FunctionType::Exported`, dropping the weak binding, so a weak Rust default cannot
// coexist with (and be overridden by) a strong definition. The strong `provider` in
// `tests/c/bug_linkage_weak.c` must win over the weak Rust definition below; under cg_gcc
// the link currently FAILS with `duplicate symbol: provider`, so the compile step of this
// test fails until the bug is fixed (under cg_llvm it links and prints 999).

#![feature(linkage)]

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn provider() -> u32 {
    111 // weak default, must lose against the strong C definition
}

unsafe extern "C" {
    fn call_provider() -> u32;
}

fn main() {
    let value = unsafe { call_provider() };
    println!("provider via C = {}", value);
}
