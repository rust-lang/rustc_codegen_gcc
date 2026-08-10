//@ assembly-output: emit-asm
//@ compile-flags: --crate-type staticlib

// Reproducer for: `#[linkage = "weak"]` emits a STRONG (GLOBAL) symbol
// (codegen-audit-2026-08.md). `linkage_to_gcc` (src/base.rs) maps `WeakAny` to
// `FunctionType::Exported`, so the assembly contains `.globl` with no `.weak` directive
// and the symbol table binding is GLOBAL instead of WEAK. A weak definition must be
// overridable by a strong one; see tests/run/bug_linkage_weak.rs for the resulting
// duplicate-symbol link failure against a GCC-built strong definition.

#![feature(linkage)]

#[linkage = "weak"]
#[no_mangle]
pub extern "C" fn overridable_default() -> u32 {
    111
}

// CHECK: .weak{{.*}}overridable_default
