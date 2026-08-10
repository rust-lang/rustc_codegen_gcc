// Compiler:
//   status: 0

// Reproducer for: `global_asm!` comment stripping corrupts `//` inside string literals
// (codegen-audit-2026-08.md). Because GAS has no `//` line comments, src/asm.rs strips
// `//...` from the template — but without any string-literal awareness, so the `//` in
// `.ascii "http://x"` is treated as a comment start and the rest of the line is deleted,
// leaving an unterminated string. The assembler then rejects the output (`unterminated
// string`, `junk at end of line`) and the compilation fails; a template that still happened
// to assemble would silently contain corrupted data. cg_llvm passes the template through
// verbatim and compiles this fine.

use std::arch::global_asm;

global_asm!(
    ".pushsection .rodata",
    ".globl MY_BYTES",
    "MY_BYTES:",
    ".ascii \"http://x\"",
    ".popsection",
);

unsafe extern "C" {
    #[link_name = "MY_BYTES"]
    static MY_BYTES: [u8; 8];
}

fn main() {
    let bytes = unsafe { std::ptr::read_volatile(&raw const MY_BYTES) };
    assert_eq!(&bytes, b"http://x");
    println!("bytes={:?}", std::str::from_utf8(&bytes));
}
