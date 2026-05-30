// Compiler:
//   status: error
//   stderr:
//     error: GCC backend does not support `asm goto` with output operands
//     ...

// Test that an `asm goto` with output operands emits a clean error instead of an
// ICE: libgccjit rejects output operands on an `asm goto` (issue #835).

#![feature(asm_goto_with_outputs)]

use std::arch::asm;

fn main() {
    let mut a: i32 = 0;
    unsafe {
        asm!(
            "jmp {op}",
            inout("eax") a,
            op = label { a = 7; },
            options(nostack, nomem),
        );
    }
    let _ = a;
}
