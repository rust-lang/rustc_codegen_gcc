// Compiler:
//
// Run-time:
//   status: 0
//   stdout: first=222 second=111

// Reproducer for: `sym` operands are spliced into the template in DECLARATION order, not
// template-reference order (codegen-audit-2026-08.md). src/asm.rs collects the symbol names
// of `sym`/const-pointer operands into a Vec in operand order but consumes them with
// `remove(0)` while walking the template, so a template that references `{1}` before `{0}`
// gets the two symbols swapped — it calls the WRONG functions. cg_gcc currently prints
// `first=111 second=222`; this test asserts the correct mapping, so it fails until the bug
// is fixed. The asm is x86_64-specific; other targets print the expected output directly
// and pass trivially.

#[no_mangle]
extern "C" fn func_a() -> u64 {
    111
}

#[no_mangle]
extern "C" fn func_b() -> u64 {
    222
}

#[cfg(target_arch = "x86_64")]
fn run() -> (u64, u64) {
    let first: u64;
    let second: u64;
    unsafe {
        // The template references operand 1 BEFORE operand 0.
        std::arch::asm!(
            "call {1}",
            "mov r12, rax",
            "call {0}",
            "mov r13, rax",
            sym func_a,
            sym func_b,
            out("r12") first,
            out("r13") second,
            clobber_abi("C"),
        );
    }
    (first, second)
}

#[cfg(not(target_arch = "x86_64"))]
fn run() -> (u64, u64) {
    (func_b(), func_a())
}

fn main() {
    let (first, second) = run();
    println!("first={} second={}", first, second);
}
