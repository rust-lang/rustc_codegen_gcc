// Compiler:
//   status: 0

// Reproducer for: referencing a `sym` operand more than once in an asm template ICEs
// (codegen-audit-2026-08.md). src/asm.rs stores one symbol name per `sym`/const-pointer
// OPERAND but pops one entry per template REFERENCE (`const_syms.remove(0)`), so the second
// `{0}` hits an empty Vec: `panicked at src/asm.rs: removal index (is 0) should be < len
// (is 0)`. cg_llvm compiles and runs this fine. Same root cause as the operand-order bug
// covered by tests/run/bug_asm_sym_order.rs. The asm is x86_64-specific; on other targets
// this compiles trivially.

#[no_mangle]
extern "C" fn func_a() -> u64 {
    111
}

#[cfg(target_arch = "x86_64")]
fn run() -> (u64, u64) {
    let first: u64;
    let second: u64;
    unsafe {
        std::arch::asm!(
            "call {0}",
            "mov r12, rax",
            "call {0}",
            "mov r13, rax",
            sym func_a,
            out("r12") first,
            out("r13") second,
            clobber_abi("C"),
        );
    }
    (first, second)
}

#[cfg(not(target_arch = "x86_64"))]
fn run() -> (u64, u64) {
    (func_a(), func_a())
}

fn main() {
    let (first, second) = run();
    assert_eq!((first, second), (111, 111));
    println!("ok");
}
