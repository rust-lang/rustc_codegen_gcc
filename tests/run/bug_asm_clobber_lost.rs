// Compiler:
//
// Run-time:
//   status: 0
//   stdout: result = 42

// Reproducer for: an explicit-register clobber is silently LOST when the same register is
// also an input (codegen-audit-2026-08.md). In src/asm.rs, a `lateout("rcx") _` whose
// register already appears as an input (`in("rcx") x`) is rewritten into a generic `"=r"`
// dummy output that is neither pinned to rcx nor added to the clobber list, so GCC believes
// rcx is preserved across the asm and reads the pre-asm value back afterwards. This is
// exactly the documented "call a function from asm" pattern (`in("rdi") x` +
// `clobber_abi("C")`). cg_gcc currently prints `result = 1` at -O3 (it rematerializes `x`
// from the clobbered register); this test asserts the correct result, so it fails until
// the bug is fixed. The asm is x86_64-specific; other targets print the expected output
// directly and pass trivially.

#[cfg(target_arch = "x86_64")]
#[inline(never)]
fn victim(x: u64) -> u64 {
    unsafe {
        std::arch::asm!(
            "mov rcx, 0",
            in("rcx") x,
            lateout("rcx") _,
            lateout("rax") _, lateout("rdx") _, lateout("rsi") _, lateout("rdi") _,
            lateout("r8") _, lateout("r9") _, lateout("r10") _, lateout("r11") _,
            options(nostack, nomem)
        );
    }
    x + 1
}

#[cfg(not(target_arch = "x86_64"))]
fn victim(x: u64) -> u64 {
    x + 1
}

fn main() {
    let result = victim(std::hint::black_box(41));
    println!("result = {}", result);
}
