//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=2

#![crate_type = "lib"]
#![no_std]

// Recursing through a plain helper is fine for GCC as long as every step is a direct call, so
// `step` keeps always_inline.
#[inline(always)]
fn step(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    let acc = n.wrapping_mul(0x9e3779b1).rotate_left(5);
    helper(n - 1).wrapping_add(helper(n / 2)).wrapping_add(acc)
}

fn helper(n: u32) -> u32 {
    step(n)
}

#[no_mangle]
pub fn other(n: u32) -> u32 {
    step(n)
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK-NOT: {{(call|jmp).*step}}
// CHECK: .size
#[no_mangle]
pub fn entry(n: u32) -> u32 {
    step(n.wrapping_add(1))
}
