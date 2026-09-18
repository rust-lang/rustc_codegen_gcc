//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=0

#![crate_type = "lib"]
#![no_std]

// At -O0, an ordinary inline hint is insufficient: the entire chain must retain
// always_inline even though its wrappers call other always-inline functions.
#[inline(always)]
fn leaf(x: u32) -> u32 {
    x ^ 0xa5a5
}

#[inline(always)]
fn mid(x: u32) -> u32 {
    leaf(x).wrapping_mul(3)
}

#[inline(always)]
fn top(x: u32) -> u32 {
    mid(x).wrapping_add(7)
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK-NOT: call
// CHECK: ret
#[no_mangle]
pub fn entry(x: u32) -> u32 {
    top(x)
}
