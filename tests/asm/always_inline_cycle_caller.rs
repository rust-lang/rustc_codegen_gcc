//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=0

#![crate_type = "lib"]
#![no_std]

#[inline(always)]
fn countdown(n: u32) -> u32 {
    if n == 0 { 0 } else { countdown(n - 1) }
}

// Reaching a cycle is not being on one: only `countdown` loses always_inline.
#[inline(always)]
fn wrapper(n: u32) -> u32 {
    countdown(n)
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK-NOT: {{call.*wrapper}}
// CHECK: {{call.*countdown}}
// CHECK-NOT: {{call.*wrapper}}
// CHECK: ret
#[no_mangle]
pub fn entry(n: u32) -> u32 {
    wrapper(n)
}
