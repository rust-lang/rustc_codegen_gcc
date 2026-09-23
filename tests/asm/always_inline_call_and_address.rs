//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=2

#![crate_type = "lib"]
#![no_std]

// `helper` both calls `forced` and returns its address. Once GCC inlines `helper`, that address
// turns into direct calls back into `forced`, so `forced` must lose always_inline.

#[inline(always)]
fn forced(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    let f = helper();
    f(n - 1).wrapping_add(f(n / 2)).wrapping_add(n)
}

#[inline]
fn helper() -> fn(u32) -> u32 {
    let _ = forced(0);
    forced
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK: .size
#[no_mangle]
pub fn entry(n: u32) -> u32 {
    forced(n)
}
