//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=1
//@ aux-build: avx_generic.rs

#![crate_type = "lib"]
#![no_std]

// `imported::<()>` comes from the upstream crate, built with avx. We only declare it here, so its
// body must not be checked against our target features.
extern crate avx_generic;

static TABLE: [fn(); 1] = [avx_generic::imported::<()>];

#[inline(always)]
fn wrapper() {
    TABLE[0]()
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK: ret
#[no_mangle]
pub fn entry() {
    wrapper()
}
