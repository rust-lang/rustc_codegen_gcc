// Compiler:

// To GCC, calling an EII declaration from its own implementation is a plain self-call.

#![crate_type = "lib"]
#![feature(extern_item_impls)]
#![allow(incomplete_features, unused_attributes)]

#[eii]
fn callback(n: u32) -> u32;

#[inline(always)]
fn leaf(n: u32) -> u32 {
    n - 1
}

#[callback]
#[inline(always)]
fn implementation(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    callback(leaf(n)) + 1
}

#[unsafe(no_mangle)]
pub fn entry(n: u32) -> u32 {
    implementation(n)
}
