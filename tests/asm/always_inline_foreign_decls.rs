//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=0

#![crate_type = "lib"]
#![no_std]
#![feature(extern_item_impls)]
#![allow(incomplete_features, unused_attributes)]

// Being reachable from a foreign declaration only matters when it closes a cycle.

#[eii]
fn hook(n: u32) -> u32;

#[hook]
#[inline(always)]
fn hook_impl(n: u32) -> u32 {
    n.wrapping_mul(3)
}

unsafe extern "C" {
    #[link_name = "exported"]
    fn exported_alias(n: u32) -> u32;
}

#[no_mangle]
#[inline(always)]
pub extern "C" fn exported(n: u32) -> u32 {
    n.wrapping_add(5)
}

#[no_mangle]
pub fn through_decls(n: u32) -> u32 {
    hook(n).wrapping_add(unsafe { exported_alias(n) })
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK-NOT: call
// CHECK: ret
#[no_mangle]
pub fn entry(n: u32) -> u32 {
    hook_impl(n).wrapping_add(exported(n))
}
