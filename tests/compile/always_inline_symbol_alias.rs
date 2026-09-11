// Compiler:

// `alias` is `recurse` under another name, so the Rust call graph can't see this recursion.

#![crate_type = "lib"]
#![allow(unused_attributes)]

unsafe extern "C" {
    #[link_name = "recurse"]
    fn alias(n: u32) -> u32;
}

#[inline(always)]
fn leaf(n: u32) -> u32 {
    n - 1
}

#[unsafe(no_mangle)]
#[inline(always)]
pub extern "C" fn recurse(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    unsafe { alias(leaf(n)) + 1 }
}

pub fn entry(n: u32) -> u32 {
    recurse(n)
}
