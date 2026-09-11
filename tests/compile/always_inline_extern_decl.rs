// Compiler:

// A declaration has no body to inline, so it must not get always_inline.

#![crate_type = "lib"]
#![allow(unused_attributes)]

unsafe extern "C" {
    #[inline(always)]
    fn abs(x: i32) -> i32;
}

pub fn entry(x: i32) -> i32 {
    unsafe { abs(x) }
}
