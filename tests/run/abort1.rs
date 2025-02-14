// Compiler:
//
// Run-time:
//   status: signal

#![feature(auto_traits, lang_items, no_core, intrinsics, rustc_attrs)]
#![allow(internal_features)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

fn test_fail() -> ! {
    mini_core::intrinsics::abort();
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    test_fail();
}
