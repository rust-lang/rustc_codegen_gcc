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

fn fail() -> i32 {
    mini_core::intrinsics::abort();
    0
}

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    fail();
    0
}
