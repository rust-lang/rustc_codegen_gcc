// Compiler:
//
// Run-time:
//   status: 2

#![feature(auto_traits, lang_items, no_core, intrinsics)]
#![allow(internal_features)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

use mini_core::libc;

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        libc::exit(2);
    }
    0
}
