// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 3

#![feature(auto_traits, lang_items, no_core, intrinsics)]
#![allow(internal_features)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

use mini_core::libc;

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let test: (isize, isize, isize) = (3, 1, 4);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.0);
    }
    0
}
