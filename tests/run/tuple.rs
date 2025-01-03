// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 3

#![feature(auto_traits, lang_items, no_core, start, intrinsics)]
#![allow(internal_features)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    let test: (isize, isize, isize) = (3, 1, 4);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.0);
    }
    0
}
