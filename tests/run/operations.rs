// Compiler:
//
// Run-time:
//   stdout: 41
//     39
//     10

#![allow(internal_features, unused_attributes)]
#![feature(auto_traits, lang_items, no_core, intrinsics, arbitrary_self_types, rustc_attrs)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

use mini_core::libc;

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, 40 + argc);
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, 40 - argc);
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, 10 * argc);
    }
    0
}
