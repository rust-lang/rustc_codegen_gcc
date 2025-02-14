// Compiler:
//
// Run-time:
//   status: 0

#![feature(auto_traits, lang_items, no_core)]
#![allow(internal_features)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    0
}
