// Compiler:
//
// Run-time:
//   status: 2

#![feature(no_core, start, include, include_str)]
#![allow(internal_features)]

#![no_std]
#![no_core]

mod libc {
    #[link(name = "c")]
    extern "C" {
        pub fn exit(status: i32);
    }
}

include!("../../example/mini_core.rs");

/*
 * Code
 */

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        libc::exit(2);
    }
    0
}
