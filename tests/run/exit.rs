// Compiler:
//
// Run-time:
//   status: 2

#![feature(no_core, start)]
#![allow(internal_features)]

#![no_std]
#![no_core]

mod libc {
    #[link(name = "c")]
    extern "C" {
        pub fn exit(status: i32);
    }
}

/*
 * Core
 */

extern crate mini_core;
use mini_core::{
    libc,
    Sized,
    Copy,
    Receiver,
    Freeze
};

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
