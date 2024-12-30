// Compiler:
//
// Run-time:
//   status: signal

#![feature(no_core, start)]
#![allow(internal_features)]

#![no_std]
#![no_core]

/*
 * Core
 */

 extern crate mini_core;
 use mini_core::{intrinsics, Sized, Copy, Receiver, Freeze};

/*
 * Code
 */

fn fail() -> i32 {
    unsafe { intrinsics::abort() };
    0
}

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    fail();
    0
}
