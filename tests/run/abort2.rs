// Compiler:
//
// Run-time:
//   status: signal

#![feature(no_core, start, include, include_str)]
#![allow(internal_features)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

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
