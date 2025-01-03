// Compiler:
//
// Run-time:
//   status: 0

#![feature(no_core, start)]
#![allow(internal_features)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

#[start]
fn main(_argc: isize, _argv: *const *const u8) -> isize {
    0
}
