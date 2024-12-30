// Compiler:
//
// Run-time:
//   status: 1

#![feature(no_core, start)]
#![allow(internal_features)]

#![no_std]
#![no_core]

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
    1
}
