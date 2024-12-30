// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 1

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
    Add,
    Sub,
    Index,
    Sized,
    Copy,
    Receiver,
    Freeze
};

/*
 * Code
 */

fn i16_as_i8(a: i16) -> i8 {
    a as i8
}

fn call_func(func: fn(i16) -> i8, param: i16) -> i8 {
    func(param)
}

#[start]
fn main(argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        let result = call_func(i16_as_i8, argc as i16) as isize;
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, result);
    }
    0
}
