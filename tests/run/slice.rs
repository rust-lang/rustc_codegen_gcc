// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 5

#![feature(no_core, start)]
#![allow(internal_features)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

static mut TWO: usize = 2;

fn index_slice(s: &[u32]) -> u32 {
    unsafe {
        s[TWO]
    }
}

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    let array = [42, 7, 5];
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, index_slice(&array));
    }
    0
}
