// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 1

#![feature(no_core, start, include, include_str)]
#![allow(internal_features)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

static mut ONE: usize = 1;

fn make_array() -> [u8; 3] {
    [42, 10, 5]
}

#[start]
fn main(argc: isize, _argv: *const *const u8) -> isize {
    unsafe {
        let ptr = ONE as *mut usize;
        let value = ptr as usize;
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, value);
    }
    0
}
