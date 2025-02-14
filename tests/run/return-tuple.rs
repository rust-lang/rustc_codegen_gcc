// Compiler:
//
// Run-time:
//   status: 0
//   stdout: 10
//     10
//     42

#![feature(auto_traits, lang_items, no_core, intrinsics)]
#![allow(internal_features)]

#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

use mini_core::libc;

fn int_cast(a: u16, b: i16) -> (u8, u16, u32, usize, i8, i16, i32, isize, u8, u32) {
    (
        a as u8, a as u16, a as u32, a as usize, a as i8, a as i16, a as i32, a as isize, b as u8,
        b as u32,
    )
}

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    let (a, b, c, d, e, f, g, h, i, j) = int_cast(10, 42);
    unsafe {
        libc::printf(b"%d\n\0" as *const u8 as *const i8, c);
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, d);
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, j);
    }
    0
}
