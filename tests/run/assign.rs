// Compiler:
//
// Run-time:
//   stdout: 2
//     7 8
//     10

#![allow(internal_features, unused_attributes)]
#![feature(no_core, start, include, include_str)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

fn inc_ref(num: &mut isize) -> isize {
    *num = *num + 5;
    *num + 1
}

fn inc(num: isize) -> isize {
    num + 1
}


#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    argc = inc(argc);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }

    let b = inc_ref(&mut argc);
    unsafe {
        libc::printf(b"%ld %ld\n\0" as *const u8 as *const i8, argc, b);
    }

    argc = 10;
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }
    0
}
