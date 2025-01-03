
// Compiler:
//
// Run-time:
//   stdout: 2
//     7
//     6
//     11

#![allow(internal_features, unused_attributes)]
#![feature(no_core, start, include, include_str)]

#![no_std]
#![no_core]

include!("../../example/mini_core.rs");

/*
 * Code
 */

struct Test {
    field: isize,
}

fn test(num: isize) -> Test {
    Test {
        field: num + 1,
    }
}

fn update_num(num: &mut isize) {
    *num = *num + 5;
}

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    let mut test = test(argc);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.field);
    }
    update_num(&mut test.field);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, test.field);
    }

    update_num(&mut argc);
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }

    let refe = &mut argc;
    *refe = *refe + 5;
    unsafe {
        libc::printf(b"%ld\n\0" as *const u8 as *const i8, argc);
    }

    0
}
