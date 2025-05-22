// Compiler:
//
// Run-time:

#![feature(no_core, intrinsics)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use intrinsics::black_box;
use mini_core::*;

#[rustc_intrinsic]
pub const fn ctlz<T: Copy>(_x: T) -> u32;

#[rustc_intrinsic]
pub const fn cttz<T: Copy>(_x: T) -> u32;

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    if ctlz(black_box(0_u128)) != 128 {
        return 1;
    }
    if ctlz(black_box(1_u128)) != 127 {
        return 2;
    }
    if cttz(black_box(0_u128)) != 128 {
        return 3;
    }
    if cttz(black_box(1_u128)) != 0 {
        return 4;
    }
    if cttz(black_box(2_u128)) != 1 {
        return 4;
    }
    0
}
