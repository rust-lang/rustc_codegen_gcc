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
    macro_rules! check {
        ($func_name:ident, $input:expr, $expected:expr, $res:expr) => {{
            if $func_name(black_box($input)) != $expected {
                return $res;
            }
        }};
    }

    check!(ctlz, 0_u128, 128_u32, 1);
    check!(ctlz, 1_u128, 127_u32, 2);
    check!(ctlz, 0x8000_0000_0000_0000_0000_0000_0000_0000_u128, 0_u32, 3);
    check!(cttz, 0_u128, 128_u32, 4);
    check!(cttz, 1_u128, 0_u32, 5);
    check!(cttz, 2_u128, 1_u32, 6);
    check!(cttz, 0x8000_0000_0000_0000_0000_0000_0000_0000_u128, 127_u32, 7);

    check!(ctlz, 0_u64, 64_u32, 8);
    check!(ctlz, 1_u64, 63_u32, 9);
    check!(ctlz, 0x8000_0000_0000_0000_u64, 0_u32, 10);
    check!(cttz, 0_u64, 64_u32, 11);
    check!(cttz, 1_u64, 0_u32, 12);
    check!(cttz, 2_u64, 1_u32, 13);
    check!(cttz, 0x8000_0000_0000_0000_u64, 63_u32, 14);

    check!(ctlz, 0_u32, 32_u32, 15);
    check!(ctlz, 1_u32, 31_u32, 16);
    check!(ctlz, 0x8000_0000_u32, 0_u32, 17);
    check!(cttz, 0_u32, 32_u32, 18);
    check!(cttz, 1_u32, 0_u32, 19);
    check!(cttz, 2_u32, 1_u32, 20);
    check!(cttz, 0x8000_0000_u32, 31_u32, 21);

    check!(ctlz, 0_u16, 16_u32, 22);
    check!(ctlz, 1_u16, 15_u32, 23);
    check!(ctlz, 0x8000_u16, 0_u32, 24);
    check!(cttz, 0_u16, 16_u32, 25);
    check!(cttz, 1_u16, 0_u32, 26);
    check!(cttz, 2_u16, 1_u32, 27);
    check!(cttz, 0x8000_u16, 15_u32, 28);

    check!(ctlz, 0_u8, 8_u32, 29);
    check!(ctlz, 1_u8, 7_u32, 30);
    check!(ctlz, 0x80_u8, 0_u32, 31);
    check!(cttz, 0_u8, 8_u32, 32);
    check!(cttz, 1_u8, 0_u32, 33);
    check!(cttz, 2_u8, 1_u32, 34);
    check!(cttz, 0x80_u8, 7_u32, 35);

    0
}
