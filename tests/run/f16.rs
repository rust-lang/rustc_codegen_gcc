// Compiler:
//
// Run-time:
//   status: 0

#![feature(core_intrinsics, f16, float_algebraic)]
#![allow(internal_features)]

use std::cmp::Ordering;
use std::hint::black_box;
use std::intrinsics::{fmaf16, powif16};

fn assert_f16_bits(value: f16, bits: u16) {
    assert_eq!(value.to_bits(), bits);
}

fn main() {
    let one_and_half = black_box(f16::from_bits(0x3e00));
    assert_eq!(one_and_half as f32, 1.5f32);
    assert_eq!(one_and_half as f64, 1.5f64);

    let three_and_three_quarters = black_box(f16::from_bits(0x4380));
    assert_eq!(three_and_three_quarters as i32, 3);
    assert_eq!(three_and_three_quarters as u32, 3);

    let negative_two_and_half = black_box(f16::from_bits(0xc100));
    assert_eq!(negative_two_and_half as i32, -2);
    assert_eq!(negative_two_and_half as u32, 0);

    assert_f16_bits(black_box(1.5f32) as f16, 0x3e00);
    assert_f16_bits(black_box(-2.0f32) as f16, 0xc000);
    assert_f16_bits(black_box(1.5f64) as f16, 0x3e00);
    assert_f16_bits(black_box(42i32) as f16, 0x5140);
    assert_f16_bits(black_box(42u32) as f16, 0x5140);

    let one = black_box(1.0f16);
    let two = black_box(2.0f16);
    let three = black_box(3.0f16);
    assert_f16_bits(one + two, 0x4200);
    assert_f16_bits(two * three, 0x4600);
    assert_f16_bits(two / one, 0x4000);
    assert_f16_bits(-three, 0xc200);
    assert_f16_bits(fmaf16(one, two, -three), 0xbc00);
    assert_f16_bits(powif16(two, 3), 0x4800);

    assert_f16_bits(black_box(123.0f16).algebraic_add(black_box(456.0f16)), 0x6086);
    assert_f16_bits(black_box(123.0f16).algebraic_rem(black_box(17.0f16)), 0x4400);

    let q_nan = f16::from_bits(0x7e00);
    let s_nan = f16::from_bits(0x7c2a);
    assert_f16_bits(-q_nan, 0xfe00);
    assert_f16_bits(-s_nan, 0xfc2a);
    assert_eq!(f16::total_cmp(&-q_nan, &-s_nan), Ordering::Less);
}
