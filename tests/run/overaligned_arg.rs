// Compiler:
//
// Run-time:
//   status: 0

#![feature(no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;

#[repr(align(64))]
struct AlignedF32(f32);

#[inline(never)]
extern "C" fn write<T>(value: T, destination: &mut T) {
    *destination = value;
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let mut output = AlignedF32(0.0);
    write(AlignedF32(6.0), &mut output);
    output.0 as i32 - 6
}
