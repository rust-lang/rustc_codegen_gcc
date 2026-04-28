// Compiler:
//
// Run-time:
//   status: 0

#![feature(no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

#[inline(never)]
unsafe fn zero_sized_mem_ops(count: usize) {
    let src = 0usize as *const ();
    let dst = 0usize as *mut ();

    intrinsics::copy_nonoverlapping(src, dst, count);
    intrinsics::copy(src, dst, count);
    intrinsics::write_bytes(dst, 0xab, count);
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe { zero_sized_mem_ops(1) };
    0
}
