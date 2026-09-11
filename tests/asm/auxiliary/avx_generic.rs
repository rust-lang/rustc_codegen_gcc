//@ no-prefer-dynamic
//@ compile-flags: -Copt-level=1 -Ctarget-feature=+avx

#![crate_type = "rlib"]
#![no_std]
#![feature(simd_ffi)]
#![allow(improper_ctypes)]

use core::arch::x86_64::__m256;

unsafe extern "C" {
    fn takes_avx(value: __m256);
}

pub fn imported<T>() {
    unsafe { takes_avx(core::mem::zeroed()) }
}

pub fn instantiate() {
    imported::<()>();
}
