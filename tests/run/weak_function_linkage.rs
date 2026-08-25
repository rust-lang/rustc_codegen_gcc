// Compiler:
//
// Run-time:
//   status: 0

// Checks that the `#[linkage]` flavours another object file is allowed to override are emitted as
// weak symbols, by linking against `tests/c/weak_function_linkage.c`, which defines the same
// symbols strongly.

#![feature(linkage, no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

#[linkage = "weak"]
#[no_mangle]
extern "C" fn weak_function() -> i32 {
    0
}

#[linkage = "weak_odr"]
#[no_mangle]
extern "C" fn weak_odr_function() -> i32 {
    0
}

#[linkage = "linkonce"]
#[no_mangle]
extern "C" fn linkonce_function() -> i32 {
    0
}

#[linkage = "linkonce_odr"]
#[no_mangle]
extern "C" fn linkonce_odr_function() -> i32 {
    0
}

#[linkage = "common"]
#[no_mangle]
extern "C" fn common_function() -> i32 {
    0
}

// Not overridden by the C side: the definition here is the one that runs.
#[linkage = "weak"]
#[no_mangle]
extern "C" fn only_weak_function() -> i32 {
    6
}

// Emitted as a private copy of a definition that lives elsewhere, so it must still be callable.
#[linkage = "available_externally"]
#[no_mangle]
extern "C" fn available_externally_function() -> i32 {
    7
}

// GCC warns that `inline` and `weak` conflict, and cg_gcc turns libgccjit warnings into errors, so
// this used to fail to compile at all. The inline hint is what gives way: rustc lints it as ignored
// on a function with an explicit `#[linkage]` anyway, hence the `allow`.
#[linkage = "weak"]
#[inline]
#[allow(unused_attributes)]
extern "C" fn weak_inline_function() -> i32 {
    8
}

extern "C" {
    fn c_call_all() -> i32;
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let result = unsafe { c_call_all() };
    if result != 0 {
        return result;
    }

    if weak_function() != 1 {
        return 1;
    }
    if weak_odr_function() != 2 {
        return 2;
    }
    if linkonce_function() != 3 {
        return 3;
    }
    if linkonce_odr_function() != 4 {
        return 4;
    }
    if common_function() != 5 {
        return 5;
    }
    if only_weak_function() != 6 {
        return 6;
    }
    if available_externally_function() != 7 {
        return 7;
    }
    if weak_inline_function() != 8 {
        return 8;
    }
    0
}
