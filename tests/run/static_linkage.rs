// Compiler:
//
// Run-time:
//   status: 0

// Checks that `#[linkage]` on a static that this crate defines reaches the symbol, against
// `tests/c/static_linkage.c`, which defines the overridable ones strongly.
//
// `predefine_static` used to ignore its `linkage` argument outright, so every static came out as
// an ordinary global symbol: the overridable ones clashed with the C definitions at link time, and
// `internal` exported a symbol it should have kept private.

#![feature(linkage, no_core)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

#[linkage = "weak"]
#[no_mangle]
pub static weak_static: i32 = 0;

#[linkage = "weak_odr"]
#[no_mangle]
pub static weak_odr_static: i32 = 0;

#[linkage = "linkonce"]
#[no_mangle]
pub static linkonce_static: i32 = 0;

#[linkage = "linkonce_odr"]
#[no_mangle]
pub static linkonce_odr_static: i32 = 0;

#[linkage = "common"]
#[no_mangle]
pub static common_static: i32 = 0;

// Private to this crate, so the C definition of the same name is a different object.
#[linkage = "internal"]
#[no_mangle]
pub static internal_static: i32 = 100;

// Not overridden by the C side: the definition here is the one that survives.
#[linkage = "weak"]
#[no_mangle]
pub static only_weak_static: i32 = 6;

// Emitted as a private copy of a definition that lives elsewhere, so it must still be readable.
#[linkage = "available_externally"]
#[no_mangle]
pub static available_externally_static: i32 = 7;

extern "C" {
    fn c_read_all() -> i32;
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    let result = unsafe { c_read_all() };
    if result != 0 {
        return result;
    }

    if internal_static != 100 {
        return 1;
    }
    if only_weak_static != 6 {
        return 2;
    }
    if available_externally_static != 7 {
        return 3;
    }
    0
}
