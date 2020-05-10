// Compiler:
//
// Run-time:
//   status: signal

#![feature(optin_builtin_traits, lang_items, link_args, no_core, start, intrinsics)]

#![no_std]
#![no_core]

#[link_args="-lc"]
extern {
}

/*
 * Core
 */

// Because we don't have core yet.
#[lang = "sized"]
pub trait Sized {}

#[lang = "copy"]
trait Copy {
}

impl Copy for isize {}

#[lang = "receiver"]
trait Receiver {
}

#[lang = "freeze"]
pub(crate) unsafe auto trait Freeze {}

mod intrinsics {
    use super::Sized;

    extern "rust-intrinsic" {
        pub fn abort() -> !;
    }
}

/*
 * Code
 */

fn fail() -> i32 {
    unsafe { intrinsics::abort() };
    0
}

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    fail();
    0
}
