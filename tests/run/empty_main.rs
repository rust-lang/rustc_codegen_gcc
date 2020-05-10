// Compiler:
//
// Run-time:
//   status: 0

#![feature(optin_builtin_traits, lang_items, link_args, no_core, start)]

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

/*
 * Code
 */

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    0
}
