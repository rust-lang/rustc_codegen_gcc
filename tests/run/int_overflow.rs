// Compiler:
//
// Run-time:
//   stdout: Panicking
//   status: signal

#![allow(unused_attributes)]
#![feature(optin_builtin_traits, lang_items, link_args, no_core, start, intrinsics, track_caller)]

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
impl Copy for *mut i32 {}

#[lang = "receiver"]
trait Receiver {
}

#[lang = "freeze"]
pub(crate) unsafe auto trait Freeze {}

#[lang = "panic_location"]
struct PanicLocation {
    file: &'static str,
    line: u32,
    column: u32,
}

mod libc {
    #[link(name = "c")]
    extern "C" {
        pub fn puts(s: *const u8) -> i32;
        pub fn fflush(stream: *mut i32) -> i32;

        pub static STDOUT: *mut i32;
    }
}

mod intrinsics {
    extern "rust-intrinsic" {
        pub fn abort() -> !;
    }
}

#[lang = "panic"]
#[track_caller]
#[no_mangle]
pub fn panic(_msg: &str) -> ! {
    unsafe {
        libc::puts("Panicking\0" as *const str as *const u8);
        libc::fflush(libc::STDOUT);
        intrinsics::abort();
    }
}

#[lang = "add"]
trait Add<RHS = Self> {
    type Output;

    fn add(self, rhs: RHS) -> Self::Output;
}

impl Add for u8 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Add for i8 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Add for i32 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Add for usize {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
}

impl Add for isize {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self + rhs
    }
}

/*
 * Code
 */

#[start]
fn main(mut argc: isize, _argv: *const *const u8) -> isize {
    let int = 9223372036854775807isize;
    let int = int + argc;
    int
}
