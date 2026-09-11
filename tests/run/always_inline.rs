// Compiler:
//
// Run-time:
//   status: 0

#![feature(no_core, stmt_expr_attributes)]
#![no_std]
#![no_core]
#![no_main]

extern crate mini_core;
use mini_core::*;

#[inline(always)]
fn fib(n: u8) -> u8 {
    if n == 0 {
        return 1;
    }
    if n == 1 {
        return 1;
    }
    fib(n - 1) + fib(n - 2)
}

#[inline(always)]
fn fib_b(n: u8) -> u8 {
    if n == 0 {
        return 1;
    }
    if n == 1 {
        return 1;
    }
    fib_a(n - 1) + fib_a(n - 2)
}

#[inline(always)]
fn fib_a(n: u8) -> u8 {
    if n == 0 {
        return 1;
    }
    if n == 1 {
        return 1;
    }
    fib_b(n - 1) + fib_b(n - 2)
}

// These cycles only show up after monomorphization: the generic callers call
// `<T as Step>::step` and `<F as FnMut>::call_mut`, not the impls.
trait Step {
    fn step(n: u8) -> u8;
}

struct S;

impl Step for S {
    #[inline(always)]
    fn step(n: u8) -> u8 {
        if n == 0 {
            return 0;
        }
        drive::<Self>(n - 1) + 1
    }
}

#[inline(always)]
fn drive<T: Step>(n: u8) -> u8 {
    T::step(n)
}

#[inline(always)]
fn apply<F: FnMut(u8) -> u8>(mut f: F, n: u8) -> u8 {
    f(n)
}

#[inline(always)]
fn countdown(n: u8) -> u8 {
    if n == 0 {
        return 0;
    }
    apply(
        #[inline(always)]
        |m| countdown(m),
        n - 1,
    ) + 1
}

// GCC turns a call through a known fn pointer into a direct call, which closes the cycle.
#[inline(always)]
fn via_pointer(n: u8) -> u8 {
    if n == 0 {
        return 0;
    }
    let f: fn(u8) -> u8 = via_direct;
    f(n - 1) + 1
}

#[inline(always)]
fn via_direct(n: u8) -> u8 {
    via_pointer(n)
}

#[no_mangle]
extern "C" fn main(argc: i32, _argv: *const *const u8) -> i32 {
    if fib(2) != fib_a(2) {
        intrinsics::abort();
    }
    if drive::<S>(3) != 3 {
        intrinsics::abort();
    }
    if countdown(3) != 3 {
        intrinsics::abort();
    }
    if via_direct(3) != 3 {
        intrinsics::abort();
    }
    0
}
