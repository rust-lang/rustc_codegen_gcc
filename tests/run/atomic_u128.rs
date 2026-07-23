// Compiler:
//
// Run-time:
//   status: 0

// Exercises lock-free inline 128-bit atomics. Platform-agnostic: the backend
// emits `cmpxchg16b` on x86-64 and `ldxp/stxp` on aarch64 from the same code.
// x86-64 needs the `cmpxchg16b` feature (aarch64 has 128-bit atomics in the
// baseline), so the flag is guarded to x86-64 only. State is checked with
// compare_exchange (a bool result) to avoid needing a `PartialEq`/`Add` impl for
// `u128` in `no_core`.

//@ [x86_64] compile-flags: -Ctarget-feature=+cmpxchg16b

#![feature(no_core, intrinsics, rustc_attrs, lang_items, adt_const_params, unsized_const_params)]
#![no_std]
#![no_core]
#![no_main]
#![allow(internal_features, incomplete_features)]

extern crate mini_core;
use mini_core::*;

pub trait Eq: PartialEq {}
#[lang = "const_param_ty"]
pub trait ConstParamTy_: StructuralPartialEq + Eq {}

pub enum Ordering {
    Relaxed,
    Release,
    Acquire,
    AcqRel,
    SeqCst,
}
impl Copy for Ordering {}
impl PartialEq for Ordering {
    fn eq(&self, other: &Self) -> bool {
        (*self as u8) == (*other as u8)
    }
    fn ne(&self, other: &Self) -> bool {
        (*self as u8) != (*other as u8)
    }
}
impl Eq for Ordering {}
impl StructuralPartialEq for Ordering {}
impl ConstParamTy_ for Ordering {}

#[rustc_intrinsic]
unsafe fn atomic_store<T: Copy, const ORD: Ordering>(destination: *mut T, value: T);
#[rustc_intrinsic]
unsafe fn atomic_xadd<T: Copy, U: Copy, const ORD: Ordering>(destination: *mut T, value: U) -> T;
#[rustc_intrinsic]
unsafe fn atomic_cxchg<T: Copy, const SUCCESS: Ordering, const FAILURE: Ordering>(
    destination: *mut T,
    old: T,
    new: T,
) -> (T, bool);

static mut VALUE: u128 = 0;

/// True if `*pointer == expected`, checked via a no-op compare_exchange so we do
/// not need `PartialEq` for `u128`.
unsafe fn holds(pointer: *mut u128, expected: u128) -> bool {
    let (_, matched) =
        atomic_cxchg::<u128, { Ordering::SeqCst }, { Ordering::SeqCst }>(pointer, expected, expected);
    matched
}

#[no_mangle]
extern "C" fn main(_argc: i32, _argv: *const *const u8) -> i32 {
    unsafe {
        let pointer = &raw mut VALUE;

        // store / load
        atomic_store::<u128, { Ordering::SeqCst }>(pointer, 0xDEAD_BEEF_0000_0000_0000_0000_0000_0001);
        if !holds(pointer, 0xDEAD_BEEF_0000_0000_0000_0000_0000_0001) {
            return 1;
        }

        // fetch_add carrying across the 64-bit boundary
        atomic_store::<u128, { Ordering::SeqCst }>(pointer, 0xFFFF_FFFF_FFFF_FFFF);
        atomic_xadd::<u128, u128, { Ordering::SeqCst }>(pointer, 1);
        if !holds(pointer, 0x1_0000_0000_0000_0000) {
            return 2;
        }

        // compare_exchange success, then failure leaves the value unchanged
        atomic_store::<u128, { Ordering::SeqCst }>(pointer, 100);
        let (_, ok) =
            atomic_cxchg::<u128, { Ordering::SeqCst }, { Ordering::SeqCst }>(pointer, 100, 200);
        if !ok {
            return 3;
        }
        let (_, unexpected) =
            atomic_cxchg::<u128, { Ordering::SeqCst }, { Ordering::SeqCst }>(pointer, 999, 300);
        if unexpected {
            return 4;
        }
        if !holds(pointer, 200) {
            return 5;
        }
    }
    0
}
