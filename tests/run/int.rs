// Compiler:
//
// Run-time:
//   status: 0

#![feature(arbitrary_self_types, auto_traits, core_intrinsics, lang_items, start, intrinsics)]

#![no_std]

mod intrinsics {
    extern "rust-intrinsic" {
        pub fn abort() -> !;
    }
}

/*
 * Core
 */

mod libc {
    #[link(name = "c")]
    extern "C" {
        pub fn puts(s: *const u8) -> i32;
    }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    unsafe {
        core::intrinsics::abort();
    }
}

/*
 * Code
 */

#[start]
fn main(argc: isize, _argv: *const *const u8) -> isize {

    let var = 134217856;
    let var2 = 10475372733397991552;
    let var3 = 193236519889708027473620326106273939584;
    /*if argc == 1 {
        unsafe {
            core::intrinsics::abort();
            libc::puts("Hello\0" as *const str as *const u8);
        }
    }*/
    // Shifts.
    assert_eq!(var << argc as u128, 268435712);

    assert_eq!(var >> argc as u128, 67108928);
    assert_eq!(var >> (argc + 32) as u128, 0);
    assert_eq!(var >> (argc + 48) as u128, 0);
    assert_eq!(var >> (argc + 60) as u128, 0);
    assert_eq!(var >> (argc + 62) as u128, 0);

    assert_eq!(var2 >> argc as u128, 5237686366698995776);
    assert_eq!(var2 >> (argc + 32) as u128, 1219493888);
    assert_eq!(var2 >> (argc + 48) as u128, 18608);
    assert_eq!(var2 >> (argc + 60) as u128, 4);
    assert_eq!(var2 >> (argc + 62) as u128, 1);

    assert_eq!(var3 >> argc as u128, 96618259944854013736810163053136969792);
    assert_eq!(var3 >> (argc + 32) as u128, 22495691651677250335181635584);
    assert_eq!(var3 >> (argc + 48) as u128, 343257013727985387194544);
    assert_eq!(var3 >> (argc + 60) as u128, 83802981867183932420);
    assert_eq!(var3 >> (argc + 62) as u128, 20950745466795983105);

    // Casts
    assert_eq!((var >> (argc + 32) as u128) as u64, 0);
    assert_eq!((var >> argc as u128) as u64, 67108928);

    // Addition.
    assert_eq!(var + argc as u128, 134217857);
    //assert_eq!(var + (argc + 32) as u128, );

    assert_eq!(var2 + argc as u128, 10475372733397991553);

    assert_eq!(var3 + argc as u128, 193236519889708027473620326106273939585);
    0
}
