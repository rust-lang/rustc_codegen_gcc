// Compiler:
//
// Run-time:
//   status: 0
//   stdout: imax 0 0 0
//     imin -1
//     umax 2147483648
//     umin 1
//     ret -5 3

// Reproducer for: unsigned atomic `fetch_max`/`fetch_min` compare with a SIGNED comparison
// (codegen-audit-2026-08.md). All four RMW extremum ops go through `atomic_extremum`
// (src/builder.rs:1754-1765), which compares in the return type of the `__atomic_load_N`
// builtin — a signed type — so `AtomicU32::fetch_max(1, 2^31)` keeps 1 and
// `AtomicU32::fetch_min(u32::MAX, 1)` keeps u32::MAX. The signed variants happen to work.
// cg_gcc currently prints `umax 1` and `umin 4294967295`; this test asserts the correct
// values, so it fails until the bug is fixed.
//
// Only 8/16/32-bit atomics are used so the test also runs on 32-bit targets (m68k CI).

use std::sync::atomic::Ordering::SeqCst;
use std::sync::atomic::{AtomicI16, AtomicI32, AtomicI8, AtomicU32};

fn main() {
    // Signed max sanity: max(-1, 0) == 0.
    let a8 = AtomicI8::new(-1);
    a8.fetch_max(0, SeqCst);
    let a16 = AtomicI16::new(-1);
    a16.fetch_max(0, SeqCst);
    let a32 = AtomicI32::new(-1);
    a32.fetch_max(0, SeqCst);
    println!("imax {} {} {}", a8.load(SeqCst), a16.load(SeqCst), a32.load(SeqCst));

    // Signed min sanity: min(1, -1) == -1.
    let b32 = AtomicI32::new(1);
    b32.fetch_min(-1, SeqCst);
    println!("imin {}", b32.load(SeqCst));

    // Unsigned max: max(1, 2^31) == 2^31. Lost under a signed comparison.
    let c32 = AtomicU32::new(1);
    c32.fetch_max(0x8000_0000, SeqCst);
    println!("umax {}", c32.load(SeqCst));

    // Unsigned min: min(u32::MAX, 1) == 1. Lost under a signed comparison.
    let d32 = AtomicU32::new(u32::MAX);
    d32.fetch_min(1, SeqCst);
    println!("umin {}", d32.load(SeqCst));

    // The return value must be the previous value.
    let e = AtomicI32::new(-5);
    let returned = e.fetch_max(3, SeqCst);
    println!("ret {} {}", returned, e.load(SeqCst));
}
