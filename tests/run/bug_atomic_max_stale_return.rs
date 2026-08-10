// Compiler:
//
// Run-time:
//   status: 0
//   stdout: ok

// Reproducer for: atomic `fetch_max`/`fetch_min` return a stale previous value after a CAS
// retry (codegen-audit-2026-08.md). In `atomic_extremum` (src/builder.rs:89-91) the returned
// "previous value" is loaded once before the compare-exchange loop and never updated inside
// it, so whenever the CAS has to retry, the caller receives a value older than the one the
// successful CAS actually replaced.
//
// Detector: every `fetch_max` operand is globally unique (from a ticket counter), so in a
// correct implementation the values returned by *writing* operations (previous < operand)
// are exactly the strictly-increasing state sequence of the target — all distinct. Any
// duplicate means some operation returned a stale snapshot. On this bug the race fires
// reliably (>100k duplicates per run at -O0 and -O3 on x86_64); a correct backend prints
// `ok`. Signed atomics are used because unsigned max/min have a separate signedness bug
// (see bug_atomic_umax_umin.rs), and 32-bit atomics so the test also runs on m68k.

use std::sync::atomic::AtomicI32;
use std::sync::atomic::Ordering::SeqCst;
use std::thread;

static TICKET: AtomicI32 = AtomicI32::new(1);
static TARGET: AtomicI32 = AtomicI32::new(0);

fn main() {
    let threads: Vec<_> = (0..4)
        .map(|_| {
            thread::spawn(|| {
                let mut writes = Vec::new();
                for _ in 0..200_000 {
                    let value = TICKET.fetch_add(1, SeqCst);
                    let previous = TARGET.fetch_max(value, SeqCst);
                    if previous < value {
                        writes.push(previous);
                    }
                }
                writes
            })
        })
        .collect();
    let mut all: Vec<i32> = Vec::new();
    for thread in threads {
        all.extend(thread.join().unwrap());
    }
    all.sort_unstable();
    let duplicates = all.windows(2).filter(|window| window[0] == window[1]).count();
    if duplicates == 0 {
        println!("ok");
    } else {
        println!("BUG: {} duplicate previous-value returns", duplicates);
    }
}
