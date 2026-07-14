// Compiler:
//
// Run-time:
//   status: 0
//   stdout: Caught

// Regression test for a release-mode (-O3) unwinding bug: `catch_unwind` must
// still catch a panic when the panicking closure is inlined across the catch
// boundary. The `#[inline]` `call_once` below forces that inlining.
//
// Previously, GCC inlined the out-of-line `__rust_try` shim into its caller
// under optimization, which degraded the try/catch landing pad into a plain
// `_Unwind_Resume`. The panic was then re-raised instead of caught, escaped
// `main`, and the process exited with code 101 (in release only; debug and the
// LLVM backend were unaffected). See `get_rust_try_fn` in `src/intrinsic/mod.rs`,
// which now marks `__rust_try` as `NoInline`.

#![feature(fn_traits, unboxed_closures)]

struct Wrapper<A>(A);

impl<R, F: FnOnce() -> R> FnOnce<()> for Wrapper<F> {
    type Output = R;

    #[inline]
    extern "rust-call" fn call_once(self, _args: ()) -> R {
        (self.0)()
    }
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let result = std::panic::catch_unwind(Wrapper(|| panic!()));
    assert!(result.is_err());
    println!("Caught");
}
