// Compiler:
//   status: error
//   stderr:
//     error: the GCC backend requires the first argument of an `x86-interrupt` function to be a pointer
//     ...

// Test that an `x86-interrupt` function whose first argument is not a pointer emits a
// clean error instead of an internal libgccjit error (issue #833).

#![feature(abi_x86_interrupt)]

pub extern "x86-interrupt" fn f(_a: i64) {}

fn main() {
    // Take the function's address so that it is codegened.
    let _f: extern "x86-interrupt" fn(i64) = f;
}
