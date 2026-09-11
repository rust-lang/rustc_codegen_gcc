// Compiler:

// GCC won't inline a function that uses va_arg, cycle or not.

#![crate_type = "lib"]

#[inline(always)]
fn helper(n: u32) -> u32 {
    n + 1
}

#[inline(always)]
pub unsafe extern "C" fn variadic(n: u32, mut args: ...) -> u32 {
    helper(n) + unsafe { args.next_arg::<u32>() }
}

pub fn entry(n: u32) -> u32 {
    unsafe { variadic(n, n) }
}
