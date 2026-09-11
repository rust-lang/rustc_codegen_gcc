// Compiler:

// Interrupt handlers are built with general-regs-only, and GCC won't inline normally-built code
// into them.

#![feature(abi_x86_interrupt)]
#![crate_type = "lib"]

static mut STATE: u64 = 0;

#[inline(always)]
fn leaf(x: u64) -> u64 {
    x.wrapping_add(1)
}

#[inline(always)]
fn wrapper(x: u64) -> u64 {
    leaf(x)
}

pub extern "x86-interrupt" fn via_wrapper(_frame: u64) {
    unsafe { STATE = wrapper(STATE) }
}

pub extern "x86-interrupt" fn direct(_frame: u64) {
    unsafe { STATE = leaf(STATE) }
}
