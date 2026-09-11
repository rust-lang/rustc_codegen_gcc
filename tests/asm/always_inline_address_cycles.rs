//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=1

#![crate_type = "lib"]
#![no_std]

// From -O1, GCC folds loads from read-only data, so calling through a static table or a vtable
// becomes a direct call, which closes the cycle.

static TABLE: [fn(u32) -> u32; 1] = [via_table];

#[inline(always)]
fn via_table(n: u32) -> u32 {
    table_caller(n)
}

#[inline(always)]
fn table_caller(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    TABLE[0](n - 1) + 1
}

trait Step {
    fn step(&self, n: u32) -> u32;
}

struct S;

impl Step for S {
    #[inline(always)]
    fn step(&self, n: u32) -> u32 {
        dyn_caller(n)
    }
}

#[inline(always)]
fn dyn_caller(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    let step: &dyn Step = &S;
    step.step(n - 1) + 1
}

// CHECK-LABEL: {{^"?_?}}entry{{"?}}:
// CHECK: ret
#[no_mangle]
pub fn entry(n: u32) -> u32 {
    via_table(n) + dyn_caller(n)
}
