//@ only-x86_64
//@ assembly-output: emit-asm
//@ compile-flags: --crate-type staticlib -Ccodegen-units=1

// Reproducer for: constants are 8x over-aligned on a const-cache hit
// (codegen-audit-2026-08.md; related: rust-lang/rustc_codegen_gcc#714). In
// `static_addr_of_mut`'s cache-hit path (src/consts.rs), the alignment is compared and set
// using `align.bits()` where the libgccjit API takes BYTES (the fresh-creation path
// correctly uses `align.bytes()`). The two functions below promote the same `&42`
// allocation; the second request hits the cache and the shared 4-byte constant gets
// `.align 32` instead of `.align 4`, wasting rodata for every deduplicated constant.
// `-Ccodegen-units=1` keeps both functions in one codegen unit so the cache hit happens.

#[no_mangle]
pub fn first() -> &'static u32 {
    &42
}

#[no_mangle]
pub fn second() -> &'static u32 {
    &42
}

// The promoted constant is the only `.long 42` in the file; nothing before it may align
// to 32 bytes. Today cg_gcc emits `.align 32` right above it.
// CHECK-NOT: .align 32
// CHECK: .long 42
