//! Lock-free inline codegen for atomics that GCC would otherwise lower to a
//! `libatomic` libcall (`__atomic_load_16`, `__atomic_load_8` on a 32-bit target,
//! …).
//!
//! GCC always turns the 16-byte `__atomic_*` builtins into libcalls (even with
//! `-mcx16`), and turns any `__atomic_*_N` wider than the target can do inline
//! into a libcall too. rustc does not link `libatomic`, so those become
//! `undefined reference` errors. cg_llvm instead inlines a lock-free sequence;
//! this module makes cg_gcc do the same, using one of two primitives:
//!
//! * **x86-64 `cmpxchg16b`** (hand-written inline asm) for 128-bit atomics when
//!   the `cmpxchg16b` target feature is available. This is independent of whether
//!   GCC itself was told about `-mcx16`.
//! * **the legacy `__sync_*_N` builtins** for every other not-lock-free size/arch
//!   (aarch64 128-bit, `__atomic_load_8` on a 32-bit target, …). Unlike
//!   `__atomic_*_N`, GCC inlines these to a lock-free sequence wherever the target
//!   supports it (and libcalls — exactly as today — where it genuinely cannot).
//!
//! Every operation (load / store / exchange / all RMW) is expressed as a
//! gccjit-level compare-and-swap loop over a single primitive, mirroring
//! [`Builder::atomic_extremum`], so there is very little hand-written assembly.
//!
//! Ordering note: `cmpxchg16b` and the full-barrier `__sync_*` builtins are all
//! sequentially consistent, so the requested [`AtomicOrdering`] is (soundly)
//! strengthened to SeqCst on these paths. Precise per-ordering instruction
//! selection on aarch64 (`ldaxp`/`stlxp`, `casp{a,l,al}`) is a possible follow-up.
//!
//! When no inline sequence applies, the entry points return `None`/`false` and the
//! caller falls back to the existing `__atomic_*_N` path (matching cg_llvm, e.g.
//! x86-64 without `cmpxchg16b`).

use gccjit::{BinaryOp, ComparisonOp, RValue, ToRValue, Type, UnaryOp};
use rustc_abi::Size;
use rustc_codegen_ssa::common::AtomicRmwBinOp;
use rustc_codegen_ssa::traits::BuilderMethods;
use rustc_middle::ty::AtomicOrdering;
use rustc_target::spec::Arch;

use crate::builder::Builder;

/// Which lock-free compare-and-swap primitive to use for an operation.
#[derive(Clone, Copy)]
enum Primitive {
    /// x86-64 `lock cmpxchg16b` (128-bit only). Always a full barrier.
    Cmpxchg16b,
    /// aarch64 load/store-exclusive pair (`ld[a]xp`/`st[l]xp`), 128-bit only. The
    /// acquire/release variants are selected from [`AtomicCtx::order`].
    LdxpStxp,
    /// aarch64 FEAT_LSE single-instruction 128-bit CAS (`casp{,a,l,al}`).
    LseCasp,
    /// `__sync_val_compare_and_swap_N`, inlined lock-free by GCC where supported.
    /// Always a full barrier.
    Sync,
}

/// Everything a 128-bit-or-oversized atomic operation needs, decided once up front.
#[derive(Clone, Copy)]
struct AtomicCtx<'gcc> {
    primitive: Primitive,
    /// Unsigned integer type of the access size (the working type).
    int_type: Type<'gcc>,
    /// Signed integer type of the access size (for signed min/max).
    signed_type: Type<'gcc>,
    /// Memory ordering of the operation (only the `LdxpStxp` primitive varies with
    /// it; `Cmpxchg16b`/`Sync` are always sequentially consistent).
    order: AtomicOrdering,
    size: Size,
}

/// Whether GCC would lower `__atomic_*_N` for this size into a `libatomic` libcall
/// on the current target, i.e. the size is not natively lock-free.
///
/// - 16 bytes is always a libcall (GCC never inlines `__atomic_*_16`, on any arch,
///   even where `max_atomic_width` reports 128, such as aarch64).
/// - otherwise, any size wider than `max_atomic_width` is a libcall (e.g. 64-bit on
///   a 32-bit target without a 64-bit CAS).
fn is_libatomic_size(bx: &Builder<'_, '_, '_>, size: Size) -> bool {
    size.bytes() == 16 || size.bits() > bx.cx.sess().target.max_atomic_width()
}

/// Decide how (if at all) to inline an atomic of this size lock-free, or `None` to
/// leave it on the default `__atomic_*_N` path.
fn atomic_ctx<'gcc>(
    bx: &Builder<'_, 'gcc, '_>,
    size: Size,
    order: AtomicOrdering,
) -> Option<AtomicCtx<'gcc>> {
    if !is_libatomic_size(bx, size) {
        return None;
    }
    let arch = &bx.cx.sess().target.arch;
    if size.bytes() == 16 {
        match arch {
            // The only x86-64 128-bit option is `cmpxchg16b`; without it, defer to
            // the default `__atomic_*_16` libcall (matching cg_llvm). Never use
            // `__sync` here, since that could emit `cmpxchg16b` where it isn't
            // guaranteed available.
            Arch::X86_64 => {
                return bx.cx.has_cx16.then(|| AtomicCtx {
                    primitive: Primitive::Cmpxchg16b,
                    int_type: bx.cx.u128_type,
                    signed_type: bx.cx.i128_type,
                    order,
                    size,
                });
            }
            // aarch64: FEAT_LSE gives a single-instruction CAS (`casp`); otherwise
            // the load/store-exclusive pair, always present since ARMv8.0.
            Arch::AArch64 => {
                let primitive =
                    if bx.cx.has_lse { Primitive::LseCasp } else { Primitive::LdxpStxp };
                return Some(AtomicCtx {
                    primitive,
                    int_type: bx.cx.u128_type,
                    signed_type: bx.cx.i128_type,
                    order,
                    size,
                });
            }
            _ => {}
        }
    }
    // Everything else that would libcall: let GCC inline `__sync_*_N` where it can.
    Some(AtomicCtx {
        primitive: Primitive::Sync,
        int_type: bx.context.new_int_type(size.bytes() as i32, false),
        signed_type: bx.context.new_int_type(size.bytes() as i32, true),
        order,
        size,
    })
}

// -- u128 <-> (u64, u64) helpers (for the `cmpxchg16b` primitive) -----------------

fn low_half<'gcc>(bx: &Builder<'_, 'gcc, '_>, value: RValue<'gcc>) -> RValue<'gcc> {
    bx.context.new_cast(bx.location, value, bx.cx.u64_type)
}

fn high_half<'gcc>(bx: &Builder<'_, 'gcc, '_>, value: RValue<'gcc>) -> RValue<'gcc> {
    let shift = bx.context.new_rvalue_from_int(bx.cx.u128_type, 64);
    let shifted =
        bx.context.new_binary_op(bx.location, BinaryOp::RShift, bx.cx.u128_type, value, shift);
    bx.context.new_cast(bx.location, shifted, bx.cx.u64_type)
}

fn join_halves<'gcc>(
    bx: &Builder<'_, 'gcc, '_>,
    low: RValue<'gcc>,
    high: RValue<'gcc>,
) -> RValue<'gcc> {
    let low = bx.context.new_cast(bx.location, low, bx.cx.u128_type);
    let high = bx.context.new_cast(bx.location, high, bx.cx.u128_type);
    let shift = bx.context.new_rvalue_from_int(bx.cx.u128_type, 64);
    let high = bx.context.new_binary_op(bx.location, BinaryOp::LShift, bx.cx.u128_type, high, shift);
    bx.context.new_binary_op(bx.location, BinaryOp::BitwiseOr, bx.cx.u128_type, high, low)
}

// -- Primitives -----------------------------------------------------------------

/// x86-64 `lock cmpxchg16b`: a full-barrier 128-bit compare-and-swap.
///
/// Returns `(old_value, success)`, `old_value` being the value read (equal to
/// `expected` on success) and `success` a `bool` taken from the zero flag.
fn cmpxchg16b<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ptr: RValue<'gcc>,
    expected: RValue<'gcc>,
    desired: RValue<'gcc>,
) -> (RValue<'gcc>, RValue<'gcc>) {
    let func = bx.current_func();

    // RDX:RAX hold `expected` on input and the read value on output.
    let rax = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let rdx = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let expected_low = low_half(bx, expected);
    let expected_high = high_half(bx, expected);
    bx.llbb().add_assignment(bx.location, rax, expected_low);
    bx.llbb().add_assignment(bx.location, rdx, expected_high);

    // RCX:RBX hold `desired`.
    let desired_low = low_half(bx, desired);
    let desired_high = high_half(bx, desired);

    let success = bx.new_temp(func, bx.location, bx.cx.bool_type);

    // The 16-byte memory operand.
    let u128_ptr_type = bx.cx.u128_type.make_pointer();
    let mem = bx.context.new_cast(bx.location, ptr, u128_ptr_type).dereference(bx.location);

    // Operand order (`%N`): 0:+a 1:+d 2:=@ccz 3:+m | 4:b 5:c. Only the memory
    // operand is referenced; the rest are pinned to their registers by constraints.
    let asm = bx.llbb().add_extended_asm(bx.location, "lock cmpxchg16b %3");
    asm.add_output_operand(None, "+a", rax);
    asm.add_output_operand(None, "+d", rdx);
    asm.add_output_operand(None, "=@ccz", success);
    asm.add_output_operand(None, "+m", mem);
    asm.add_input_operand(None, "b", desired_low);
    asm.add_input_operand(None, "c", desired_high);
    asm.add_clobber("cc");
    asm.add_clobber("memory");
    asm.set_volatile_flag(true);

    let old = join_halves(bx, rax.to_rvalue(), rdx.to_rvalue());
    (old, success.to_rvalue())
}

/// aarch64 128-bit compare-and-swap via a load/store-exclusive retry loop.
///
/// Returns `(old_value, success)`. The exclusive pair is retried internally on
/// spurious `stxp` failure, so `success` is a true CAS result (value matched), not a
/// store-exclusive status. The acquire/release instruction variant is chosen from
/// `ctx.order`, so this honours the requested [`AtomicOrdering`]:
///
/// | order        | load    | store   |
/// |--------------|---------|---------|
/// | Relaxed      | `ldxp`  | `stxp`  |
/// | Acquire      | `ldaxp` | `stxp`  |
/// | Release      | `ldxp`  | `stlxp` |
/// | AcqRel/SeqCst| `ldaxp` | `stlxp` |
fn ldxp_stxp_cmpxchg<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ctx: AtomicCtx<'gcc>,
    ptr: RValue<'gcc>,
    expected: RValue<'gcc>,
    desired: RValue<'gcc>,
) -> (RValue<'gcc>, RValue<'gcc>) {
    let func = bx.current_func();

    let load = match ctx.order {
        AtomicOrdering::Acquire | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => "ldaxp",
        AtomicOrdering::Relaxed | AtomicOrdering::Release => "ldxp",
    };
    let store = match ctx.order {
        AtomicOrdering::Release | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => "stlxp",
        AtomicOrdering::Relaxed | AtomicOrdering::Acquire => "stxp",
    };

    let expected_low = low_half(bx, expected);
    let expected_high = high_half(bx, expected);
    let desired_low = low_half(bx, desired);
    let desired_high = high_half(bx, desired);

    let old_low = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let old_high = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let success = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let status = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let address = bx.context.new_cast(bx.location, ptr, bx.cx.u128_type.make_pointer());

    // Operand `%N`: 0:old_low 1:old_high 2:success 3:status(scratch) |
    // 4:address 5:exp_low 6:exp_high 7:new_low 8:new_high.
    // `%wN` selects the 32-bit W view (for the store-exclusive status register).
    let template = format!(
        "1:\n\t\
         {load} %0, %1, [%4]\n\t\
         cmp %0, %5\n\t\
         ccmp %1, %6, #0, eq\n\t\
         b.ne 2f\n\t\
         {store} %w3, %7, %8, [%4]\n\t\
         cbnz %w3, 1b\n\t\
         mov %w2, #1\n\t\
         b 3f\n\t\
         2:\n\t\
         clrex\n\t\
         mov %w2, #0\n\t\
         3:"
    );
    let asm = bx.llbb().add_extended_asm(bx.location, &template);
    asm.add_output_operand(None, "=&r", old_low);
    asm.add_output_operand(None, "=&r", old_high);
    asm.add_output_operand(None, "=&r", success);
    asm.add_output_operand(None, "=&r", status);
    asm.add_input_operand(None, "r", address);
    asm.add_input_operand(None, "r", expected_low);
    asm.add_input_operand(None, "r", expected_high);
    asm.add_input_operand(None, "r", desired_low);
    asm.add_input_operand(None, "r", desired_high);
    asm.add_clobber("cc");
    asm.add_clobber("memory");
    asm.set_volatile_flag(true);

    let old = join_halves(bx, old_low.to_rvalue(), old_high.to_rvalue());
    let zero = bx.context.new_rvalue_zero(bx.cx.u64_type);
    let success =
        bx.context.new_comparison(bx.location, ComparisonOp::NotEquals, success.to_rvalue(), zero);
    (old, success)
}

/// aarch64 FEAT_LSE single-instruction 128-bit CAS via `casp`.
///
/// `casp` needs the expected/old value in an even:odd register pair and the desired
/// value in another; we pin them to x0:x1 and x2:x3 (like the kernel does), which is
/// the standard way to express the pair requirement in inline asm. The ordering
/// suffix (`casp`/`caspa`/`caspl`/`caspal`) is chosen from `ctx.order`.
fn casp_cmpxchg<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ctx: AtomicCtx<'gcc>,
    ptr: RValue<'gcc>,
    expected: RValue<'gcc>,
    desired: RValue<'gcc>,
) -> (RValue<'gcc>, RValue<'gcc>) {
    let func = bx.current_func();
    let variant = match ctx.order {
        AtomicOrdering::Relaxed => "casp",
        AtomicOrdering::Acquire => "caspa",
        AtomicOrdering::Release => "caspl",
        AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => "caspal",
    };

    let expected_low = assign_temp(bx, low_half(bx, expected));
    let expected_high = assign_temp(bx, high_half(bx, expected));

    // x0:x1 = expected on input, old on output; x2:x3 = desired.
    let register = |bx: &mut Builder<'_, 'gcc, '_>, name, value| {
        let local = func.new_local(bx.location, bx.cx.u64_type, name);
        local.set_register_name(name);
        bx.llbb().add_assignment(bx.location, local, value);
        local
    };
    let x0 = register(bx, "x0", expected_low);
    let x1 = register(bx, "x1", expected_high);
    let x2 = register(bx, "x2", low_half(bx, desired));
    let x3 = register(bx, "x3", high_half(bx, desired));
    let address = bx.context.new_cast(bx.location, ptr, bx.cx.u128_type.make_pointer());

    let asm = bx.llbb().add_extended_asm(bx.location, &format!("{variant} %0, %1, %2, %3, [%4]"));
    asm.add_output_operand(None, "+r", x0);
    asm.add_output_operand(None, "+r", x1);
    asm.add_input_operand(None, "r", x2.to_rvalue());
    asm.add_input_operand(None, "r", x3.to_rvalue());
    asm.add_input_operand(None, "r", address);
    asm.add_clobber("memory");
    asm.set_volatile_flag(true);

    let old = join_halves(bx, x0.to_rvalue(), x1.to_rvalue());
    let low_equal =
        bx.context.new_comparison(bx.location, ComparisonOp::Equals, x0.to_rvalue(), expected_low);
    let high_equal =
        bx.context.new_comparison(bx.location, ComparisonOp::Equals, x1.to_rvalue(), expected_high);
    let success = bx.context.new_binary_op(
        bx.location,
        BinaryOp::LogicalAnd,
        bx.cx.bool_type,
        low_equal,
        high_equal,
    );
    (old, success)
}

/// aarch64 FEAT_LSE2 single-copy-atomic 128-bit load via `ldp` (no write-back,
/// unlike the exclusive/CAS load). A trailing barrier provides acquire/seq-cst.
fn ldp_load<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ptr: RValue<'gcc>,
    order: AtomicOrdering,
) -> RValue<'gcc> {
    let func = bx.current_func();
    let low = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let high = bx.new_temp(func, bx.location, bx.cx.u64_type);
    let address = bx.context.new_cast(bx.location, ptr, bx.cx.u128_type.make_pointer());
    let barrier = match order {
        AtomicOrdering::Acquire | AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => "\n\tdmb ish",
        _ => "",
    };
    let asm = bx.llbb().add_extended_asm(bx.location, &format!("ldp %0, %1, [%2]{barrier}"));
    asm.add_output_operand(None, "=r", low);
    asm.add_output_operand(None, "=r", high);
    asm.add_input_operand(None, "r", address);
    asm.add_clobber("memory");
    asm.set_volatile_flag(true);
    join_halves(bx, low.to_rvalue(), high.to_rvalue())
}

/// aarch64 FEAT_LSE2 single-copy-atomic 128-bit store via `stp`, with barriers for
/// release/seq-cst ordering.
fn stp_store<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    value: RValue<'gcc>,
    ptr: RValue<'gcc>,
    order: AtomicOrdering,
) {
    let low = assign_temp(bx, low_half(bx, value));
    let high = assign_temp(bx, high_half(bx, value));
    let address = bx.context.new_cast(bx.location, ptr, bx.cx.u128_type.make_pointer());
    let (pre, post) = match order {
        AtomicOrdering::Release => ("dmb ish\n\t", ""),
        AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => ("dmb ish\n\t", "\n\tdmb ish"),
        _ => ("", ""),
    };
    let asm = bx.llbb().add_extended_asm(bx.location, &format!("{pre}stp %0, %1, [%2]{post}"));
    asm.add_input_operand(None, "r", low);
    asm.add_input_operand(None, "r", high);
    asm.add_input_operand(None, "r", address);
    asm.add_clobber("memory");
    asm.set_volatile_flag(true);
}

/// Whether a non-writing FEAT_LSE2 `ldp`/`stp` load/store applies to this context.
fn use_lse2(bx: &Builder<'_, '_, '_>, ctx: AtomicCtx<'_>) -> bool {
    bx.cx.has_lse2 && matches!(ctx.primitive, Primitive::LdxpStxp | Primitive::LseCasp)
}

/// Assign an rvalue to a fresh temporary and return the temporary's rvalue, so the
/// value is computed once (gccjit rvalues are expressions).
fn assign_temp<'gcc>(bx: &mut Builder<'_, 'gcc, '_>, value: RValue<'gcc>) -> RValue<'gcc> {
    let temp = bx.new_temp(bx.current_func(), bx.location, value.get_type());
    bx.llbb().add_assignment(bx.location, temp, value);
    temp.to_rvalue()
}

/// `__sync_val_compare_and_swap_N`: GCC inlines a lock-free full-barrier CAS where
/// the target supports it. Success is derived as `old == expected`, which is the
/// correct compare-exchange semantics.
fn sync_cmpxchg<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ctx: AtomicCtx<'gcc>,
    ptr: RValue<'gcc>,
    expected: RValue<'gcc>,
    desired: RValue<'gcc>,
) -> (RValue<'gcc>, RValue<'gcc>) {
    let func =
        bx.context.get_builtin_function(format!("__sync_val_compare_and_swap_{}", ctx.size.bytes()));
    // Match the builtin's own parameter types: arg 0 is `volatile void *`, args 1/2
    // are the value type. (Mirrors the `__atomic_*` handling in `builder.rs`.)
    let ptr_type = func.get_param(0).to_rvalue().get_type();
    let value_type = func.get_param(1).to_rvalue().get_type();
    let ptr = bx.context.new_cast(bx.location, ptr, ptr_type);
    let expected_arg = bx.context.new_bitcast(bx.location, expected, value_type);
    let desired_arg = bx.context.new_bitcast(bx.location, desired, value_type);
    let call = bx.context.new_call(bx.location, func, &[ptr, expected_arg, desired_arg]);
    // Bind the call to a variable: a gccjit rvalue is an expression, so using the
    // call in more than one place (the returned old value *and* the success
    // comparison) would execute the CAS more than once.
    let old = bx.new_temp(bx.current_func(), bx.location, ctx.int_type);
    bx.llbb().add_assignment(bx.location, old, bx.context.new_bitcast(bx.location, call, ctx.int_type));
    let old = old.to_rvalue();
    let success = bx.context.new_comparison(bx.location, ComparisonOp::Equals, old, expected);
    (old, success)
}

/// A single compare-and-swap using the context's primitive.
fn cmpxchg<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ctx: AtomicCtx<'gcc>,
    ptr: RValue<'gcc>,
    expected: RValue<'gcc>,
    desired: RValue<'gcc>,
) -> (RValue<'gcc>, RValue<'gcc>) {
    match ctx.primitive {
        Primitive::Cmpxchg16b => cmpxchg16b(bx, ptr, expected, desired),
        Primitive::LdxpStxp => ldxp_stxp_cmpxchg(bx, ctx, ptr, expected, desired),
        Primitive::LseCasp => casp_cmpxchg(bx, ctx, ptr, expected, desired),
        Primitive::Sync => sync_cmpxchg(bx, ctx, ptr, expected, desired),
    }
}

/// Run `compute(old) -> new` in a CAS retry loop and return the value replaced.
/// Mirrors [`Builder::atomic_extremum`]'s block structure.
fn cmpxchg_loop<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ctx: AtomicCtx<'gcc>,
    ptr: RValue<'gcc>,
    compute: impl Fn(&mut Builder<'_, 'gcc, '_>, RValue<'gcc>) -> RValue<'gcc>,
) -> RValue<'gcc> {
    let func = bx.current_func();
    let zero = bx.context.new_rvalue_zero(ctx.int_type);

    // Seed `current` with an actual read (a CAS of 0 with 0).
    let (initial, _) = cmpxchg(bx, ctx, ptr, zero, zero);
    let current = func.new_local(bx.location, ctx.int_type, "atomic_current");
    bx.llbb().add_assignment(bx.location, current, initial);

    let loop_block = func.new_block("atomic_cas");
    let after_block = func.new_block("atomic_after");
    bx.llbb().end_with_jump(bx.location, loop_block);
    bx.switch_to_block(loop_block);

    let new_value = compute(bx, current.to_rvalue());
    let (actual, success) = cmpxchg(bx, ctx, ptr, current.to_rvalue(), new_value);
    bx.llbb().add_assignment(bx.location, current, actual);
    let retry =
        bx.context.new_unary_op(bx.location, UnaryOp::LogicalNegate, bx.cx.bool_type, success);
    bx.llbb().end_with_conditional(bx.location, retry, loop_block, after_block);

    bx.switch_to_block(after_block);
    current.to_rvalue()
}

// -- Entry points ----------------------------------------------------------------

pub fn atomic_load<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    ty: Type<'gcc>,
    ptr: RValue<'gcc>,
    order: AtomicOrdering,
    size: Size,
) -> Option<RValue<'gcc>> {
    let ctx = atomic_ctx(bx, size, order)?;
    // FEAT_LSE2: a genuine non-writing atomic load via `ldp`.
    if use_lse2(bx, ctx) {
        return Some(bx.context.new_bitcast(bx.location, ldp_load(bx, ptr, order), ty));
    }
    // Otherwise a load is a CAS of 0 with 0: it returns the current value, and only
    // writes (the same 0) when the value already is 0. Requires writable memory,
    // exactly as cg_llvm's inlined load does.
    let zero = bx.context.new_rvalue_zero(ctx.int_type);
    let (value, _) = cmpxchg(bx, ctx, ptr, zero, zero);
    Some(bx.context.new_bitcast(bx.location, value, ty))
}

pub fn atomic_store<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    value: RValue<'gcc>,
    ptr: RValue<'gcc>,
    order: AtomicOrdering,
    size: Size,
) -> bool {
    let Some(ctx) = atomic_ctx(bx, size, order) else {
        return false;
    };
    let value = bx.context.new_bitcast(bx.location, value, ctx.int_type);
    // FEAT_LSE2: a direct atomic store via `stp` instead of a CAS loop.
    if use_lse2(bx, ctx) {
        stp_store(bx, value, ptr, order);
        return true;
    }
    cmpxchg_loop(bx, ctx, ptr, move |_bx, _old| value);
    true
}

pub fn atomic_cmpxchg<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    dst: RValue<'gcc>,
    cmp: RValue<'gcc>,
    src: RValue<'gcc>,
    order: AtomicOrdering,
    failure_order: AtomicOrdering,
    _weak: bool,
    size: Size,
) -> Option<(RValue<'gcc>, RValue<'gcc>)> {
    // Use the stronger of the two orderings for the single CAS (GCC/aarch64 has no
    // way to use a failure ordering stronger than the success ordering anyway).
    let order = if failure_order as i32 > order as i32 { failure_order } else { order };
    let ctx = atomic_ctx(bx, size, order)?;
    let cmp_type = cmp.get_type();
    let expected = bx.context.new_bitcast(bx.location, cmp, ctx.int_type);
    let desired = bx.context.new_bitcast(bx.location, src, ctx.int_type);
    // A single strong CAS (no spurious failure), a valid impl of weak and strong.
    let (old, success) = cmpxchg(bx, ctx, dst, expected, desired);
    let old = bx.context.new_bitcast(bx.location, old, cmp_type);
    Some((old, success))
}

pub fn atomic_rmw<'gcc>(
    bx: &mut Builder<'_, 'gcc, '_>,
    op: AtomicRmwBinOp,
    dst: RValue<'gcc>,
    src: RValue<'gcc>,
    order: AtomicOrdering,
    size: Size,
) -> Option<RValue<'gcc>> {
    let ctx = atomic_ctx(bx, size, order)?;
    let src_type = src.get_type();
    let operand = bx.context.new_bitcast(bx.location, src, ctx.int_type);
    let old = cmpxchg_loop(bx, ctx, dst, move |bx, old| {
        let int_type = ctx.int_type;
        match op {
            AtomicRmwBinOp::AtomicXchg => operand,
            AtomicRmwBinOp::AtomicAdd => {
                bx.context.new_binary_op(bx.location, BinaryOp::Plus, int_type, old, operand)
            }
            AtomicRmwBinOp::AtomicSub => {
                bx.context.new_binary_op(bx.location, BinaryOp::Minus, int_type, old, operand)
            }
            AtomicRmwBinOp::AtomicAnd => {
                bx.context.new_binary_op(bx.location, BinaryOp::BitwiseAnd, int_type, old, operand)
            }
            AtomicRmwBinOp::AtomicOr => {
                bx.context.new_binary_op(bx.location, BinaryOp::BitwiseOr, int_type, old, operand)
            }
            AtomicRmwBinOp::AtomicXor => {
                bx.context.new_binary_op(bx.location, BinaryOp::BitwiseXor, int_type, old, operand)
            }
            AtomicRmwBinOp::AtomicNand => {
                let and = bx
                    .context
                    .new_binary_op(bx.location, BinaryOp::BitwiseAnd, int_type, old, operand);
                bx.context.new_unary_op(bx.location, UnaryOp::BitwiseNegate, int_type, and)
            }
            AtomicRmwBinOp::AtomicMax
            | AtomicRmwBinOp::AtomicMin
            | AtomicRmwBinOp::AtomicUMax
            | AtomicRmwBinOp::AtomicUMin => {
                let (compare_type, comparison) = match op {
                    AtomicRmwBinOp::AtomicMax => (ctx.signed_type, ComparisonOp::GreaterThan),
                    AtomicRmwBinOp::AtomicMin => (ctx.signed_type, ComparisonOp::LessThan),
                    AtomicRmwBinOp::AtomicUMax => (int_type, ComparisonOp::GreaterThan),
                    _ => (int_type, ComparisonOp::LessThan),
                };
                let old_cmp = bx.context.new_bitcast(bx.location, old, compare_type);
                let operand_cmp = bx.context.new_bitcast(bx.location, operand, compare_type);
                let keep_old =
                    bx.context.new_comparison(bx.location, comparison, old_cmp, operand_cmp);
                // Branchless select `keep_old ? old : operand`, computed as
                // `operand + (old - operand) * keep_old` (keep_old is 0 or 1).
                let cond = bx.context.new_cast(bx.location, keep_old, int_type);
                let diff =
                    bx.context.new_binary_op(bx.location, BinaryOp::Minus, int_type, old, operand);
                let scaled =
                    bx.context.new_binary_op(bx.location, BinaryOp::Mult, int_type, diff, cond);
                bx.context.new_binary_op(bx.location, BinaryOp::Plus, int_type, operand, scaled)
            }
        }
    });
    Some(bx.context.new_bitcast(bx.location, old, src_type))
}
