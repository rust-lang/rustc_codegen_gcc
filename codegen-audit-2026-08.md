# rustc_codegen_gcc correctness & codegen-quality audit — August 2026

- **Audited commit:** 66e76371ce4 ("Merge pull request #954"), `master` cargo feature enabled.
- **Target:** x86_64-unknown-linux-gnu (native `__int128`, `-fwrapv` set globally).
- **GCC / libgccjit:** 17.0.0 experimental 20260713, install at `/home/bouanto/tests/gcc/gcc-build/install/lib/`.
- **Toolchain:** nightly-2026-08-04 (rustc 1.99.0-nightly 504869653), sysroot `build/build_sysroot/sysroot`.
- **Reference:** every runtime claim was diffed against the same program compiled by the stock
  LLVM rustc of the same nightly, at cg_gcc `-O0` (plus the CI sanitizer config where noted) and
  `-Copt-level=3 -Clto=no`.

Every confirmed bug has a reproducer test in this repository. As agreed, the tests are
**ungated**: they assert the *correct* behavior, fail today, and pass once the bug is fixed.

> **Warning about the failing tests and CI:** the lang-test binary runs its three suites in
> order (compile → debug run → release run) and **exits at the end of the first suite that has
> a failure**. With the `bug_*` compile tests red, `./y.sh test --cargo-tests` therefore stops
> after the compile suite and does not run the debug/release run suites at all. Until the ICE
> bugs are fixed (or the tests are gated), run-suite coverage must be obtained with filters,
> e.g. `cargo test structs`. All pre-existing tests were verified still green through such
> filtered runs; each `bug_*` test was verified to fail with exactly its documented mismatch.

Run a single test with `./y.sh test --cargo-tests -- <substring>`; asm tests with
`./y.sh test --gcc-asm-tests -- bug`.

---

## 1. Executive summary

Silent miscompilations (wrong results at runtime, no diagnostic):

| # | Title | Root cause | Reproducer | Existing issue |
|---|-------|-----------|------------|----------------|
| 1 | Unsigned atomic `fetch_max`/`fetch_min` use a signed comparison | src/builder.rs:1754-1765 → `atomic_extremum` (69-135) | tests/run/bug_atomic_umax_umin.rs | – (may explain part of #821) |
| 2 | Atomic `fetch_max`/`fetch_min` return a stale previous value after a CAS retry | src/builder.rs:89-91 | tests/run/bug_atomic_max_stale_return.rs | – (may explain part of #821) |
| 3 | `compare_exchange(Release, Acquire)` drops the Release ordering | src/builder.rs:1726 | tests/compile/bug_cmpxchg_release_acquire.rs (GIMPLE test) | – |
| 4 | `simd_as` float→int does not saturate | src/intrinsic/simd.rs:659-711 | tests/run/bug_simd_as_sat.rs | – |
| 5 | `simd_gather` dereferences masked-off lanes (SIGSEGV) | src/intrinsic/simd.rs:919-964 | tests/run/bug_simd_gather_mask.rs | **#640** |
| 6 | `simd_scatter` reads *and* writes masked-off lanes (SIGSEGV) | src/intrinsic/simd.rs:1189-1211 | tests/run/bug_simd_scatter_mask.rs | **#640** |
| 7 | Signed `simd_saturating_sub` wrong when rhs contains `T::MIN` | src/intrinsic/simd.rs:1310-1342 | tests/run/bug_simd_saturating_sub.rs | – |
| 8 | `is_val_statically_known` is inverted | src/intrinsic/mod.rs:320-325 | tests/run/bug_is_val_statically_known.rs | – |
| 9 | `f16::mul_add` double-rounded (fmaf16 via f32 `fmaf`) | src/intrinsic/mod.rs:156-179 | tests/run/bug_fma_f16.rs | related: #825 |
| 10 | `unaligned_volatile_load` ignores alignment (SIGSEGV at -O3) | src/builder.rs:1048 | tests/run/bug_unaligned_volatile_load.rs | – |
| 11 | Inline-asm register clobber silently lost when the register is also an input | src/asm.rs:205-217 | tests/run/bug_asm_clobber_lost.rs | **#77** (answers it: no) |
| 12 | Inline-asm `sym` operands spliced in declaration order, not template order | src/asm.rs:418-423 vs 520-522 | tests/run/bug_asm_sym_order.rs | – (cf. old #157) |
| 13 | `#[linkage = "weak"]` emits a GLOBAL symbol instead of WEAK | src/base.rs:63 (+ static path in declare.rs) | tests/run/bug_linkage_weak.rs (+ tests/c/bug_linkage_weak.c, tests/asm/bug_weak_linkage.rs) | – |
| 14 | `ArgAbi::store` PassMode::Cast memcpy reads out of bounds; **breaks the build at -O0** | src/intrinsic/mod.rs:782-799 | tests/run/bug_abi_cast_align16.rs | – |

ICEs / valid code rejected:

| # | Title | Root cause | Reproducer | Existing issue |
|---|-------|-----------|------------|----------------|
| 15 | Any non-power-of-two SIMD lane count ICEs | src/type_of.rs:76 | tests/compile/bug_simd_nonpow2_lanes.rs | – |
| 16 | `simd_arith_offset` unimplemented (breaks `std::simd` pointer math) | src/intrinsic/simd.rs:1677 | tests/compile/bug_simd_arith_offset.rs | – |
| 17 | `breakpoint` intrinsic ICEs | src/intrinsic/mod.rs:337 | tests/compile/bug_breakpoint.rs | – |
| 18 | `prefetch_*` intrinsics ICE | src/intrinsic/mod.rs:360 | tests/compile/bug_prefetch.rs | **#414** |
| 19 | `sym` operand referenced twice in a template ICEs | src/asm.rs:522 | tests/compile/bug_asm_sym_dup.rs | – |
| 20 | `global_asm!` comment stripping corrupts `//` inside string literals | src/asm.rs:956-968 | tests/compile/bug_global_asm_string.rs | – |
| 21 | `#[linkage]` weak_odr / linkonce / linkonce_odr / common ICE | src/base.rs:61-67 | tests/compile/bug_linkage_weak_odr.rs | – |
| 22 | `u128 as f16` ICEs on targets without native 128-bit ints | src/int.rs:937-944 | tests/run/bug_u128_to_f16.rs (green locally; fails on the without-128bit CI and 32-bit targets) | related: #825, old #155 |

Suboptimal codegen, asm-verified (§4): const over-alignment on cache hits
(tests/asm/bug_static_overalign.rs, related #714), u128 `switch` if-ladder, `ctpop` loop at
baseline x86-64 (#351), `fmuladd` forced libcall, `simd_bitmask` scalarized, branchy saturating
add / small-struct `==`. Several other suspected quality problems turned out to be **fine at
-O3** because GCC's optimizer recovers them — they are listed explicitly in §4.3 so they don't
get re-reported.

---

## 2. Confirmed bugs in detail

Commands used for every entry (abbreviated in the transcripts below):

```
# cg_gcc               (debug CI config adds: -C llvm-args=sanitize-undefined -C link-args=-lubsan)
rustc +nightly-2026-08-04 -Zcodegen-backend=$PWD/target/debug/librustc_codegen_gcc.so \
      --sysroot $PWD/build/build_sysroot/sysroot/ -C link-arg=-lc [-C opt-level=3 -C lto=no] x.rs
# reference
rustc +nightly-2026-08-04 [-O] x.rs
```

### Bug 1 — unsigned atomic `fetch_max`/`fetch_min` use a signed comparison

All four RMW extremum ops (`Max`, `UMax`, `Min`, `UMin`, src/builder.rs:1754-1765) funnel into
the same `atomic_extremum` helper, which performs its comparison in the return type of the
`__atomic_load_N` builtin — a *signed* integer type — so the unsigned variants compare signed.

```
AtomicU32::new(1).fetch_max(0x8000_0000)    gcc: stays 1          llvm: 2147483648
AtomicU32::new(u32::MAX).fetch_min(1)       gcc: stays 4294967295 llvm: 1
```

Identical at -O0 and -O3; signed variants and the basic return value are correct. The
reproducer only uses ≤32-bit atomics so it also runs on the m68k CI.

### Bug 2 — atomic `fetch_max`/`fetch_min` return a stale previous value

`atomic_extremum` (src/builder.rs:89-91) loads the current value once, before the
compare-exchange loop, and returns that first snapshot even when the CAS had to retry. The
returned "previous value" can then be older than the value the successful CAS actually
replaced — `fetch_max` linearizability is broken.

Detector (tests/run/bug_atomic_max_stale_return.rs): 4 threads perform `fetch_max` with
globally unique ticket values; in a correct implementation the returns of writing operations
are all distinct. Observed: LLVM `ok`; cg_gcc **125467** duplicate returns at -O0 and
**342131** at -O3 (of 800k ops) — the race fires reliably, this is not a flaky detector.

### Bug 3 — `compare_exchange(Release, Acquire)` loses the Release ordering

src/builder.rs:1726 resolves the success/failure ordering pair by taking the **max of the two
discriminants**. `Release` and `Acquire` are incomparable in the ordering lattice (Release=1 <
Acquire=2 as discriminants), so success collapses to Acquire and the emitted builtin call is:

```
__atomic_compare_exchange_4 (&value, &expected, 2, 0, 2, 2);   // success=ACQUIRE — WRONG
```

The release barrier on the successful store is gone. GCC requires failure ≤ success, so the
correct strengthening is success=ACQ_REL: `(..., 0, 4, 2)`. Evidence: `CG_GCCJIT_DUMP_GIMPLE=1`
dump of all 15 monomorphized ordering combinations — the pair `(3, 2)` is never emitted and
`(2, 2)` appears 3× (for Relaxed/Acquire and Acquire/Acquire, which are legal, and for
Release/Acquire, which is the bug). x86-TSO gives release stores for free, so this is not
runtime-observable on x86_64 — the reproducer is a **GIMPLE test**
(tests/compile/bug_cmpxchg_release_acquire.rs) in the spirit of rustc's LLVM-IR codegen tests:
it sets `env-var: CG_GCCJIT_DUMP_GIMPLE=1` and asserts the corrected memmodel pair
`..., 0, 4, 2);` in the dump (verified: 0 matches today, the call is monomorphic in the test
crate via a direct `atomic_cxchg::<u32, {Release}, {Acquire}>` call).

### Bug 4 — `simd_as` float→int does not saturate

Both `simd_cast` (allowed to be UB out of range) and `simd_as` (must have scalar `as`
semantics) lower to the same `convert_vector` C-style cast (src/intrinsic/simd.rs:659-711).

```
[1e10f32, -1e10, NaN, 1.0] as I32x4
gcc0/gcc3: [-2147483648, -2147483648, -2147483648, 1]
llvm:      [2147483647, -2147483648, 0, 1]            (saturate, NaN → 0)
```

### Bugs 5 & 6 — `simd_gather`/`simd_scatter` access masked-off lanes (issue #640)

The lowering evaluates every lane's load before selecting by mask; scatter additionally
performs a gather with the inverted mask and then stores every lane. A masked-off lane
holding a null pointer segfaults. Both reproducers put null in a disabled lane: LLVM prints
`[42, -2]` / `7`, cg_gcc dies with SIGSEGV at both opt levels. This matches the analysis in
issue #640 exactly. (Masked *load/store* — `simd_masked_load`/`simd_masked_store` — were
explicitly guard-page-tested and do NOT share this bug; the `bx.select` there only evaluates
the load in the taken branch.)

### Bug 7 — signed `simd_saturating_sub` wrong when rhs contains `T::MIN`

The signed path implements `sat_sub(a, b)` as `sat_add(a, -b)`; `-(T::MIN)` wraps to `T::MIN`
(src/intrinsic/simd.rs:1310-1342).

```
[0, 100, -100, -1]i8 saturating_sub [-128; 4]
gcc0/gcc3: [-128, -28, -128, -128]      llvm: [127, 127, 28, 127]
```

Scalar saturating ops and `simd_saturating_add` are unaffected (verified).

### Bug 8 — `is_val_statically_known` inverted

src/intrinsic/mod.rs:320-325 emits `__builtin_constant_p(x) == 0` — the polarity is backwards.
For a runtime value (the program's argument count) cg_gcc returns `true` at both opt levels;
the intrinsic's contract explicitly forbids `true` for values not known at compile time
(LLVM prints `false`). Every `core` fast-path keyed on this intrinsic (e.g. `int_pow`)
currently takes the wrong branch.

### Bug 9 — `f16::mul_add` double rounding

`fmaf16` is lowered by casting operands to f32, calling f32 `fmaf`, and casting back
(src/intrinsic/mod.rs:156-179, `f16_builtin`). The f32 fma rounds the exact result to 24 bits,
the cast rounds again to 11 — and when the first rounding lands exactly on an f16 tie point,
ties-to-even goes the wrong way. Sweep evidence: 60 mismatches vs a correctly-rounded f64
reference over ~2.03M input triples (LLVM: 0). Hand-verified minimal case (in the test):
`a=0x4001, b=0x03ff, c=0x3555` → exact result 2·2⁻³⁴ *below* the tie; correct 0x3555, cg_gcc
0x3556. The `"llvm.fma.f16"` arm (src/intrinsic/mod.rs:580-584, f64 fma + truncate) is the
same class of issue (unverified; needs avx512fp16 stdarch intrinsics to reach).

### Bug 10 — `unaligned_volatile_load` ignores its alignment

The intrinsic arm correctly passes `Align::ONE`, but `volatile_load` (src/builder.rs:1048,
`// FIXME(antoyo): set alignment`) drops the parameter and dereferences a naturally-aligned
`volatile T*`. For a `#[repr(C, packed)]` u128 field, GCC concludes the pointer is 16-aligned
and at -O3 emits `vmovdqa` (an alignment-checking load) at base+1 → **SIGSEGV**. The debug
pass happens to survive; the release pass of the reproducer crashes. LLVM is correct at both.

### Bug 11 — inline-asm register clobber lost when the register is also an input (issue #77)

src/asm.rs:205-217: a discarded explicit-register output (`lateout("rcx") _` — including every
clobber synthesized by `clobber_abi`) whose register also appears as an input is rewritten
into a generic `"=r"` dummy output that is neither pinned to the register nor put in the
clobber list. GCC then assumes the register survives the asm and reads the clobbered register
afterwards. This breaks the *documented* call-from-asm pattern (`in("rdi") x` +
`clobber_abi("C")`).

```
victim(41): asm zeroes rcx which also carries x; then computes x + 1
gcc -O3: result = 1        llvm -O3: result = 42
```

Also reproduced with a realistic `call {f}` + `clobber_abi("C")` and with `in("xmm0")` +
`lateout("xmm0") _`. This answers issue #77: `clobber_abi` is **not** correctly supported
whenever an input lives in a clobbered register. (At -O0 the reproducer happens to pass —
GCC keeps `x` on the stack — so the checked-in test fails in the release suite.)

### Bug 12 — `sym` operands spliced in declaration order

src/asm.rs pushes `sym`/const-pointer symbol names in *operand* order (asm.rs:418-423) but
consumes them with `remove(0)` in *template-reference* order (asm.rs:520-522). A template
referencing `{1}` before `{0}` calls the wrong functions:

```
asm!("call {1}", ..., "call {0}", ..., sym func_a, sym func_b, ...)
gcc: first=111 second=222 (swapped)     llvm: first=222 second=111
```

### Bug 13 — `#[linkage = "weak"]` emits a GLOBAL symbol

`linkage_to_gcc` maps `WeakAny` to `FunctionType::Exported` (src/base.rs:63,
`// FIXME(antoyo): should be similar to linkonce.`); the static path (`define_global`) likewise
drops the weak binding. `readelf` shows binding GLOBAL where LLVM emits WEAK. Consequence: a
weak Rust default cannot be overridden by a strong definition — the link fails with
`duplicate symbol`. Reproducers: tests/run/bug_linkage_weak.rs links against a strong
`provider()` in tests/c/bug_linkage_weak.c (GCC-compiled; LLVM links and prints 999, cg_gcc
fails to link), and tests/asm/bug_weak_linkage.rs asserts the `.weak` directive in the
emitted assembly.

### Bug 14 — `ArgAbi::store` PassMode::Cast copies `layout.size` bytes from a `cast.size` scratch

src/intrinsic/mod.rs:782-799 allocates the scratch slot with the *cast* type's size but
memcpys `self.layout.size` bytes out of it. Current cg_llvm copies
`min(cast.unaligned_size, layout.size)` with a comment that the ABI type may be smaller than
the Rust type. On x86-64 SysV, `#[repr(C, align(16))] struct { x: u64 }` (size 16) classifies
as a single `i64` (8 bytes): cg_gcc copies 16 bytes from an 8-byte object. Observable impact:
at -O0 GCC's own `memcpy reading 16 bytes from a region of size 8` diagnostic is escalated
through gccjit into a rustc panic — **any crate passing such a struct by value `extern "C"`
fails to build**. At -O3 it builds; the over-read lands in trailing padding on x86-64, so no
wrong value was observed (but the OOB read is real and sanitizer-visible). The checked-in
test currently fails at the debug pass (build failure) and passes the release pass.

### Bug 15 — non-power-of-two SIMD lane counts ICE

Valid `#[repr(simd)]` / `std::simd::Simd<T, N>` types with N = 3, 5, 6, 7, 9, ... abort:
`gcc_jit_type_get_vector: num_units not a power of two: 3`, panic at src/type_of.rs:76. LLVM
compiles and runs the same program (prints `11 22 33`). Note: this single ICE currently
**masks four real latent bugs** in the non-pow2 code paths (§3.1) — fixing it (e.g. by
padding to the next power of two) will expose them, so they should be fixed together.

### Bug 16 — `simd_arith_offset` unimplemented

No handler exists; it falls through to `unimplemented!("simd {}", name)`
(src/intrinsic/simd.rs:1677). Reached by ordinary `std::simd` pointer-vector arithmetic
(`Simd<*const T, N>::wrapping_add` — core_simd const_ptr.rs:126 calls it directly), so any
portable-simd pointer math ICEs. cg_llvm implements it as a vector GEP.

### Bugs 17 & 18 — `breakpoint` and `prefetch_*` ICE

`sym::breakpoint => unimplemented!()` (src/intrinsic/mod.rs:337; `core::arch::breakpoint()` is
on the stabilization track) and the four prefetch arms (mod.rs:360, issue #414). GCC offers
`__builtin_prefetch` for the latter; LLVM compiles both fine.

### Bug 19 — `sym` operand referenced twice ICEs

Same root cause as bug 12: one Vec entry per *operand*, one `remove(0)` per template
*reference* — the second `{0}` pops an empty Vec:
`panicked at src/asm.rs:522: removal index (is 0) should be < len (is 0)`.

### Bug 20 — `global_asm!` comment stripping corrupts string literals

Because GAS lacks `//` comments, src/asm.rs:956-968 strips `//…` from the raw template with no
string-literal awareness. `.ascii "http://x"` becomes `.ascii "http:` → assembler error
(`unterminated string`), compilation fails; a template that still assembled would carry
silently corrupted data. LLVM passes the template through verbatim.

### Bug 21 — remaining `#[linkage]` kinds ICE

`weak_odr`, `linkonce`, `linkonce_odr`, `common` on functions hit `unimplemented!()` arms in
`linkage_to_gcc` (src/base.rs:61-67). All five kinds (incl. `weak`) compile and run under
LLVM. The static-side `global_linkage_to_gcc` arms (base.rs:46-52) are only reachable via
`import_linkage` on extern statics.

### Bug 22 — `u128 as f16` ICEs without native 128-bit integers

`int_to_float_cast` (src/int.rs:937-944) handles Float/Double/FP128 destinations but not
`TypeKind::Half`: `panic!("cannot cast a non-native integer to type Half")`. The reverse
direction handles Half by promoting through f32 (int.rs:984-990), so only int→f16 is broken.
Verified locally by temporarily forcing `u128_type_supported = false` in src/base.rs: the
reproducer ICEs at src/int.rs:943 (edit reverted, backend rebuilt clean). The checked-in test
passes on x86_64 and is expected to fail on the without-128bit-integers CI and on 32-bit
targets (m68k CI).

---

## 3. Suspected / latent (no reproducer possible today — with reachability analysis)

### 3.1 Masked by the non-pow2 ICE (bug 15) — will become live when it is fixed

- **`vector_reduce` duplicates lanes for non-pow2 counts** (src/builder.rs:2218-2233): the
  rotate-and-combine tree with `(i + shift) % element_count` only visits each lane once for
  power-of-two counts. For 3 lanes, `reduce_add([a0,a1,a2])` = `2*a0+a1+a2`; xor loses a
  lane entirely. Idempotent reductions (min/max/and/or/all/any) survive. All pow2-lane
  reductions verified correct vs LLVM.
- **`shuffle_vector` drops second-vector lanes when `in_len < out_len < 2*in_len`**
  (src/builder.rs:2128-2164): the concat keeps only `out_len - in_len` elements of v2 and
  replaces v2 with zeros, so legal mask indices in `[out_len, 2*in_len)` select zero. The
  same path also constructs out-of-bounds `new_vector_access(v2, i)` reads in the reachable
  `out_len ≥ 2*in_len` case (empirically harmless, UBSAN-clean; lanes never selectable).
  All constructible (pow2) length-changing shuffles verified correct.
- **`simd_bitmask`/`simd_select_bitmask` for 9..24 lanes**: `type_ix` (src/type_.rs:26,
  `(num_bits / 8).next_power_of_two()`) rounds 9..15 and 17..23 bits *down* to i8/i16 →
  mask truncation; the 24-lane `[u8; 3]` form loads/stores 4 bytes against a 3-byte alloca
  (src/intrinsic/simd.rs:86-91, 779-786) → stack OOB. Also simd.rs:744 `in_len.max(8)` differs
  from cg_llvm's `.next_power_of_two()` formula (coincidentally equal for pow2 lanes). All
  reachable (pow2 8/16/32/64-lane) bitmask forms verified correct and UBSAN-clean.
- **zext of a signed-source i1-vector** (src/builder.rs:1850-1853 does a cast, not a
  zero-extension): exhaustive cg_ssa call-site audit found no reachable signed-source case
  apart from the masked bitmask path above.

### 3.2 Cross-arch / other-config only

- **`store_fn_arg` bypasses on-stack byval handling** (src/intrinsic/mod.rs:808-834 uses raw
  `get_param`, unlike abi.rs:23-34 which takes the address for `on_stack_param_indices`):
  only reachable when cg_ssa sees `attrs.pointee_align < layout.align.abi` — never true on
  x86-64, plausible on 32-bit x86 (byval align 4 vs u64 align 8). Would treat a by-value
  struct as a pointer.
- **`simd_masked_load`/`store` ignore the `SimdAlign` parameter** (src/intrinsic/simd.rs:1509,
  1597): element-typed accesses assume natural alignment; harmless on x86-64 (verified,
  including guard-page proof that masked-off lanes are untouched), could fault on
  strict-alignment targets.
- **`clobber_abi` silently drops x87/MMX/AMX clobbers** (asm.rs:228-239 filters out st0-7,
  mm0-7, tmm0-7 because their reg classes have empty `supported_types`): no miscompile
  constructible on x86-64 since Rust never keeps values in those banks, but the clobbers are
  really gone.
- **Sub-register aliasing rejected** (asm.rs:206 compares register *name strings*): `in("al")`
  + `clobber_abi("C")` (which clobbers `ax`) → GCC hard error `'asm' specifier for variable
  conflicts with 'asm' clobber list`; LLVM accepts. Rejects-valid-code, same alias-blindness
  family as bug 11.
- **Big-endian `high()`/`low()`** (src/int.rs:1025-1043) read correct but are untestable on
  x86_64; the m68k CI plus the audit's sweep files would cover them.
- **f16/f128 `Reg::gcc_type` `bug!()`** (abi.rs:88-91): unreachable on x86-64 (classifier
  never produces f16/f128 Reg components).

### 3.3 Latent-but-unreachable (kept for the record)

- **fcmp `RealUGE`/`RealULE` map to strict `>`/`<`** (src/builder.rs:2539/2541, drops the
  equals case): only ordered rows + ULT/UGT/OEQ/OGT are reachable from Rust float comparisons
  and `fptoint_sat`; the wrong rows are dead today (context: #626 closed, #721 open).
- **`scalar_to_backend` Ptr-scalar with integer primitive does `ptr.dereference()`**
  (src/common.rs:357-358) — would read the *pointee* where LLVM takes the *address*;
  const-eval structurally forbids the combination today (tried transmute and union tricks).
- **`gcc_shl` casts the shifted value to `b_type`** (src/int.rs:667-670): truncates if a
  future caller passes a narrower shift-amount type; all current callers size-equalize.
- **`__mulosi4`/`__mulodi4` arms** (src/int.rs:313-314): dead (only 128-bit is non-native);
  would trip a debug_assert if ever reached.

---

## 4. Suboptimal codegen (all claims backed by asm diffs produced this session)

Method: `#[no_mangle]` kernels, cg_gcc `-Copt-level=3 -Clto=no -Ccodegen-units=1
-Cpanic=abort -Ctarget-feature=-avx --emit asm` vs LLVM with the same options (minus the
gcc-specific ones), `-Ctarget-cpu=x86-64-v2` unless stated. cg_gcc force-adds `-mavx`
otherwise (src/gcc_util.rs:183-188), which would skew comparisons.

### 4.1 Confirmed

1. **128-bit `switch` → if-ladder** (src/builder.rs:620-641): an 8-arm u128 match compiles to
   a 43-instruction cmp/branch ladder; LLVM emits 6 branchless instructions. Dramatic and
   hits any dispatch on u128/i128 discriminants.
2. **`ctpop` at baseline x86-64** (src/intrinsic/mod.rs Wegner-loop lowering, issue #351):
   without `popcnt` hardware GCC keeps the *data-dependent loop* (O(set bits) iterations);
   LLVM emits the 19-instruction constant-time bit-twiddle. At x86-64-v2 GCC's loop-idiom
   recognition converts the loop to `popcnt` and the gap disappears — this is baseline-only,
   but the baseline is the default target. Using `__builtin_popcountll` would fix both.
3. **`fmuladd` forces a correctly-rounded libcall without FMA hardware**: `fmuladdf64` at
   baseline compiles to `jmp fma@PLT` (libm software fma, ~100 cycles); LLVM emits
   `mulsd + addsd` (2 instructions — the intrinsic explicitly permits unfused evaluation).
4. **`simd_bitmask` scalarized**: i32x4 → u8 mask is a 14-instruction per-lane
   extract/shift/or chain; LLVM: `movaps + movmskps`. GCC does not recover the movmsk idiom
   (unlike blend, which it does recover — see §4.3).
5. **Signed `saturating_add` is branchy** (src/intrinsic/mod.rs:1210-1334): `jo` over a
   branchless LLVM `cmovno` sequence (7 vs 6 insns). Minor (overflow path is cold).
6. **8-byte struct `==` is branchy**: GCC inlines the `raw_eq` memcmp into two 4-byte
   compares with an early-out branch; LLVM does one branchless 8-byte compare. Minor. The
   `_use_integer_compare` fast path in `raw_eq` (src/intrinsic/mod.rs:449-490) is computed
   and then ignored — correct but wasted.
7. **Constants 8× over-aligned on const-cache hits** (src/consts.rs:65 passes `align.bits()`
   to a bytes-taking API; the fresh-creation path at :55 correctly uses `align.bytes()`):
   a deduplicated `&42` gets `.align 32` instead of `.align 4`
   (tests/asm/bug_static_overalign.rs; related: #714). Pure rodata waste, listed here rather
   than as a miscompile.

### 4.2 Report-only notes (code-level, no asm needed)

- `-Os`/`-Oz` are mapped to GCC `-O1`, not `-Os` (src/lib.rs:500-509).
- Fast-math flags are dropped (src/builder.rs:962-985); `expect`/`likely` is a no-op
  (src/intrinsic/mod.rs:667) — not demonstrable in a small kernel (GCC's call-based
  heuristics compensate) but real for panic-path layout; `assume` is skipped at -O0 by
  design and **does** optimize at -O3 (verified, §4.3).
- `MemFlags::NONTEMPORAL` ignored; memcpy/memmove/memset ignore the volatile flag.
- `arith_red!` int reductions compute `vector_reduce_op` twice, discarding the first
  (src/intrinsic/simd.rs:1348-1387); the `$identity` argument is unused (simd.rs:1394 FIXME).
- `const_to_opt_uint` always returns None (src/common.rs:302-310); dropped param attributes
  (src/abi.rs:139-158); lifetime markers are no-ops. (Issue #56 — extra memcpys — is the
  broader umbrella for the PassMode::Cast scratch traffic; at -O3 the small-struct case
  optimized clean in this audit's kernels.)

### 4.3 Suspected quality problems that turned out FINE at -O3 (checked, dropped)

GCC's middle-end recovers all of these from cg_gcc's naive lowerings — do not re-report:

- `select` → branches: if-converted to `cmov`(4v4 insns, equal).
- `ctpop` at x86-64-v2: loop-idiom-recognized into `popcnt`.
- `unlikely` dropped: the kernel was if-converted; no layout penalty demonstrable.
- NonZero niche `== 0`: the `assume`-as-branch encoding folds to `xor eax` — range metadata
  loss did not hurt here.
- `simd_fsqrt` scalarized to 4 libm calls in the IR: SLP re-vectorizes to one `sqrtps`
  (transcendentals without a vector ISA equivalent stay scalar calls on both backends).
- `memcpy` alignment dropped: 64-byte copies identical (`movups` both).
- `black_box`: LLVM generates the same stack round-trip (identical 4v4).
- `simd_select` `(m & a) | (~m & b)`: GCC recognizes it and emits `pblendvb` (equal to LLVM's
  `blendvps`).
- extern "C" small-struct passing (PassMode::Cast): register-only and identical at -O3; the
  scratch round-trip only exists at -O0 (see bug 14 for the correctness part).

---

## 5. Dropped candidates (verified not-bugs)

Everything below was runtime-diffed against LLVM at -O0 and -O3 (sources in the audit
scratchpad) and found identical:

- **Scalar saturating add/sub** all widths (exhaustive i8 sweep) — the pointer-cast formula
  is correct.
- **`vector_reduce_min/max` wrapping-sub trick** — sound under the global `-fwrapv`.
- **Float `simd_reduce_min/max`** rejection (E0511) matches cg_llvm's behavior (upstream
  LLVM limitation, not a cg_gcc divergence).
- **128-bit integers** (src/int.rs): shifts/compares/checked/saturating/rotates/casts/
  formatting/switches, native AND emulated paths (via the temporary base.rs toggle), incl.
  `i128::MIN / -1`, `INT_MIN * -1`, float↔int128 saturation boundaries — no divergence.
  `operation_with_overflow`'s signed FnAbi is harmless (i128/u128 classify identically).
- **ctlz/cttz/ctpop/bswap/bitreverse/rotate** full-width sweeps incl. u128 and the uchar
  width-correction branch; **funnel shifts** incl. the u128 promotion path.
- **f16 unary ops** (all 65536 bit patterns: sqrt/rounding family/abs/copysign), **powi**,
  f32/f64 `minimum`/`maximum` IEEE semantics, f128 family, `simd_fma` (fused, bit-exact),
  vector float rounding (sign-of-zero, ties), transcendentals.
- **c_variadic** (va_copy, 10-arg spills, mixed types, u128 va_arg, snprintf caller).
- **Inline asm**: tied operand numbering with scrambled operand kinds, byte registers,
  att_syntax, `|` in templates, asm-goto labels, naked functions, `sym` statics with offsets,
  AVX-512 k-reg brace escaping, `options(nomem)` not causing rdtsc CSE.
- **ABI**: 26-struct battery (sizes 3-25, mixed int/float, both directions Rust↔GCC-compiled
  C at -O0/-O3), guard-page proof of no argument over-read from the CastTarget round-up,
  i128 by value/in structs/indirect calls, f16/f128 extern "C" on x86-64, over-aligned byval
  (existing tests), interior-mutability statics writable, thread_local, vtables, fn-pointer
  arrays, relocated statics (pointer identity holds), `declare_raw_fn` name-cache with
  conflicting signatures.
- **Memory/builder**: scalar pairs (bool niches, b_offset=16), packed/misaligned u128
  load/store, `become` tail calls 100k deep, three_way_compare, negative/huge GEP offsets,
  `write_operand_repeatedly`, `mir_preserve_ub_empty_switch` (existing test), volatile
  round-trips, `simd_insert/extract(_dyn)`, provenance intrinsics, `ptr_mask`,
  `compare_bytes`, `raw_eq` (incl. 0- and 17-byte), aligned `volatile_load`.

---

## 6. Appendix

### 6.1 Known pre-existing tracked problems (excluded from this audit's findings)

panic_nounwind garbled `&str` argument; pthread_exit-through-nounwind abort (#264 family);
rt-explody catch_unwind miscompile; 16-byte atomic libcalls (`__atomic_load_16` undefined);
m68k eh_return epilogue clobber (GCC bug); stack-probe detection flakiness; stdarch scalef
(GCC sse.md bug); panic=abort unoptimized-std link failure (upstream rustc#144121).

### 6.2 Test inventory added by this audit

- `tests/run/`: bug_atomic_umax_umin, bug_atomic_max_stale_return, bug_simd_as_sat,
  bug_simd_gather_mask, bug_simd_scatter_mask, bug_simd_saturating_sub,
  bug_is_val_statically_known, bug_fma_f16, bug_unaligned_volatile_load,
  bug_abi_cast_align16, bug_asm_clobber_lost, bug_asm_sym_order, bug_linkage_weak,
  bug_u128_to_f16 (each `.rs`).
- `tests/c/`: bug_linkage_weak.c (strong-override reference, auto-linked by stem).
- `tests/compile/`: bug_simd_nonpow2_lanes, bug_simd_arith_offset, bug_breakpoint,
  bug_prefetch, bug_asm_sym_dup, bug_global_asm_string, bug_linkage_weak_odr,
  bug_cmpxchg_release_acquire (GIMPLE test via `env-var: CG_GCCJIT_DUMP_GIMPLE=1`).
- `tests/asm/`: bug_static_overalign.rs, bug_weak_linkage.rs (compiletest Assembly/FileCheck).

Verified states on this machine: all of the above fail with exactly the documented mismatch,
except bug_u128_to_f16 (green here; targets the without-128bit CI / 32-bit targets).
bug_asm_clobber_lost and bug_unaligned_volatile_load pass the debug suite and fail the
release suite; bug_abi_cast_align16 fails the debug suite at its compile step (the release
build succeeds); bug_linkage_weak fails the link step at both opt levels. Pre-existing tests spot-checked green (structs, overaligned_byval*, int_overflow,
full green baseline run before any test was added). The x86_64-specific asm-using tests are
cfg-gated to pass trivially on non-x86 targets; note that the f16 tests assume the target
supports f16 (x86_64 CI does; if the m68k CI lacks it they would need an entry in
`files_to_ignore_on_m68k` in tests/lang_tests.rs).

**GIMPLE tests**: compiletest has no GIMPLE mode, so the cmpxchg test uses lang_tester's
`env-var:` + fuzzy `stderr:` matching against `CG_GCCJIT_DUMP_GIMPLE=1` output — that dump
goes to stderr, and `...`-prefixed patterns give the same feel as FileCheck. This pattern is
reusable for any future IR-level assertion.

### 6.3 What was NOT covered

Other targets at runtime (m68k/BE paths analyzed statically only), LTO configurations,
panic=abort sysroots, debuginfo quality, the non-`master` feature configuration, distro
GCC versions, 32-bit x86 (no sysroot available — relevant for the store_fn_arg suspicion).

### 6.4 Methodology

Phased: (0) green-baseline `./y.sh test --cargo-tests`; (1) triage-verify ~15 pre-analyzed
candidates through a compile-run-diff harness (gcc -O0 / gcc -O3 -Clto=no / LLVM reference,
core dumps disabled, 10s timeouts); (2) hard cases via a threaded stress detector, GIMPLE
dumps, `--emit asm`, and a temporary `u128_type_supported = false` toggle (reverted, backend
rebuilt clean — `git diff` empty for src/); (3) six parallel deep-review agents over
builder.rs, int.rs, intrinsic/mod.rs, intrinsic/simd.rs, abi/consts/type layers, and asm.rs,
each runtime-verifying its own findings the same way; (4) asm-verification of every quality
claim (claims that didn't survive -O3 are listed in §4.3 rather than silently dropped);
(5) one ungated reproducer test per confirmed bug; (6) this report. GitHub issues were
searched for every finding; matches are in the summary tables.
