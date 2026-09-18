//@ assembly-output: emit-asm
//@ only-x86_64
//@ compile-flags: -Copt-level=3
//@ revisions: att intel
//@[att] compile-flags: -Cllvm-args=-masm=att
// cg_gcc defaults to -masm=intel (gcc_util::new_context). It appends -Cllvm-args
// afterwards, so the att revision overrides that default; intel uses it unchanged.

#![crate_type = "lib"]
#![no_std]
#![feature(avx10_target_feature, x86_amx_intrinsics)]

use core::arch::x86_64::*;

// These use the fixed-register APIs, not the __tile* APIs with compiler-allocated tiles.
// Callers provide a palette-1 configuration with 16 rows and 64 bytes per row for
// each used tile, and buffers large enough for 16 rows at the supplied byte stride.
// Functions are alphabetical to match the assembly runner's emission order.

// CHECK-LABEL: {{^"?_?}}amx_float{{"?}}:
// CHECK: ldtilecfg
// att: tileloadd {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE:%[a-z0-9]+]]{{(,1)?\)}}, %tmm0
// intel: tileloadd tmm0, {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE:[a-z0-9]+]]{{(\*1)?\]}}
// att: tileloaddt1 {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE]]{{(,1)?\)}}, %tmm3
// intel: tileloaddt1 tmm3, {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE]]{{(\*1)?\]}}
// CHECK: tilezero {{%?}}tmm7
// att: tdpbf16ps %tmm3, %tmm0, %tmm7
// intel: tdpbf16ps tmm7, tmm0, tmm3
// att: tilestored %tmm7, {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE]]{{(,1)?\)}}
// intel: tilestored {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE]]{{(\*1)?\]}}, tmm7
// CHECK: tilezero {{%?}}tmm6
// att: tdpfp16ps %tmm0, %tmm3, %tmm6
// intel: tdpfp16ps tmm6, tmm3, tmm0
// att: tilestored %tmm6, {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE]]{{(,1)?\)}}
// intel: tilestored {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE]]{{(\*1)?\]}}, tmm6
// CHECK: tilezero {{%?}}tmm7
// att: tcmmimfp16ps %tmm3, %tmm0, %tmm7
// intel: tcmmimfp16ps tmm7, tmm0, tmm3
// att: tilestored %tmm7, {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE]]{{(,1)?\)}}
// intel: tilestored {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE]]{{(\*1)?\]}}, tmm7
// CHECK: tilezero {{%?}}tmm6
// att: tcmmrlfp16ps %tmm3, %tmm0, %tmm6
// intel: tcmmrlfp16ps tmm6, tmm0, tmm3
// att: tilestored %tmm6, {{\(%[a-z0-9]+,}}[[FLOAT_STRIDE]]{{(,1)?\)}}
// intel: tilestored {{\[[a-z0-9]+ *\+ *}}[[FLOAT_STRIDE]]{{(\*1)?\]}}, tmm6
// CHECK: tilerelease
#[no_mangle]
#[target_feature(enable = "amx-tile,amx-bf16,amx-fp16,amx-complex")]
pub unsafe fn amx_float(
    config: *const u8,
    a: *const u8,
    b: *const u8,
    bf16: *mut u8,
    fp16: *mut u8,
    imaginary: *mut u8,
    real: *mut u8,
    stride: usize,
) {
    _tile_loadconfig(config);
    _tile_loadd::<0>(a, stride);
    _tile_stream_loadd::<3>(b, stride);

    // Interpret the input bits as BF16, FP16 and complex FP16 independently.
    _tile_zero::<7>();
    _tile_dpbf16ps::<7, 0, 3>();
    _tile_stored::<7>(bf16, stride);
    _tile_zero::<6>();
    _tile_dpfp16ps::<6, 3, 0>();
    _tile_stored::<6>(fp16, stride);
    _tile_zero::<7>();
    _tile_cmmimfp16ps::<7, 0, 3>();
    _tile_stored::<7>(imaginary, stride);
    _tile_zero::<6>();
    _tile_cmmrlfp16ps::<6, 0, 3>();
    _tile_stored::<6>(real, stride);
    _tile_release();
}

// CHECK-LABEL: {{^"?_?}}amx_fp8{{"?}}:
// att: tdpbf8ps %tmm2, %tmm1, %tmm7
// intel: tdpbf8ps tmm7, tmm1, tmm2
// att: tdpbhf8ps %tmm1, %tmm2, %tmm7
// intel: tdpbhf8ps tmm7, tmm2, tmm1
// att: tdphbf8ps %tmm2, %tmm1, %tmm7
// intel: tdphbf8ps tmm7, tmm1, tmm2
// att: tdphf8ps %tmm1, %tmm2, %tmm7
// intel: tdphf8ps tmm7, tmm2, tmm1
#[no_mangle]
#[target_feature(enable = "amx-fp8")]
pub unsafe fn amx_fp8() {
    _tile_dpbf8ps::<7, 1, 2>();
    _tile_dpbhf8ps::<7, 2, 1>();
    _tile_dphbf8ps::<7, 1, 2>();
    _tile_dphf8ps::<7, 2, 1>();
}

// CHECK-LABEL: {{^"?_?}}amx_int8{{"?}}:
// CHECK: ldtilecfg
// CHECK: sttilecfg
// att: tileloadd {{\(%[a-z0-9]+,}}[[INT_STRIDE:%[a-z0-9]+]]{{(,1)?\)}}, %tmm1
// intel: tileloadd tmm1, {{\[[a-z0-9]+ *\+ *}}[[INT_STRIDE:[a-z0-9]+]]{{(\*1)?\]}}
// att: tileloaddt1 {{\(%[a-z0-9]+,}}[[INT_STRIDE]]{{(,1)?\)}}, %tmm2
// intel: tileloaddt1 tmm2, {{\[[a-z0-9]+ *\+ *}}[[INT_STRIDE]]{{(\*1)?\]}}
// CHECK: tilezero {{%?}}tmm7
// att: tdpbssd %tmm2, %tmm1, %tmm7
// intel: tdpbssd tmm7, tmm1, tmm2
// att: tdpbsud %tmm1, %tmm2, %tmm7
// intel: tdpbsud tmm7, tmm2, tmm1
// att: tdpbusd %tmm2, %tmm1, %tmm7
// intel: tdpbusd tmm7, tmm1, tmm2
// att: tdpbuud %tmm1, %tmm2, %tmm7
// intel: tdpbuud tmm7, tmm2, tmm1
// att: tilestored %tmm7, {{\(%[a-z0-9]+,}}[[INT_STRIDE]]{{(,1)?\)}}
// intel: tilestored {{\[[a-z0-9]+ *\+ *}}[[INT_STRIDE]]{{(\*1)?\]}}, tmm7
// CHECK: tilerelease
#[no_mangle]
#[target_feature(enable = "amx-tile,amx-int8")]
pub unsafe fn amx_int8(
    config: *const u8,
    saved_config: *mut u8,
    a: *const u8,
    b: *const u8,
    output: *mut u8,
    stride: usize,
) {
    _tile_loadconfig(config);
    _tile_storeconfig(saved_config);
    _tile_loadd::<1>(a, stride);
    _tile_stream_loadd::<2>(b, stride);
    _tile_zero::<7>();
    // Accumulate all signedness combinations; reversing inputs must not swap
    // which source is signed in the two mixed-signedness instructions.
    _tile_dpbssd::<7, 1, 2>();
    _tile_dpbsud::<7, 2, 1>();
    _tile_dpbusd::<7, 1, 2>();
    _tile_dpbuud::<7, 2, 1>();
    _tile_stored::<7>(output, stride);
    _tile_release();
}

// Here config enables only tile 7, with one row of four bytes. Input and output
// point to separate u32s. No volatile Rust accesses hide missing memory effects:
// the first input store is dead unless tileloadd reads memory, and the result is
// the sentinel unless tilestored invalidates the compiler's cached output value.
// Capture addresses rather than pinning register allocation or stack offsets.
// CHECK-LABEL: {{^"?_?}}amx_memory{{"?}}:
// CHECK: ldtilecfg
// att: movl {{%[a-z0-9]+}}, ([[INPUT:%[a-z0-9]+]])
// intel: mov DWORD PTR {{\[}}[[INPUT:[a-z0-9]+]]{{\]}}, {{[a-z0-9]+}}
// att: tileloadd ([[INPUT]],[[MEM_STRIDE:%[a-z0-9]+]]{{(,1)?}}), %tmm7
// intel: tileloadd tmm7, {{\[}}[[INPUT]]{{ *\+ *}}[[MEM_STRIDE:[a-z0-9]+]]{{(\*1)?\]}}
// att: movl $0, ([[INPUT]])
// intel: mov DWORD PTR {{\[}}[[INPUT]]{{\]}}, 0
// att: movl $305419896, ([[OUTPUT:%[a-z0-9]+]])
// intel: mov DWORD PTR {{\[}}[[OUTPUT:[a-z0-9]+]]{{\]}}, 305419896
// att: tilestored %tmm7, ([[OUTPUT]],[[MEM_STRIDE]]{{(,1)?}})
// intel: tilestored {{\[}}[[OUTPUT]]{{ *\+ *}}[[MEM_STRIDE]]{{(\*1)?\]}}, tmm7
// att-DAG: movl ([[OUTPUT]]), %eax
// intel-DAG: mov eax, DWORD PTR {{\[}}[[OUTPUT]]{{\]}}
// CHECK-DAG: tilerelease
// CHECK: ret
#[no_mangle]
#[target_feature(enable = "amx-tile")]
pub unsafe extern "C" fn amx_memory(
    config: *const u8,
    input: *mut u32,
    output: *mut u32,
    value: u32,
    stride: usize,
) -> u32 {
    _tile_loadconfig(config);
    input.write(value);
    _tile_loadd::<7>(input.cast(), stride);
    input.write(0);
    output.write(0x12345678);
    _tile_stored::<7>(output.cast(), stride);
    let result = output.read();
    _tile_release();
    result
}

// CHECK-LABEL: {{^"?_?}}amx_movrs{{"?}}:
// att: tileloaddrs {{\(%[a-z0-9]+,}}[[RS_STRIDE:%[a-z0-9]+]]{{(,1)?\)}}, %tmm7
// intel: tileloaddrs tmm7, {{\[[a-z0-9]+ *\+ *}}[[RS_STRIDE:[a-z0-9]+]]{{(\*1)?\]}}
// att: tileloaddrst1 {{\(%[a-z0-9]+,}}[[RS_STRIDE]]{{(,1)?\)}}, %tmm0
// intel: tileloaddrst1 tmm0, {{\[[a-z0-9]+ *\+ *}}[[RS_STRIDE]]{{(\*1)?\]}}
#[no_mangle]
#[target_feature(enable = "amx-movrs")]
pub unsafe fn amx_movrs(input: *const u8, stride: usize) {
    _tile_loaddrs::<7>(input, stride);
    _tile_stream_loaddrs::<0>(input, stride);
}

// Row operations return vectors, unlike the other fixed-register intrinsics. Preserve
// all results in caller-provided storage. Exercise both row encodings and both tile
// register boundaries; row 15 is the last row in a fully configured tile.
// CHECK-LABEL: {{^"?_?}}amx_rows{{"?}}:
// att: tilemovrow [[ROW:%(e[a-z]+|r[0-9]+d)]], %tmm7, {{%zmm[0-9]+}}
// intel: tilemovrow {{zmm[0-9]+}}, tmm7, [[ROW:(e[a-z]+|r[0-9]+d)]]
// att: tilemovrow $15, %tmm0, {{%zmm[0-9]+}}
// intel: tilemovrow {{zmm[0-9]+}}, tmm0, 15
// att: tcvtrowd2ps [[ROW]], %tmm7, {{%zmm[0-9]+}}
// intel: tcvtrowd2ps {{zmm[0-9]+}}, tmm7, [[ROW]]
// att: tcvtrowd2ps $15, %tmm0, {{%zmm[0-9]+}}
// intel: tcvtrowd2ps {{zmm[0-9]+}}, tmm0, 15
// att: tcvtrowps2phh [[ROW]], %tmm7, {{%zmm[0-9]+}}
// intel: tcvtrowps2phh {{zmm[0-9]+}}, tmm7, [[ROW]]
// att: tcvtrowps2phh $15, %tmm0, {{%zmm[0-9]+}}
// intel: tcvtrowps2phh {{zmm[0-9]+}}, tmm0, 15
// att: tcvtrowps2phl [[ROW]], %tmm7, {{%zmm[0-9]+}}
// intel: tcvtrowps2phl {{zmm[0-9]+}}, tmm7, [[ROW]]
// att: tcvtrowps2phl $15, %tmm0, {{%zmm[0-9]+}}
// intel: tcvtrowps2phl {{zmm[0-9]+}}, tmm0, 15
// att: tcvtrowps2bf16h [[ROW]], %tmm7, {{%zmm[0-9]+}}
// intel: tcvtrowps2bf16h {{zmm[0-9]+}}, tmm7, [[ROW]]
// att: tcvtrowps2bf16h $15, %tmm0, {{%zmm[0-9]+}}
// intel: tcvtrowps2bf16h {{zmm[0-9]+}}, tmm0, 15
// att: tcvtrowps2bf16l [[ROW]], %tmm7, {{%zmm[0-9]+}}
// intel: tcvtrowps2bf16l {{zmm[0-9]+}}, tmm7, [[ROW]]
// att: tcvtrowps2bf16l $15, %tmm0, {{%zmm[0-9]+}}
// intel: tcvtrowps2bf16l {{zmm[0-9]+}}, tmm0, 15
#[no_mangle]
#[target_feature(enable = "amx-avx512,avx10.2")]
pub unsafe fn amx_rows(output: *mut u8, row: u32) {
    output.cast::<__m512i>().write_unaligned(_tile_movrow::<7>(row));
    output.add(64).cast::<__m512i>().write_unaligned(_tile_movrowi::<0, 15>());
    output.add(128).cast::<__m512>().write_unaligned(_tile_cvtrowd2ps::<7>(row));
    output.add(192).cast::<__m512>().write_unaligned(_tile_cvtrowd2psi::<0, 15>());
    output.add(256).cast::<__m512h>().write_unaligned(_tile_cvtrowps2phh::<7>(row));
    output.add(320).cast::<__m512h>().write_unaligned(_tile_cvtrowps2phhi::<0, 15>());
    output.add(384).cast::<__m512h>().write_unaligned(_tile_cvtrowps2phl::<7>(row));
    output.add(448).cast::<__m512h>().write_unaligned(_tile_cvtrowps2phli::<0, 15>());
    output.add(512).cast::<__m512bh>().write_unaligned(_tile_cvtrowps2bf16h::<7>(row));
    output.add(576).cast::<__m512bh>().write_unaligned(_tile_cvtrowps2bf16hi::<0, 15>());
    output.add(640).cast::<__m512bh>().write_unaligned(_tile_cvtrowps2bf16l::<7>(row));
    output.add(704).cast::<__m512bh>().write_unaligned(_tile_cvtrowps2bf16li::<0, 15>());
}
