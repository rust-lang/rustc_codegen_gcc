use gccjit::Function;

use crate::context::CodegenCx;

pub fn intrinsic<'gcc, 'tcx>(name: &str, cx: &CodegenCx<'gcc, 'tcx>) -> Function<'gcc> {
    let gcc_name =
        match name {
            "llvm.x86.xgetbv" => "__builtin_ia32_xgetbv",
            // NOTE: this doc specifies the equivalent GCC builtins: http://huonw.github.io/llvmint/llvmint/x86/index.html
            "llvm.x86.sse2.pmovmskb.128" => "__builtin_ia32_pmovmskb128",
            "llvm.x86.avx2.pmovmskb" => "__builtin_ia32_pmovmskb256",
            "llvm.x86.sse2.cmp.pd" => "__builtin_ia32_cmppd",
            "llvm.x86.sse2.movmsk.pd" => "__builtin_ia32_movmskpd",
            "llvm.x86.ssse3.pshuf.b.128" => "__builtin_ia32_pshufb128",
            "llvm.x86.sse2.pause" => "__builtin_ia32_pause",
            "llvm.x86.avx2.pshuf.b" => "__builtin_ia32_pshufb256",
            "llvm.x86.avx2.pslli.d" => "__builtin_ia32_pslldi256",
            "llvm.x86.avx2.psrli.d" => "__builtin_ia32_psrldi256",
            "llvm.x86.avx.vzeroupper" => "__builtin_ia32_vzeroupper",
            "llvm.x86.avx2.vperm2i128" => "__builtin_ia32_permti256",
            "llvm.x86.avx2.psrli.w" => "__builtin_ia32_psrlwi256",
            "llvm.x86.sse2.storeu.dq" => "__builtin_ia32_storedqu",
            "llvm.x86.sse2.psrli.w" => "__builtin_ia32_psrlwi128",
            "llvm.x86.avx2.pabs.d" => "__builtin_ia32_pabsd256",
            "llvm.x86.sse2.psrli.q" => "__builtin_ia32_psrlqi128",
            "llvm.x86.avx2.pabs.w" => "__builtin_ia32_pabsw256",
            "llvm.x86.avx2.pblendvb" => "__builtin_ia32_pblendvb256",
            _ => unimplemented!("***** unsupported LLVM intrinsic {}", name),
        };

    let func = cx.context.get_target_builtin_function(gcc_name);
    cx.functions.borrow_mut().insert(gcc_name.to_string(), func);
    func
}
