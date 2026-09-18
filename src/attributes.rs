#[cfg(feature = "master")]
use gccjit::FnAttribute;
use gccjit::Function;
#[cfg(feature = "master")]
use rustc_abi::{CanonAbi, InterruptKind};
#[cfg(feature = "master")]
use rustc_data_structures::fx::FxHashSet;
#[cfg(feature = "master")]
use rustc_hir::attrs::InlineAttr;
use rustc_hir::attrs::InstructionSetAttr;
#[cfg(feature = "master")]
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
#[cfg(feature = "master")]
use rustc_middle::mir::TerminatorKind;
use rustc_middle::ty;
#[cfg(feature = "master")]
use rustc_span::def_id::DefId;
use rustc_target::callconv::FnAbi;
#[cfg(feature = "master")]
use rustc_target::spec::Arch;

#[cfg(feature = "master")]
use crate::base;
use crate::context::CodegenCx;
use crate::gcc_util::to_gcc_features;

/// Check forced-inline call chains for cycles. Merely calling another
/// always-inline function is not recursion.
#[cfg(feature = "master")]
fn recursively_inline<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    instance: ty::Instance<'tcx>,
) -> bool {
    // Keep the DFS on the heap: valid forced-inline chains can be arbitrarily
    // deep, independently of the compiler thread's remaining call stack.
    let mut pending: Vec<(DefId, bool)> = vec![(instance.def_id(), false)];
    let mut active = FxHashSet::default();
    while let Some((def, finishing)) = pending.pop() {
        if finishing {
            active.remove(&def);
            cx.inline_recursion.borrow_mut().insert(def, false);
            continue;
        }
        let cached = cx.inline_recursion.borrow().get(&def).copied();
        if cached == Some(false) {
            continue;
        }
        if cached == Some(true) || active.contains(&def) || !cx.tcx.is_mir_available(def) {
            let mut cache = cx.inline_recursion.borrow_mut();
            cache.insert(def, true);
            for caller in active {
                cache.insert(caller, true);
            }
            return true;
        }
        active.insert(def);
        pending.push((def, true));
        for block in cx.tcx.optimized_mir(def).basic_blocks.iter().rev() {
            let Some(ref terminator) = block.terminator else { continue };
            let TerminatorKind::Call { ref func, .. } = terminator.kind else { continue };
            let Some((callee, _)) = func.const_fn_def() else { continue };
            if matches!(
                cx.tcx.codegen_fn_attrs(callee).inline,
                InlineAttr::Always | InlineAttr::Force { .. }
            ) {
                pending.push((callee, false));
            }
        }
    }
    false
}

/// Get GCC attribute for the provided inline heuristic, attached to `instance`.
#[cfg(feature = "master")]
#[inline]
fn inline_attr<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    inline: InlineAttr,
    instance: ty::Instance<'tcx>,
) -> Option<FnAttribute<'gcc>> {
    match inline {
        InlineAttr::Always => {
            // GCC cannot force recursive call chains inline. Preserve the
            // guarantee for acyclic chains, including nested intrinsic wrappers.
            if recursively_inline(cx, instance) {
                Some(FnAttribute::Inline)
            } else {
                Some(FnAttribute::AlwaysInline)
            }
        }
        InlineAttr::Hint => Some(FnAttribute::Inline),
        InlineAttr::Force { .. } => Some(FnAttribute::AlwaysInline),
        InlineAttr::Never => {
            if cx.sess().target.arch != Arch::AmdGpu {
                Some(FnAttribute::NoInline)
            } else {
                None
            }
        }
        InlineAttr::None => None,
    }
}

#[cfg(feature = "master")]
fn is_x86_interrupt<'tcx>(fn_abi: Option<&FnAbi<'tcx, ty::Ty<'tcx>>>) -> bool {
    matches!(
        fn_abi,
        Some(fn_abi) if matches!(fn_abi.conv, CanonAbi::Interrupt(InterruptKind::X86))
    )
}

/// Composite function which sets GCC attributes for function depending on its AST (`#[attribute]`)
/// attributes.
pub fn from_fn_attrs<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    #[cfg_attr(not(feature = "master"), expect(unused_variables))] func: Function<'gcc>,
    instance: ty::Instance<'tcx>,
    #[cfg_attr(not(feature = "master"), expect(unused_variables))] fn_abi: Option<
        &FnAbi<'tcx, ty::Ty<'tcx>>,
    >,
) {
    let codegen_fn_attrs = cx.tcx.codegen_instance_attrs(instance.def);

    #[cfg(feature = "master")]
    {
        let inline = if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::NAKED) {
            InlineAttr::Never
        } else if codegen_fn_attrs.inline == InlineAttr::None
            && instance.def.requires_inline(cx.tcx)
        {
            InlineAttr::Hint
        } else {
            codegen_fn_attrs.inline
        };
        // GCC drops `weak` from a function that is also `inline`, leaving the symbol strong, and
        // the linkage is what has to survive. `inline(never)` does not conflict.
        let inline = match inline {
            InlineAttr::Always | InlineAttr::Hint | InlineAttr::Force { .. }
                if codegen_fn_attrs.linkage.is_some_and(base::linkage_needs_weak_attribute) =>
            {
                InlineAttr::None
            }
            inline => inline,
        };
        if let Some(attr) = inline_attr(cx, inline, instance) {
            if let FnAttribute::AlwaysInline = attr {
                func.add_attribute(FnAttribute::Inline);
            }
            func.add_attribute(attr);
        }

        if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::COLD) {
            func.add_attribute(FnAttribute::Cold);
        }
        if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::FFI_PURE) {
            func.add_attribute(FnAttribute::Pure);
        }
        if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::FFI_CONST) {
            func.add_attribute(FnAttribute::Const);
        }
    }

    #[cfg(feature = "master")]
    let x86_interrupt = is_x86_interrupt(fn_abi);
    #[cfg(not(feature = "master"))]
    let x86_interrupt = false;

    let mut function_features = codegen_fn_attrs
        .target_features
        .iter()
        .map(|features| features.name.as_str())
        .flat_map(|feat| to_gcc_features(cx.tcx.sess, feat).into_iter())
        .chain(codegen_fn_attrs.instruction_set.iter().map(|x| match *x {
            InstructionSetAttr::ArmA32 => "-thumb-mode", // FIXME(antoyo): support removing feature.
            InstructionSetAttr::ArmT32 => "thumb-mode",
        }))
        .collect::<Vec<_>>();

    // FIXME(antoyo): cg_llvm adds global features to each function so that LTO keep them.
    // Check if GCC requires the same.
    let mut global_features = cx.tcx.global_backend_features(()).iter().map(|s| s.as_str());
    function_features.extend(&mut global_features);
    if x86_interrupt {
        // GCC does not preserve SSE, MMX, or x87 state in interrupt handlers and rejects
        // them whenever those instruction sets are enabled, even if the handler does not
        // emit such instructions. Restrict the function to general registers so the
        // interrupt attribute works with the default x86_64 target features.
        function_features.push("general-regs-only");
    }
    let target_features = function_features
        .iter()
        .filter_map(|feature| {
            // FIXME(antoyo): support soft-float.
            if feature.contains("soft-float") {
                return None;
            }

            if feature.starts_with('-') {
                Some(format!("no{}", feature))
            } else if let Some(stripped) = feature.strip_prefix('+') {
                Some(stripped.to_string())
            } else {
                Some(feature.to_string())
            }
        })
        .collect::<Vec<_>>()
        .join(",");
    if !target_features.is_empty() {
        #[cfg(feature = "master")]
        match cx.sess().target.arch {
            Arch::X86 | Arch::X86_64 | Arch::PowerPC => {
                func.add_attribute(FnAttribute::Target(&target_features))
            }
            // The target attribute is not supported on other targets in GCC.
            _ => (),
        }
    }
}
