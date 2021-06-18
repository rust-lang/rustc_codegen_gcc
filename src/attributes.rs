use gccjit::{Function, InlineMode};
use rustc_attr::InlineAttr;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::ty::{self, layout::HasTyCtxt};

use crate::context::CodegenCx;

/// Mark GCC function to use provided inline heuristic.
#[inline]
fn inline<'gcc>(cx: &CodegenCx<'gcc, '_>, function: Function<'gcc>, inline: InlineAttr) {
    use self::InlineAttr::*;
    match inline {
        Hint => function.set_inline_mode(InlineMode::Inline),
        Always => function.set_inline_mode(InlineMode::AlwaysInline),
        Never => {
            if cx.tcx().sess.target.arch != "amdgpu" {
                function.set_inline_mode(InlineMode::NoInline);
            }
        }
        None => {}
    };
}

/// Composite function which sets LLVM attributes for function depending on its AST (`#[attribute]`)
/// attributes.
pub fn from_fn_attrs<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, func: Function<'gcc>, instance: ty::Instance<'tcx>) {
    let codegen_fn_attrs = cx.tcx.codegen_fn_attrs(instance.def_id());

    /*match codegen_fn_attrs.optimize {
        OptimizeAttr::None => {
            default_optimisation_attrs(cx.tcx.sess, func);
        }
        OptimizeAttr::Speed => {
            llvm::Attribute::MinSize.unapply_llfn(Function, func);
            llvm::Attribute::OptimizeForSize.unapply_llfn(Function, func);
            llvm::Attribute::OptimizeNone.unapply_llfn(Function, func);
        }
        OptimizeAttr::Size => {
            llvm::Attribute::MinSize.apply_llfn(Function, func);
            llvm::Attribute::OptimizeForSize.apply_llfn(Function, func);
            llvm::Attribute::OptimizeNone.unapply_llfn(Function, func);
        }
    }*/

    let inline_attr =
        if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::NAKED) {
            InlineAttr::Never
        }
        else if codegen_fn_attrs.inline == InlineAttr::None && instance.def.requires_inline(cx.tcx) {
            InlineAttr::Hint
        }
        else {
            codegen_fn_attrs.inline
        };
    inline(cx, func, inline_attr);

    // The `uwtable` attribute according to LLVM is:
    //
    //     This attribute indicates that the ABI being targeted requires that an
    //     unwind table entry be produced for this function even if we can show
    //     that no exceptions passes by it. This is normally the case for the
    //     ELF x86-64 abi, but it can be disabled for some compilation units.
    //
    // Typically when we're compiling with `-C panic=abort` (which implies this
    // `no_landing_pads` check) we don't need `uwtable` because we can't
    // generate any exceptions! On Windows, however, exceptions include other
    // events such as illegal instructions, segfaults, etc. This means that on
    // Windows we end up still needing the `uwtable` attribute even if the `-C
    // panic=abort` flag is passed.
    //
    // You can also find more info on why Windows always requires uwtables here:
    //      https://bugzilla.mozilla.org/show_bug.cgi?id=1302078
    /*if cx.sess().must_emit_unwind_tables() {
        attributes::emit_uwtable(func, true);
    }

    // FIXME: none of these three functions interact with source level attributes.
    set_frame_pointer_elimination(cx, func);
    set_instrument_function(cx, func);
    set_probestack(cx, func);

    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::COLD) {
        Attribute::Cold.apply_llfn(Function, func);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::FFI_RETURNS_TWICE) {
        Attribute::ReturnsTwice.apply_llfn(Function, func);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::FFI_PURE) {
        Attribute::ReadOnly.apply_llfn(Function, func);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::FFI_CONST) {
        Attribute::ReadNone.apply_llfn(Function, func);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::NAKED) {
        naked(func, true);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::ALLOCATOR) {
        Attribute::NoAlias.apply_llfn(llvm::AttributePlace::ReturnValue, func);
    }
    if codegen_fn_attrs.flags.contains(CodegenFnAttrFlags::CMSE_NONSECURE_ENTRY) {
        llvm::AddFunctionAttrString(func, Function, cstr!("cmse_nonsecure_entry"));
    }
    if let Some(align) = codegen_fn_attrs.alignment {
        llvm::set_alignment(func, align as usize);
    }
    sanitize(cx, codegen_fn_attrs.no_sanitize, func);

    // Always annotate functions with the target-cpu they are compiled for.
    // Without this, ThinLTO won't inline Rust functions into Clang generated
    // functions (because Clang annotates functions this way too).
    apply_target_cpu_attr(cx, func);
    // tune-cpu is only conveyed through the attribute for our purpose.
    // The target doesn't care; the subtarget reads our attribute.
    apply_tune_cpu_attr(cx, func);

    let mut function_features = codegen_fn_attrs
        .target_features
        .iter()
        .map(|f| {
            let feature = &f.as_str();
            format!("+{}", llvm_util::to_llvm_feature(cx.tcx.sess, feature))
        })
        .chain(codegen_fn_attrs.instruction_set.iter().map(|x| match x {
            InstructionSetAttr::ArmA32 => "-thumb-mode".to_string(),
            InstructionSetAttr::ArmT32 => "+thumb-mode".to_string(),
        }))
        .collect::<Vec<String>>();

    if cx.tcx.sess.target.is_like_wasm {
        // If this function is an import from the environment but the wasm
        // import has a specific module/name, apply them here.
        if let Some(module) = wasm_import_module(cx.tcx, instance.def_id()) {
            llvm::AddFunctionAttrStringValue(
                func,
                llvm::AttributePlace::Function,
                cstr!("wasm-import-module"),
                &module,
            );

            let name =
                codegen_fn_attrs.link_name.unwrap_or_else(|| cx.tcx.item_name(instance.def_id()));
            let name = CString::new(&name.as_str()[..]).unwrap();
            llvm::AddFunctionAttrStringValue(
                func,
                llvm::AttributePlace::Function,
                cstr!("wasm-import-name"),
                &name,
            );
        }

        // The `"wasm"` abi on wasm targets automatically enables the
        // `+multivalue` feature because the purpose of the wasm abi is to match
        // the WebAssembly specification, which has this feature. This won't be
        // needed when LLVM enables this `multivalue` feature by default.
        if !cx.tcx.is_closure(instance.def_id()) {
            let abi = cx.tcx.fn_sig(instance.def_id()).abi();
            if abi == Abi::Wasm {
                function_features.push("+multivalue".to_string());
            }
        }
    }

    if !function_features.is_empty() {
        let mut global_features = llvm_util::llvm_global_features(cx.tcx.sess);
        global_features.extend(function_features.into_iter());
        let features = global_features.join(",");
        let val = CString::new(features).unwrap();
        llvm::AddFunctionAttrStringValue(
            func,
            llvm::AttributePlace::Function,
            cstr!("target-features"),
            &val,
        );
    }*/
}
