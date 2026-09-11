#[cfg(feature = "master")]
use std::cell::{OnceCell, RefCell};
#[cfg(feature = "master")]
use std::iter;

#[cfg(feature = "master")]
use gccjit::FnAttribute;
use gccjit::Function;
#[cfg(feature = "master")]
use rustc_abi::{CanonAbi, InterruptKind};
#[cfg(feature = "master")]
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
#[cfg(feature = "master")]
use rustc_data_structures::graph::scc::Sccs;
#[cfg(feature = "master")]
use rustc_data_structures::graph::vec_graph::VecGraph;
#[cfg(feature = "master")]
use rustc_hir::attrs::InlineAttr;
use rustc_hir::attrs::InstructionSetAttr;
#[cfg(feature = "master")]
use rustc_hir::def::DefKind;
#[cfg(feature = "master")]
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};
#[cfg(feature = "master")]
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc};
#[cfg(feature = "master")]
use rustc_middle::mono::{CollectionMode, MonoItem};
use rustc_middle::ty;
#[cfg(feature = "master")]
use rustc_middle::ty::layout::FnAbiOf;
#[cfg(feature = "master")]
use rustc_session::config::OptLevel;
#[cfg(feature = "master")]
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_target::callconv::FnAbi;
#[cfg(feature = "master")]
use rustc_target::spec::Arch;

#[cfg(feature = "master")]
use crate::base;
use crate::context::CodegenCx;
use crate::gcc_util::to_gcc_features;

/// Whether the GCC function being annotated gets a body in this codegen unit.
#[derive(Clone, Copy)]
pub enum FnBody {
    Defined,
    Declared,
}

/// What we need to know, per codegen unit, to decide where `always_inline` is safe.
#[cfg(feature = "master")]
#[derive(Default)]
pub struct InlineAnalysis<'tcx> {
    /// Whether GCC could end up inlining the instance into itself.
    in_cycle: RefCell<FxHashMap<ty::Instance<'tcx>, bool>>,
    interrupt_callees: OnceCell<FxHashSet<ty::Instance<'tcx>>>,
    foreign_imports: OnceCell<FxHashSet<&'tcx str>>,
}

/// The inlining we ask GCC for, before checking whether it can honor `always_inline`.
#[cfg(feature = "master")]
fn requested_inline<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    attrs: &CodegenFnAttrs,
) -> InlineAttr {
    let inline = if attrs.flags.contains(CodegenFnAttrFlags::NAKED) {
        InlineAttr::Never
    } else if attrs.inline == InlineAttr::None && instance.def.requires_inline(tcx) {
        InlineAttr::Hint
    } else {
        attrs.inline
    };
    // GCC drops `weak` from a function that is also `inline`, leaving the symbol strong, and
    // the linkage is what has to survive. `inline(never)` does not conflict.
    match inline {
        InlineAttr::Always | InlineAttr::Hint | InlineAttr::Force { .. }
            if attrs.linkage.is_some_and(base::linkage_needs_weak_attribute) =>
        {
            InlineAttr::None
        }
        inline => inline,
    }
}

/// Whether GCC may inline `instance` into a caller. At `-O0` it only inlines `always_inline`
/// functions; above that, anything not marked `noinline`.
#[cfg(feature = "master")]
fn gcc_may_inline<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    optimize: OptLevel,
) -> bool {
    match requested_inline(tcx, instance, &tcx.codegen_instance_attrs(instance.def)) {
        InlineAttr::Always | InlineAttr::Force { .. } => true,
        InlineAttr::Never => false,
        InlineAttr::Hint | InlineAttr::None => optimize != OptLevel::No,
    }
}

/// Functions whose code GCC could pull into `instance`: its callees, plus anything whose address
/// it takes (fn pointers, vtables, statics), since GCC turns calls through a known address into
/// direct calls and inlines those too.
#[cfg(feature = "master")]
fn inline_edges<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    optimize: OptLevel,
) -> Vec<ty::Instance<'tcx>> {
    // Nothing to inline without a body. Monomorphizations we import from another crate count as
    // bodyless: querying them would also check them against the wrong target features.
    let has_body = match instance.def {
        ty::InstanceKind::Item(def_id) => tcx.is_mir_available(def_id),
        ty::InstanceKind::Intrinsic(_)
        | ty::InstanceKind::LlvmIntrinsic(_)
        | ty::InstanceKind::Virtual(..) => false,
        ty::InstanceKind::Shim(_) => true,
    };
    let mut edges = Vec::new();
    if !has_body || !tcx.should_codegen_locally(instance) {
        return edges;
    }
    // The collector already resolved all of this, and reported its errors.
    let Ok((used, _)) = tcx.items_of_instance((instance, CollectionMode::UsedItems)) else {
        return edges;
    };
    for item in used {
        match item.node {
            MonoItem::Fn(callee) => edges.push(callee),
            MonoItem::Static(def_id) => static_fn_addresses(tcx, def_id, &mut edges),
            MonoItem::GlobalAsm(_) => {}
        }
    }
    edges.retain(|&callee| gcc_may_inline(tcx, callee, optimize));
    edges
}

/// Functions reachable through the initializer of `def_id`. GCC can fold loads from read-only
/// data, so a call through a static fn table can become a direct call.
#[cfg(feature = "master")]
fn static_fn_addresses<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: DefId,
    out: &mut Vec<ty::Instance<'tcx>>,
) {
    fn initializer_ptrs(tcx: ty::TyCtxt<'_>, def_id: DefId, pending: &mut Vec<AllocId>) {
        if tcx.is_foreign_item(def_id)
            || !tcx.should_codegen_locally(ty::Instance::mono(tcx, def_id))
        {
            return;
        }
        if let Ok(alloc) = tcx.eval_static_initializer(def_id) {
            pending.extend(alloc.inner().provenance().ptrs().values().map(|prov| prov.alloc_id()));
        }
    }

    let mut pending = Vec::new();
    initializer_ptrs(tcx, def_id, &mut pending);
    let mut seen = FxHashSet::default();
    while let Some(alloc_id) = pending.pop() {
        if !seen.insert(alloc_id) {
            continue;
        }
        match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance, .. } => {
                if tcx.should_codegen_locally(instance) {
                    out.push(instance);
                }
            }
            GlobalAlloc::Memory(alloc) => pending
                .extend(alloc.inner().provenance().ptrs().values().map(|prov| prov.alloc_id())),
            GlobalAlloc::VTable(ty, dyn_ty) => pending.push(
                tcx.vtable_allocation((
                    ty,
                    dyn_ty
                        .principal()
                        .map(|principal| tcx.instantiate_bound_regions_with_erased(principal)),
                )),
            ),
            GlobalAlloc::Static(nested) => initializer_ptrs(tcx, nested, &mut pending),
            GlobalAlloc::TypeId { .. } => {}
        }
    }
}

/// Whether GCC could end up inlining `root` into itself.
///
/// Classifies everything reachable from `root` at once. Only functions on a cycle are affected:
/// once they lose `always_inline`, callers that merely reach the cycle can keep it. When
/// optimizing, cycles through plain helpers count too, since GCC may inline those as well.
#[cfg(feature = "master")]
fn in_inline_cycle<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, root: ty::Instance<'tcx>) -> bool {
    if let Some(&in_cycle) = cx.inline_analysis.in_cycle.borrow().get(&root) {
        return in_cycle;
    }

    // Collect the part of the graph reachable from `root` that hasn't been classified yet.
    // Classified functions can be left out: their SCC is complete, so nothing new can join it.
    let optimize = cx.sess().opts.optimize;
    let mut nodes = vec![root];
    let mut index = FxHashMap::from_iter([(root, 0)]);
    let mut edges = Vec::new();
    {
        let classified = cx.inline_analysis.in_cycle.borrow();
        let mut caller = 0;
        while let Some(&instance) = nodes.get(caller) {
            for callee in inline_edges(cx.tcx, instance, optimize) {
                if classified.contains_key(&callee) {
                    continue;
                }
                let callee = *index.entry(callee).or_insert_with(|| {
                    nodes.push(callee);
                    nodes.len() - 1
                });
                edges.push((caller, callee));
            }
            caller += 1;
        }
    }

    let mut calls_itself = vec![false; nodes.len()];
    for &(caller, callee) in &edges {
        calls_itself[caller] |= caller == callee;
    }
    let sccs: Sccs<usize, usize> = Sccs::new(&VecGraph::<usize>::new(nodes.len(), edges));
    let mut scc_sizes = vec![0usize; sccs.num_sccs()];
    for node in 0..nodes.len() {
        scc_sizes[sccs.scc(node)] += 1;
    }

    let mut in_cycle = cx.inline_analysis.in_cycle.borrow_mut();
    for (node, &instance) in nodes.iter().enumerate() {
        in_cycle.insert(instance, calls_itself[node] || scc_sizes[sccs.scc(node)] > 1);
    }
    in_cycle[&root]
}

/// `always_inline` functions that an `x86-interrupt` handler in this unit could inline. Handlers
/// are built with `general-regs-only`, and GCC refuses to inline normally-built code into them.
#[cfg(feature = "master")]
fn interrupt_callees<'a, 'gcc, 'tcx>(
    cx: &'a CodegenCx<'gcc, 'tcx>,
) -> &'a FxHashSet<ty::Instance<'tcx>> {
    cx.inline_analysis.interrupt_callees.get_or_init(|| {
        let optimize = cx.sess().opts.optimize;
        cx.codegen_unit
            .items()
            .keys()
            .filter_map(|item| match *item {
                MonoItem::Fn(instance) => Some(instance),
                MonoItem::Static(_) | MonoItem::GlobalAsm(_) => None,
            })
            .filter(|&instance| {
                is_x86_interrupt(Some(cx.fn_abi_of_instance(instance, ty::List::empty())))
            })
            .flat_map(|handler| inline_edges(cx.tcx, handler, optimize))
            .filter(|&callee| {
                matches!(
                    requested_inline(cx.tcx, callee, &cx.tcx.codegen_instance_attrs(callee.def)),
                    InlineAttr::Always | InlineAttr::Force { .. }
                )
            })
            .collect()
    })
}

/// Whether some foreign declaration (`extern` block item or EII declaration) can call `instance`.
/// GCC sees such a call as a direct call to the definition; the Rust call graph doesn't see it.
#[cfg(feature = "master")]
fn called_through_foreign_decl<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    instance: ty::Instance<'tcx>,
    attrs: &CodegenFnAttrs,
) -> bool {
    // An EII implementation is always reachable from its declaration, via the forwarding
    // wrapper that `add_function_aliases` annotates with this same instance.
    if !attrs.foreign_item_symbol_aliases.is_empty() {
        return true;
    }
    if !attrs.contains_extern_indicator() {
        return false;
    }
    let tcx = cx.tcx;
    let foreign_imports = cx.inline_analysis.foreign_imports.get_or_init(|| {
        iter::once(LOCAL_CRATE)
            .chain(tcx.crates(()).iter().copied())
            .flat_map(|krate| tcx.foreign_modules(krate).values())
            .flat_map(|module| &module.foreign_items)
            .filter(|&&def_id| tcx.def_kind(def_id) == DefKind::Fn)
            .map(|&def_id| tcx.symbol_name(ty::Instance::mono(tcx, def_id)).name)
            .collect()
    });
    foreign_imports.contains(tcx.symbol_name(instance).name)
}

/// Get GCC attribute for the provided inline heuristic, attached to `instance`.
#[cfg(feature = "master")]
#[inline]
fn inline_attr<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    inline: InlineAttr,
    instance: ty::Instance<'tcx>,
    attrs: &CodegenFnAttrs,
    body: FnBody,
    fn_abi: Option<&FnAbi<'tcx, ty::Ty<'tcx>>>,
) -> Option<FnAttribute<'gcc>> {
    match inline {
        InlineAttr::Always | InlineAttr::Force { .. } => {
            // `always_inline` is *not* a hint: GCC fails the build when it can't inline, so only
            // ask for it when it can.
            let can_inline = matches!(body, FnBody::Defined)
                // GCC never inlines functions that use va_arg.
                && !fn_abi.is_some_and(|fn_abi| fn_abi.c_variadic)
                && !interrupt_callees(cx).contains(&instance)
                && !called_through_foreign_decl(cx, instance, attrs)
                // The MIR inliner already rejects `#[rustc_force_inline]` cycles.
                && (matches!(inline, InlineAttr::Force { .. }) || !in_inline_cycle(cx, instance));
            if can_inline { Some(FnAttribute::AlwaysInline) } else { Some(FnAttribute::Inline) }
        }
        InlineAttr::Hint => Some(FnAttribute::Inline),
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
    #[cfg_attr(not(feature = "master"), expect(unused_variables))] body: FnBody,
    #[cfg_attr(not(feature = "master"), expect(unused_variables))] fn_abi: Option<
        &FnAbi<'tcx, ty::Ty<'tcx>>,
    >,
) {
    let codegen_fn_attrs = cx.tcx.codegen_instance_attrs(instance.def);

    #[cfg(feature = "master")]
    {
        let inline = requested_inline(cx.tcx, instance, &codegen_fn_attrs);
        if let Some(attr) = inline_attr(cx, inline, instance, &codegen_fn_attrs, body, fn_abi) {
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
        .flat_map(|feat| to_gcc_features(&cx.tcx.sess.target, feat).into_iter())
        .chain(codegen_fn_attrs.instruction_set.iter().map(|x| match *x {
            InstructionSetAttr::ArmA32 => "-thumb-mode", // FIXME(antoyo): support removing feature.
            InstructionSetAttr::ArmT32 => "thumb-mode",
        }))
        .collect::<Vec<_>>();

    // FIXME(antoyo): cg_llvm adds global features to each function so that LTO keep them.
    // Check if GCC requires the same.
    let mut global_features = cx.tcx.sess.global_backend_features.iter().map(|s| s.as_str());
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
