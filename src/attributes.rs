#[cfg(feature = "master")]
use std::cell::{OnceCell, RefCell};

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
use rustc_middle::middle::codegen_fn_attrs::{CodegenFnAttrFlags, CodegenFnAttrs};
#[cfg(feature = "master")]
use rustc_middle::mir::interpret::{AllocId, GlobalAlloc, Scalar};
#[cfg(feature = "master")]
use rustc_middle::mir::visit::Visitor;
#[cfg(feature = "master")]
use rustc_middle::mir::{self, Location, TerminatorKind, traversal};
#[cfg(feature = "master")]
use rustc_middle::mono::{CollectionMode, MonoItem};
use rustc_middle::ty;
#[cfg(feature = "master")]
use rustc_middle::ty::adjustment::PointerCoercion;
#[cfg(feature = "master")]
use rustc_middle::ty::layout::FnAbiOf;
#[cfg(feature = "master")]
use rustc_session::config::OptLevel;
#[cfg(feature = "master")]
use rustc_span::def_id::DefId;
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
    definitions: OnceCell<FxHashMap<&'tcx str, ty::Instance<'tcx>>>,
}

/// How a function reaches something GCC could inline into it.
#[cfg(feature = "master")]
#[derive(Clone, Copy, PartialEq, Eq)]
enum Edge {
    Call,
    /// Only its address is taken; GCC may still turn that into a direct call.
    Address,
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

#[cfg(feature = "master")]
fn requests_forced_inline<'tcx>(tcx: ty::TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> bool {
    matches!(
        requested_inline(tcx, instance, &tcx.codegen_instance_attrs(instance.def)),
        InlineAttr::Always | InlineAttr::Force { .. }
    )
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

/// Functions defined in this unit, under every symbol GCC knows them by. A foreign declaration
/// naming one of these symbols is, as far as GCC is concerned, that function.
#[cfg(feature = "master")]
fn definitions<'a, 'gcc, 'tcx>(
    cx: &'a CodegenCx<'gcc, 'tcx>,
) -> &'a FxHashMap<&'tcx str, ty::Instance<'tcx>> {
    cx.inline_analysis.definitions.get_or_init(|| {
        let tcx = cx.tcx;
        let mut definitions = FxHashMap::default();
        for item in cx.codegen_unit.items().keys() {
            let MonoItem::Fn(instance) = *item else { continue };
            definitions.insert(tcx.symbol_name(instance).name, instance);
            // An EII implementation also gets a wrapper under the declaration's symbol, and
            // `add_function_aliases` annotates it with this same instance.
            let attrs = tcx.codegen_instance_attrs(instance.def);
            for &(alias, ..) in &attrs.foreign_item_symbol_aliases {
                definitions.insert(tcx.symbol_name(ty::Instance::mono(tcx, alias)).name, instance);
            }
        }
        definitions
    })
}

/// Functions whose code GCC could pull into `instance`: what it calls, and what it takes the
/// address of (fn pointers, vtables, statics), since GCC turns calls through a known address into
/// direct calls.
#[cfg(feature = "master")]
fn inline_edges<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    instance: ty::Instance<'tcx>,
) -> Vec<(ty::Instance<'tcx>, Edge)> {
    let tcx = cx.tcx;
    // Nothing to inline without a body. Monomorphizations we import from another crate count as
    // bodyless: querying them would also check them against the wrong target features.
    let has_body = match instance.def {
        ty::InstanceKind::Item(def_id) => tcx.is_mir_available(def_id),
        ty::InstanceKind::Intrinsic(_)
        | ty::InstanceKind::LlvmIntrinsic(_)
        | ty::InstanceKind::Virtual(..) => false,
        ty::InstanceKind::Shim(_) => true,
    };
    if !has_body || !tcx.should_codegen_locally(instance) {
        return Vec::new();
    }
    // The collector already resolved all of this, and reported its errors.
    let Ok((used, _)) = tcx.items_of_instance((instance, CollectionMode::UsedItems)) else {
        return Vec::new();
    };
    // The collector doesn't say which uses are calls, and skips foreign declarations.
    let body = tcx.instance_mir(instance.def);
    let mut refs = BodyRefs {
        tcx,
        instance,
        body,
        definitions: definitions(cx),
        calls: FxHashSet::default(),
        addresses: FxHashSet::default(),
        makes_vtables: false,
    };
    for (block, data) in traversal::mono_reachable(body, tcx, instance) {
        refs.visit_basic_block_data(block, data);
    }
    for item in used {
        match item.node {
            MonoItem::Fn(callee) => {
                if !refs.calls.contains(&callee) {
                    refs.addresses.insert(callee);
                }
            }
            MonoItem::Static(def_id) => {
                let mut pending = Vec::new();
                static_initializer(tcx, def_id, &mut pending);
                for function in allocated_fns(tcx, pending) {
                    refs.address_of(function);
                }
            }
            MonoItem::GlobalAsm(_) => {}
        }
    }
    // We don't work out which methods a new vtable holds, so with one around, anything might be
    // in it.
    if refs.makes_vtables {
        refs.addresses.extend(refs.calls.drain());
    }

    // A function that is both called and has its address taken counts as the latter.
    let calls = refs.calls.iter().filter(|&callee| !refs.addresses.contains(callee));
    let edges = calls
        .map(|&callee| (callee, Edge::Call))
        .chain(refs.addresses.iter().map(|&callee| (callee, Edge::Address)));
    let optimize = cx.sess().opts.optimize;
    edges.filter(|&(callee, _)| gcc_may_inline(tcx, callee, optimize)).collect()
}

/// What a body does that the collector doesn't tell us: which functions it calls directly and
/// which it takes the address of. Foreign declarations are mapped to what they name.
#[cfg(feature = "master")]
struct BodyRefs<'a, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &'tcx mir::Body<'tcx>,
    definitions: &'a FxHashMap<&'tcx str, ty::Instance<'tcx>>,
    calls: FxHashSet<ty::Instance<'tcx>>,
    addresses: FxHashSet<ty::Instance<'tcx>>,
    /// Whether the body coerces something to `dyn Trait`, creating a vtable.
    makes_vtables: bool,
}

#[cfg(feature = "master")]
impl<'a, 'tcx> BodyRefs<'a, 'tcx> {
    fn monomorphize<T: ty::TypeFoldable<ty::TyCtxt<'tcx>>>(&self, value: T) -> T {
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(self.tcx, value),
        )
    }

    fn resolve(&self, fn_ty: ty::Ty<'tcx>) -> Option<ty::Instance<'tcx>> {
        let ty::FnDef(def_id, args) = *self.monomorphize(fn_ty).kind() else { return None };
        let typing_env = ty::TypingEnv::fully_monomorphized();
        ty::Instance::try_resolve(self.tcx, typing_env, def_id, args.no_bound_vars()?).ok()?
    }

    /// The function GCC will see for `function`: the definition a foreign declaration names, or
    /// nothing if that isn't in this unit or we don't generate the function here.
    fn in_this_unit(&self, function: ty::Instance<'tcx>) -> Option<ty::Instance<'tcx>> {
        match function.def {
            ty::InstanceKind::Item(def_id) if self.tcx.is_foreign_item(def_id) => {
                let symbol = self.tcx.symbol_name(ty::Instance::mono(self.tcx, def_id)).name;
                self.definitions.get(symbol).copied()
            }
            _ => self.tcx.should_codegen_locally(function).then_some(function),
        }
    }

    fn address_of(&mut self, function: ty::Instance<'tcx>) {
        if let Some(function) = self.in_this_unit(function) {
            self.addresses.insert(function);
        }
    }
}

#[cfg(feature = "master")]
impl<'a, 'tcx> Visitor<'tcx> for BodyRefs<'a, 'tcx> {
    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { ref func, .. } | TerminatorKind::TailCall { ref func, .. } =
            terminator.kind
            && let Some(callee) = self.resolve(func.ty(self.body, self.tcx))
            && let Some(callee) = self.in_this_unit(callee)
        {
            self.calls.insert(callee);
        }
        self.super_terminator(terminator, location);
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        if let mir::Rvalue::Cast(mir::CastKind::PointerCoercion(coercion, _), ref operand, target) =
            *rvalue
        {
            let source = self.monomorphize(operand.ty(self.body, self.tcx));
            match (coercion, *source.kind()) {
                (PointerCoercion::ReifyFnPointer(_), ty::FnDef(def_id, args)) => {
                    if let Some(args) = args.no_bound_vars()
                        && let Some(function) =
                            ty::Instance::resolve_for_fn_ptr(self.tcx, typing_env, def_id, args)
                    {
                        self.address_of(function);
                    }
                }
                (PointerCoercion::ClosureFnPointer(_), ty::Closure(def_id, args)) => {
                    let kind = ty::ClosureKind::FnOnce;
                    self.address_of(ty::Instance::resolve_closure(self.tcx, def_id, args, kind));
                }
                (PointerCoercion::Unsize, _) => {
                    let target = self.monomorphize(target);
                    self.makes_vtables |= target.walk().any(|arg| {
                        arg.as_type().is_some_and(|ty| matches!(ty.kind(), ty::Dynamic(..)))
                    });
                }
                _ => {}
            }
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _: Location) {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let Ok(value) =
            self.monomorphize(constant.const_).eval(self.tcx, typing_env, constant.span)
        else {
            return;
        };
        let root = match value {
            mir::ConstValue::Scalar(Scalar::Ptr(ptr, _)) => ptr.provenance.alloc_id(),
            mir::ConstValue::Indirect { alloc_id, .. }
            | mir::ConstValue::Slice { alloc_id, .. } => alloc_id,
            mir::ConstValue::Scalar(Scalar::Int(_)) | mir::ConstValue::ZeroSized => return,
        };
        for function in allocated_fns(self.tcx, vec![root]) {
            self.address_of(function);
        }
    }
}

#[cfg(feature = "master")]
fn static_initializer(tcx: ty::TyCtxt<'_>, def_id: DefId, pending: &mut Vec<AllocId>) {
    if tcx.is_foreign_item(def_id) || !tcx.should_codegen_locally(ty::Instance::mono(tcx, def_id)) {
        return;
    }
    if let Ok(alloc) = tcx.eval_static_initializer(def_id) {
        pending.extend(alloc.inner().provenance().ptrs().values().map(|prov| prov.alloc_id()));
    }
}

/// Functions whose addresses are stored in these allocations, or in anything they point to.
/// GCC can fold loads from read-only data, so a call through a static fn table can become a
/// direct call.
#[cfg(feature = "master")]
fn allocated_fns<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    mut pending: Vec<AllocId>,
) -> Vec<ty::Instance<'tcx>> {
    let mut functions = Vec::new();
    let mut seen = FxHashSet::default();
    while let Some(alloc_id) = pending.pop() {
        if !seen.insert(alloc_id) {
            continue;
        }
        match tcx.global_alloc(alloc_id) {
            GlobalAlloc::Function { instance, .. } => functions.push(instance),
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
            GlobalAlloc::Static(nested) => static_initializer(tcx, nested, &mut pending),
            GlobalAlloc::TypeId { .. } => {}
        }
    }
    functions
}

/// Whether GCC could end up inlining `root` into itself.
///
/// Classifies everything reachable from `root` at once. Only functions on a cycle are affected:
/// once they lose `always_inline`, callers that merely reach the cycle can keep it.
#[cfg(feature = "master")]
fn in_inline_cycle<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, root: ty::Instance<'tcx>) -> bool {
    if let Some(&in_cycle) = cx.inline_analysis.in_cycle.borrow().get(&root) {
        return in_cycle;
    }

    // Collect the part of the graph reachable from `root` that hasn't been classified yet.
    // Classified functions can be left out: their SCC is complete, so nothing new can join it.
    let mut nodes = vec![root];
    let mut index = FxHashMap::from_iter([(root, 0)]);
    let mut edges = Vec::new();
    {
        let classified = cx.inline_analysis.in_cycle.borrow();
        let mut caller = 0;
        while let Some(&instance) = nodes.get(caller) {
            for (callee, edge) in inline_edges(cx, instance) {
                if classified.contains_key(&callee) {
                    continue;
                }
                let callee = *index.entry(callee).or_insert_with(|| {
                    nodes.push(callee);
                    nodes.len() - 1
                });
                edges.push((caller, callee, edge));
            }
            caller += 1;
        }
    }
    let forced: Vec<bool> =
        nodes.iter().map(|&node| requests_forced_inline(cx.tcx, node)).collect();

    // GCC rejects any cycle made only of `always_inline` functions. A plain function in the middle
    // breaks it up as long as everything is a direct call: GCC inlines those early and never
    // tries to inline the plain function into itself.
    let forced_edges = edges
        .iter()
        .filter(|&&(from, to, _)| forced[from] && forced[to])
        .map(|&(from, to, _)| (from, to));
    let mut in_cycle = in_nontrivial_scc(nodes.len(), forced_edges.collect());

    // When optimizing, GCC also inlines plain functions, and can then resolve an address taken in
    // one of them into a direct call. If that call leads back to a function it was inlined into,
    // GCC rejects it, so the function whose address is taken loses `always_inline`.
    if cx.sess().opts.optimize != OptLevel::No {
        let all = Sccs::<usize, usize>::new(&VecGraph::<usize>::new(
            nodes.len(),
            edges.iter().map(|&(from, to, _)| (from, to)).collect(),
        ));
        for &(from, to, edge) in &edges {
            if edge == Edge::Address && forced[to] && all.scc(from) == all.scc(to) {
                in_cycle[to] = true;
            }
        }
    }

    let mut classified = cx.inline_analysis.in_cycle.borrow_mut();
    classified.extend(nodes.iter().copied().zip(in_cycle.iter().copied()));
    in_cycle[0]
}

/// Which nodes lie on a cycle: a strongly connected component with more than one node, or a
/// node with an edge to itself.
#[cfg(feature = "master")]
fn in_nontrivial_scc(num_nodes: usize, edges: Vec<(usize, usize)>) -> Vec<bool> {
    let mut in_cycle = vec![false; num_nodes];
    for &(from, to) in &edges {
        in_cycle[from] |= from == to;
    }
    let sccs = Sccs::<usize, usize>::new(&VecGraph::<usize>::new(num_nodes, edges));
    let mut sizes = vec![0usize; sccs.num_sccs()];
    for node in 0..num_nodes {
        sizes[sccs.scc(node)] += 1;
    }
    for (node, in_cycle) in in_cycle.iter_mut().enumerate() {
        *in_cycle |= sizes[sccs.scc(node)] > 1;
    }
    in_cycle
}

/// `always_inline` functions that an `x86-interrupt` handler in this unit could inline. Handlers
/// are built with `general-regs-only`, and GCC refuses to inline normally-built code into them.
#[cfg(feature = "master")]
fn interrupt_callees<'a, 'gcc, 'tcx>(
    cx: &'a CodegenCx<'gcc, 'tcx>,
) -> &'a FxHashSet<ty::Instance<'tcx>> {
    cx.inline_analysis.interrupt_callees.get_or_init(|| {
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
            .flat_map(|handler| inline_edges(cx, handler))
            .map(|(callee, _)| callee)
            .filter(|&callee| requests_forced_inline(cx.tcx, callee))
            .collect()
    })
}

/// Get GCC attribute for the provided inline heuristic, attached to `instance`.
#[cfg(feature = "master")]
#[inline]
fn inline_attr<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    inline: InlineAttr,
    instance: ty::Instance<'tcx>,
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
                && !in_inline_cycle(cx, instance);
            Some(if can_inline { FnAttribute::AlwaysInline } else { FnAttribute::Inline })
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
        if let Some(attr) = inline_attr(cx, inline, instance, body, fn_abi) {
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
