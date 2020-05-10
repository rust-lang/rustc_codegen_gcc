use rustc_codegen_ssa::traits::{DeclareMethods, PreDefineMethods};
use rustc_middle::mir::mono::{Linkage, Visibility};
use rustc_middle::ty::Instance;
use rustc_middle::ty::TypeFoldable;
use rustc_middle::ty::layout::FnAbiExt;
use rustc_span::def_id::DefId;
use rustc_target::abi::LayoutOf;
use rustc_target::abi::call::FnAbi;

use crate::base;
use crate::context::CodegenCx;
use crate::type_of::LayoutGccExt;

impl<'gcc, 'tcx> PreDefineMethods<'tcx> for CodegenCx<'gcc, 'tcx> {
    fn predefine_static(&self, def_id: DefId, linkage: Linkage, visibility: Visibility, symbol_name: &str) {
        let instance = Instance::mono(self.tcx, def_id);
        let ty = instance.monomorphic_ty(self.tcx);
        let gcc_type = self.layout_of(ty).gcc_type(self, true);

        let g = self.define_global(symbol_name, gcc_type).unwrap_or_else(|| {
            self.sess().span_fatal(
                self.tcx.def_span(def_id),
                &format!("symbol `{}` is already defined", symbol_name),
            )
        });

        // TODO
        /*unsafe {
            llvm::LLVMRustSetLinkage(g, base::linkage_to_llvm(linkage));
            llvm::LLVMRustSetVisibility(g, base::visibility_to_llvm(visibility));
        }*/

        self.instances.borrow_mut().insert(instance, g);
    }

    fn predefine_fn(&self, instance: Instance<'tcx>, linkage: Linkage, visibility: Visibility, symbol_name: &str) {
        assert!(!instance.substs.needs_infer() && !instance.substs.has_param_types_or_consts());

        let fn_abi = FnAbi::of_instance(self, instance, &[]);
        self.linkage.set(base::linkage_to_gcc(linkage));
        let decl = self.declare_fn(symbol_name, &fn_abi);
        let attrs = self.tcx.codegen_fn_attrs(instance.def_id());
        //base::set_link_section(decl, &attrs);
        /*if linkage == Linkage::LinkOnceODR || linkage == Linkage::WeakODR {
            llvm::SetUniqueComdat(self.llmod, decl);
        }*/

        //debug!("predefine_fn: instance = {:?}", instance);

        // TODO: use inline attribute from there in linkage.set() above:
        //attributes::from_fn_attrs(self, decl, instance);

        //self.instances.borrow_mut().insert(instance, decl);
    }
}
