use gccjit::{FunctionType, RValue};
use rustc_codegen_ssa::mir::debuginfo::{FunctionDebugContext, VariableKind};
use rustc_codegen_ssa::traits::{BuilderMethods, DebugInfoBuilderMethods, DebugInfoMethods};
use rustc_middle::mir::Body;
use rustc_middle::ty::{Instance, Ty};
use rustc_span::{SourceFile, Span, Symbol};
use rustc_span::def_id::{CrateNum, LOCAL_CRATE};
use rustc_target::abi::Size;
use rustc_target::abi::call::FnAbi;

use crate::create_function_calling_initializers;
use crate::builder::Builder;
use crate::context::{CodegenCx, unit_name};
use crate::declare::mangle_name;

impl<'a, 'gcc, 'tcx> DebugInfoBuilderMethods for Builder<'a, 'gcc, 'tcx> {
    // FIXME(eddyb) find a common convention for all of the debuginfo-related
    // names (choose between `dbg`, `debug`, `debuginfo`, `debug_info` etc.).
    fn dbg_var_addr(&mut self, dbg_var: Self::DIVariable, scope_metadata: Self::DIScope, variable_alloca: Self::Value, direct_offset: Size, indirect_offsets: &[Size], span: Span) {
        unimplemented!();
        /*let cx = self.cx();

        // Convert the direct and indirect offsets to address ops.
        // FIXME(eddyb) use `const`s instead of getting the values via FFI,
        // the values should match the ones in the DWARF standard anyway.
        let op_deref = || unsafe { llvm::LLVMRustDIBuilderCreateOpDeref() };
        let op_plus_uconst = || unsafe { llvm::LLVMRustDIBuilderCreateOpPlusUconst() };
        let mut addr_ops = SmallVec::<[_; 8]>::new();

        if direct_offset.bytes() > 0 {
            addr_ops.push(op_plus_uconst());
            addr_ops.push(direct_offset.bytes() as i64);
        }
        for &offset in indirect_offsets {
            addr_ops.push(op_deref());
            if offset.bytes() > 0 {
                addr_ops.push(op_plus_uconst());
                addr_ops.push(offset.bytes() as i64);
            }
        }

        // FIXME(eddyb) maybe this information could be extracted from `dbg_var`,
        // to avoid having to pass it down in both places?
        // NB: `var` doesn't seem to know about the column, so that's a limitation.
        let dbg_loc = cx.create_debug_loc(scope_metadata, span);
        unsafe {
            // FIXME(eddyb) replace `llvm.dbg.declare` with `llvm.dbg.addr`.
            llvm::LLVMRustDIBuilderInsertDeclareAtEnd(
                DIB(cx),
                variable_alloca,
                dbg_var,
                addr_ops.as_ptr(),
                addr_ops.len() as c_uint,
                dbg_loc,
                self.llbb(),
            );
        }*/
    }

    fn set_source_location(&mut self, scope: Self::DIScope, span: Span) {
        unimplemented!();
        /*debug!("set_source_location: {}", self.sess().source_map().span_to_string(span));

        let dbg_loc = self.cx().create_debug_loc(scope, span);

        unsafe {
            llvm::LLVMSetCurrentDebugLocation(self.llbuilder, dbg_loc);
        }*/
    }

    fn insert_reference_to_gdb_debug_scripts_section_global(&mut self) {
        // TODO: replace with gcc_jit_context_new_global_with_initializer() if it's added:
        // https://gcc.gnu.org/pipermail/jit/2020q3/001225.html
        //
        // Call the function to initialize global values here.
        // We assume this is only called for the main function.
        use std::iter;

        for crate_num in self.cx.tcx.all_crate_nums(LOCAL_CRATE).iter().copied().chain(iter::once(LOCAL_CRATE)) {
            // FIXME: better way to find if a crate is of proc-macro type?
            if self.cx.tcx.proc_macro_decls_static(crate_num).is_none() {
                // NOTE: proc-macro crates are not included in the executable, so don't call their
                // initialization routine.
                let initializer_name = format!("__gccGlobalCrateInit{}", self.cx.tcx.crate_name(crate_num));
                let codegen_init_func = self.context.new_function(None, FunctionType::Extern, self.context.new_type::<()>(), &[],
                initializer_name, false);
                self.llbb().add_eval(None, self.context.new_call(None, codegen_init_func, &[]));
            }
        }

        // TODO
        //gdb::insert_reference_to_gdb_debug_scripts_section_global(self)
    }

    fn set_var_name(&mut self, value: RValue<'gcc>, name: &str) {
        unimplemented!();
        // Avoid wasting time if LLVM value names aren't even enabled.
        /*if self.sess().fewer_names() {
            return;
        }

        // Only function parameters and instructions are local to a function,
        // don't change the name of anything else (e.g. globals).
        let param_or_inst = unsafe {
            llvm::LLVMIsAArgument(value).is_some() || llvm::LLVMIsAInstruction(value).is_some()
        };
        if !param_or_inst {
            return;
        }

        // Avoid replacing the name if it already exists.
        // While we could combine the names somehow, it'd
        // get noisy quick, and the usefulness is dubious.
        if llvm::get_value_name(value).is_empty() {
            llvm::set_value_name(value, name.as_bytes());
        }*/
    }
}

impl<'gcc, 'tcx> DebugInfoMethods<'tcx> for CodegenCx<'gcc, 'tcx> {
    fn create_vtable_metadata(&self, ty: Ty<'tcx>, vtable: Self::Value) {
        //metadata::create_vtable_metadata(self, ty, vtable)
    }

    fn create_function_debug_context<'body>(&self, instance: Instance<'tcx>, fn_abi: &FnAbi<'tcx, Ty<'tcx>>, llfn: Self::Function, mir: &Body<'body>) -> Option<FunctionDebugContext<Self::DIScope>> {
        // TODO
        None
    }

    fn extend_scope_to_file(&self, scope_metadata: Self::DIScope, file: &SourceFile, defining_crate: CrateNum) -> Self::DIScope {
        unimplemented!();
    }

    fn debuginfo_finalize(&self) {
        //unimplemented!();
    }

    fn create_dbg_var(&self, dbg_context: &FunctionDebugContext<Self::DIScope>, variable_name: Symbol, variable_type: Ty<'tcx>, scope_metadata: Self::DIScope, variable_kind: VariableKind, span: Span) -> Self::DIVariable {
        unimplemented!();
    }
}
