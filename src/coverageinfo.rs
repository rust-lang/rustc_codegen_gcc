use rustc_codegen_ssa::traits::{CoverageInfoBuilderMethods, CoverageInfoMethods};
use rustc_middle::mir::coverage::{
    CodeRegion,
    CounterValueReference,
    ExpressionOperandId,
    InjectedExpressionIndex,
    Op,
};
use rustc_middle::ty::Instance;

use crate::builder::Builder;
use crate::context::CodegenCx;

impl<'a, 'gcc, 'tcx> CoverageInfoBuilderMethods<'tcx> for Builder<'a, 'gcc, 'tcx> {
    /// Calls llvm::createPGOFuncNameVar() with the given function instance's mangled function name.
    /// The LLVM API returns an llvm::GlobalVariable containing the function name, with the specific
    /// variable name and linkage required by LLVM InstrProf source-based coverage instrumentation.
    fn create_pgo_func_name_var(&self, instance: Instance<'tcx>) -> Self::Value {
        unimplemented!();
        /*let llfn = self.cx.get_fn(instance);
        let mangled_fn_name = CString::new(self.tcx.symbol_name(instance).name)
            .expect("error converting function name to C string");
        unsafe { llvm::LLVMRustCoverageCreatePGOFuncNameVar(llfn, mangled_fn_name.as_ptr()) }*/
    }

    fn add_counter_region(&mut self, instance: Instance<'tcx>, function_source_hash: u64, id: CounterValueReference, region: CodeRegion) -> bool {
        /*if let Some(coverage_context) = self.coverage_context() {
            debug!(
                "adding counter to coverage_regions: instance={:?}, function_source_hash={}, id={:?}, \
                at {:?}",
                instance, function_source_hash, id, region,
            );
            let mut coverage_regions = coverage_context.function_coverage_map.borrow_mut();
            coverage_regions
                .entry(instance)
                .or_insert_with(|| FunctionCoverage::new(self.tcx, instance))
                .add_counter(function_source_hash, id, region);
            true
        } else {
            false
        }*/
        // TODO
        false
    }

    fn add_counter_expression_region(&mut self, instance: Instance<'tcx>, id: InjectedExpressionIndex, lhs: ExpressionOperandId, op: Op, rhs: ExpressionOperandId, region: CodeRegion) -> bool {
        /*if let Some(coverage_context) = self.coverage_context() {
            debug!(
                "adding counter expression to coverage_regions: instance={:?}, id={:?}, {:?} {:?} {:?}, \
                at {:?}",
                instance, id, lhs, op, rhs, region,
            );
            let mut coverage_regions = coverage_context.function_coverage_map.borrow_mut();
            coverage_regions
                .entry(instance)
                .or_insert_with(|| FunctionCoverage::new(self.tcx, instance))
                .add_counter_expression(id, lhs, op, rhs, region);
            true
        } else {
            false
        }*/
        // TODO
        false
    }

    fn add_unreachable_region(&mut self, instance: Instance<'tcx>, region: CodeRegion) -> bool {
        /*if let Some(coverage_context) = self.coverage_context() {
            debug!(
                "adding unreachable code to coverage_regions: instance={:?}, at {:?}",
                instance, region,
            );
            let mut coverage_regions = coverage_context.function_coverage_map.borrow_mut();
            coverage_regions
                .entry(instance)
                .or_insert_with(|| FunctionCoverage::new(self.tcx, instance))
                .add_unreachable_region(region);
            true
        } else {
            false
        }*/
        // TODO
        false
    }
}

impl<'gcc, 'tcx> CoverageInfoMethods for CodegenCx<'gcc, 'tcx> {
    fn coverageinfo_finalize(&self) {
        // TODO
        //mapgen::finalize(self)
    }
}
