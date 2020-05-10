/*
 * TODO: support #[inline] attributes.
 * TODO: support LTO.
 *
 * TODO: remove the local gccjit LD_LIBRARY_PATH in config.sh.
 * TODO: remove the object dependency.
 * TODO: remove the patches.
 */

#![feature(rustc_private, decl_macro, or_patterns, type_alias_impl_trait, associated_type_bounds, never_type, trusted_len)]
#![allow(intra_doc_link_resolution_failure)]
#![recursion_limit="256"]
#![warn(rust_2018_idioms)]
#![warn(unused_lifetimes)]

/*extern crate flate2;
extern crate libc;*/
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_errors;
//extern crate rustc_fs_util;
extern crate rustc_hir;
extern crate rustc_incremental;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;
extern crate rustc_target;

// This prevents duplicating functions and statics that are already part of the host rustc process.
#[allow(unused_extern_crates)]
extern crate rustc_driver;

mod abi;
mod allocator;
mod archive;
mod asm;
mod back;
mod base;
mod builder;
mod callee;
mod common;
mod consts;
mod context;
mod debuginfo;
mod declare;
mod intrinsic;
mod metadata;
mod mono_item;
mod target_features_whitelist;
mod type_;
mod type_of;

use std::any::Any;
use std::sync::Arc;

use gccjit::{Block, Context, FunctionType, OptimizationLevel};
use rustc_ast::expand::allocator::AllocatorKind;
use rustc_codegen_ssa::{CodegenResults, CompiledModule, ModuleCodegen};
use rustc_codegen_ssa::base::codegen_crate;
use rustc_codegen_ssa::back::write::{CodegenContext, FatLTOInput, ModuleConfig};
use rustc_codegen_ssa::back::lto::{LtoModuleCodegen, SerializedModule, ThinModule};
use rustc_codegen_ssa::traits::{CodegenBackend, ExtraBackendMethods, ModuleBufferMethods, ThinBufferMethods, WriteBackendMethods};
use rustc_errors::{ErrorReported, Handler};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::dep_graph::{DepGraph, WorkProduct};
use rustc_middle::middle::cstore::{EncodedMetadata, MetadataLoader};
use rustc_middle::ty::{
    query::Providers,
    TyCtxt,
};
use rustc_session::config::{Lto, OptLevel, OutputFilenames};
use rustc_session::Session;
use rustc_span::Symbol;
use rustc_span::fatal_error::FatalError;

use crate::context::unit_name;

pub struct PrintOnPanic<F: Fn() -> String>(pub F);

impl<F: Fn() -> String> Drop for PrintOnPanic<F> {
    fn drop(&mut self) {
        if ::std::thread::panicking() {
            println!("{}", (self.0)());
        }
    }
}

#[derive(Clone)]
pub struct GccCodegenBackend;

impl CodegenBackend for GccCodegenBackend {
    fn init(&self, sess: &Session) {
        if sess.lto() != Lto::No {
            sess.warn("LTO is not supported. You may get a linker error.");
        }
    }

    fn metadata_loader(&self) -> Box<dyn MetadataLoader + Sync> {
        Box::new(crate::metadata::GccMetadataLoader)
    }

    fn provide(&self, providers: &mut Providers<'_>) {
        providers.target_features_whitelist = |tcx, cnum| {
            assert_eq!(cnum, LOCAL_CRATE);
            if tcx.sess.opts.actually_rustdoc {
                // rustdoc needs to be able to document functions that use all the features, so
                // whitelist them all
                target_features_whitelist::all_known_features()
                    .map(|(a, b)| (a.to_string(), b))
                    .collect()
            } else {
                target_features_whitelist::target_feature_whitelist(tcx.sess)
                    .iter()
                    .map(|&(a, b)| (a.to_string(), b))
                    .collect()
            }
        };
    }

    fn provide_extern(&self, _providers: &mut Providers<'_>) {
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>, metadata: EncodedMetadata, need_metadata_module: bool) -> Box<dyn Any> {
        let res = codegen_crate(self.clone(), tcx, metadata, need_metadata_module);

        rustc_symbol_mangling::test::report_symbol_names(tcx);

        Box::new(res)
    }

    fn join_codegen(&self, ongoing_codegen: Box<dyn Any>, sess: &Session, dep_graph: &DepGraph) -> Result<Box<dyn Any>, ErrorReported> {
        /*let (codegen_results, work_products) = *ongoing_codegen.downcast::<(CodegenResults, FxHashMap<WorkProductId, WorkProduct>)>().unwrap();

        sess.time("serialize_work_products", move || {
            rustc_incremental::save_work_product_index(sess, &dep_graph, work_products)
        });

        Ok(Box::new(codegen_results))*/
        let (codegen_results, work_products) = ongoing_codegen
            .downcast::<rustc_codegen_ssa::back::write::OngoingCodegen<GccCodegenBackend>>()
            .expect("Expected GccCodegenBackend's OngoingCodegen, found Box<Any>")
            .join(sess);
        if sess.opts.debugging_opts.incremental_info {
            rustc_codegen_ssa::back::write::dump_incremental_data(&codegen_results);
        }

        sess.time("serialize_work_products", move || {
            rustc_incremental::save_work_product_index(sess, &dep_graph, work_products)
        });

        sess.compile_status()?;

        Ok(Box::new(codegen_results))
    }

    fn link(&self, sess: &Session, res: Box<dyn Any>, outputs: &OutputFilenames) -> Result<(), ErrorReported> {
        use rustc_codegen_ssa::back::link::link_binary;

        let codegen_results = *res.downcast::<CodegenResults>()
            .expect("Expected GccCodegenBackend's CodegenResult, found Box<Any>");

        let _timer = sess.prof.generic_activity("link_crate");

        sess.time("linking", || {
            let target_cpu = crate::target_triple(sess).to_string();
            link_binary::<crate::archive::ArArchiveBuilder<'_>>(
                sess,
                &codegen_results,
                outputs,
                &codegen_results.crate_name.as_str(),
                &target_cpu,
            );
        });

        rustc_incremental::finalize_session_directory(sess, codegen_results.crate_hash);

        Ok(())
    }
}

impl ExtraBackendMethods for GccCodegenBackend {
    fn new_metadata<'tcx>(&self, tcx: TyCtxt<'tcx>, mod_name: &str) -> Self::Module {
        GccContext {
            context: Context::default(),
        }
    }

    fn write_compressed_metadata<'tcx>(&self, tcx: TyCtxt<'tcx>, metadata: &EncodedMetadata, gcc_module: &mut Self::Module) {
        base::write_compressed_metadata(tcx, metadata, gcc_module)
    }

    fn codegen_allocator<'tcx>(&self, tcx: TyCtxt<'tcx>, mods: &mut Self::Module, kind: AllocatorKind) {
        unsafe { allocator::codegen(tcx, mods, kind) }
    }

    fn compile_codegen_unit<'tcx>(&self, tcx: TyCtxt<'tcx>, cgu_name: Symbol) -> (ModuleCodegen<Self::Module>, u64) {
        base::compile_codegen_unit(tcx, cgu_name)
    }

    fn target_machine_factory(&self, sess: &Session, opt_level: OptLevel) -> Arc<dyn Fn() -> Result<Self::TargetMachine, String> + Send + Sync> {
        // TODO: set opt level.
        Arc::new(|| {
            Ok(())
        })
    }

    fn target_cpu<'b>(&self, sess: &'b Session) -> &'b str {
        unimplemented!();
    }
}

pub struct ModuleBuffer;

impl ModuleBufferMethods for ModuleBuffer {
    fn data(&self) -> &[u8] {
        unimplemented!();
    }
}

pub struct ThinBuffer;

impl ThinBufferMethods for ThinBuffer {
    fn data(&self) -> &[u8] {
        unimplemented!();
    }
}

pub struct GccContext {
    context: Context<'static>,
}

unsafe impl Send for GccContext {}
// FIXME: that shouldn't be Sync. Parallel compilation is currently disabled with "-Zno-parallel-llvm". Try to disable it here.
unsafe impl Sync for GccContext {}

impl WriteBackendMethods for GccCodegenBackend {
    type Module = GccContext;
    type TargetMachine = ();
    type ModuleBuffer = ModuleBuffer;
    type Context = ();
    type ThinData = ();
    type ThinBuffer = ThinBuffer;

    fn run_fat_lto(cgcx: &CodegenContext<Self>, mut modules: Vec<FatLTOInput<Self>>, cached_modules: Vec<(SerializedModule<Self::ModuleBuffer>, WorkProduct)>) -> Result<LtoModuleCodegen<Self>, FatalError> {
        // TODO: implement LTO by sending -flto to libgccjit and adding the appropriate gcc linker plugins.
        // NOTE: implemented elsewhere.
        let module =
            match modules.remove(0) {
                FatLTOInput::InMemory(module) => module,
                FatLTOInput::Serialized { name, buffer } => {
                    unimplemented!();
                    /*info!("pushing serialized module {:?}", name);
                    let buffer = SerializedModule::Local(buffer);
                    serialized_modules.push((buffer, CString::new(name).unwrap()));*/
                }
            };
        Ok(LtoModuleCodegen::Fat { module: Some(module), _serialized_bitcode: vec![] })
    }

    fn run_thin_lto(cgcx: &CodegenContext<Self>, modules: Vec<(String, Self::ThinBuffer)>, cached_modules: Vec<(SerializedModule<Self::ModuleBuffer>, WorkProduct)>) -> Result<(Vec<LtoModuleCodegen<Self>>, Vec<WorkProduct>), FatalError> {
        unimplemented!();
    }

    fn print_pass_timings(&self) {
        unimplemented!();
    }

    unsafe fn optimize(cgcx: &CodegenContext<Self>, diag_handler: &Handler, module: &ModuleCodegen<Self::Module>, config: &ModuleConfig) -> Result<(), FatalError> {
        //if cgcx.lto == Lto::Fat {
            //module.module_llvm.context.add_driver_option("-flto");
        //}
        module.module_llvm.context.set_optimization_level(to_gcc_opt_level(config.opt_level));
        Ok(())
    }

    unsafe fn optimize_thin(cgcx: &CodegenContext<Self>, thin: &mut ThinModule<Self>) -> Result<ModuleCodegen<Self::Module>, FatalError> {
        unimplemented!();
    }

    unsafe fn codegen(cgcx: &CodegenContext<Self>, diag_handler: &Handler, module: ModuleCodegen<Self::Module>, config: &ModuleConfig) -> Result<CompiledModule, FatalError> {
        back::write::codegen(cgcx, diag_handler, module, config)
    }

    fn prepare_thin(module: ModuleCodegen<Self::Module>) -> (String, Self::ThinBuffer) {
        unimplemented!();
    }

    fn serialize_module(module: ModuleCodegen<Self::Module>) -> (String, Self::ModuleBuffer) {
        unimplemented!();
    }

    fn run_lto_pass_manager(cgcx: &CodegenContext<Self>, llmod: &ModuleCodegen<Self::Module>, config: &ModuleConfig, thin: bool) {
        // TODO
    }
}

fn target_triple(sess: &Session) -> target_lexicon::Triple {
    sess.target.target.llvm_target.parse().unwrap()
}

/// This is the entrypoint for a hot plugged rustc_codegen_gccjit
#[no_mangle]
pub fn __rustc_codegen_backend() -> Box<dyn CodegenBackend> {
    Box::new(GccCodegenBackend)
}

fn to_gcc_opt_level(optlevel: Option<OptLevel>) -> OptimizationLevel {
    match optlevel {
        None => OptimizationLevel::None,
        Some(level) => {
            match level {
                OptLevel::No => OptimizationLevel::None,
                OptLevel::Less => OptimizationLevel::Limited,
                OptLevel::Default => OptimizationLevel::Standard,
                OptLevel::Aggressive => OptimizationLevel::Aggressive,
                OptLevel::Size | OptLevel::SizeMin => OptimizationLevel::Limited,
            }
        },
    }
}

fn create_function_calling_initializers<'gcc, 'tcx>(tcx: TyCtxt<'tcx>, context: &Context<'gcc>, block: Block<'gcc>) {
    let codegen_units = tcx.collect_and_partition_mono_items(LOCAL_CRATE).1;
    for codegen_unit in codegen_units {
        let codegen_init_func = context.new_function(None, FunctionType::Extern, context.new_type::<()>(), &[],
            &format!("__gccGlobalInit{}", unit_name(&codegen_unit)), false);
        block.add_eval(None, context.new_call(None, codegen_init_func, &[]));
    }
}
