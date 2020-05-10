use gccjit::{BinaryOp, ComparisonOp, Function, RValue, ToRValue, Type, UnaryOp};
use rustc_ast::ast;
use rustc_codegen_ssa::{MemFlags, glue};
use rustc_codegen_ssa::base::{to_immediate, wants_msvc_seh};
use rustc_codegen_ssa::common::span_invalid_monomorphization_error;
use rustc_codegen_ssa::mir::operand::{OperandRef, OperandValue};
use rustc_codegen_ssa::mir::place::PlaceRef;
use rustc_codegen_ssa::traits::{ArgAbiMethods, BaseTypeMethods, BuilderMethods, ConstMethods, IntrinsicCallMethods};
use rustc_middle::bug;
use rustc_middle::ty::{self, Instance, Ty};
use rustc_span::Span;
use rustc_target::abi::{self, LayoutOf, Primitive};
use rustc_target::abi::call::{ArgAbi, FnAbi, PassMode};
use rustc_target::spec::PanicStrategy;

use crate::abi::GccType;
use crate::builder::Builder;
use crate::common::{SignType, TypeReflection};
use crate::context::CodegenCx;
use crate::type_of::LayoutGccExt;

fn get_simple_intrinsic<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, name: &str) -> Option<Function<'gcc>> {
    let gcc_name = match name {
        "sqrtf32" => "sqrtf",
        "sqrtf64" => "sqrt",
        "powif32" => "__builtin_powif",
        "powif64" => "__builtin_powi",
        "sinf32" => "sinf",
        "sinf64" => "sin",
        "cosf32" => "cosf",
        "cosf64" => "cos",
        "powf32" => "powf",
        "powf64" => "pow",
        "expf32" => "expf",
        "expf64" => "exp",
        "exp2f32" => "exp2f",
        "exp2f64" => "exp2",
        "logf32" => "logf",
        "logf64" => "log",
        "log10f32" => "log10f",
        "log10f64" => "log10",
        "log2f32" => "log2f",
        "log2f64" => "log2",
        "fmaf32" => "fmaf",
        "fmaf64" => "fma",
        "fabsf32" => "fabsf",
        "fabsf64" => "fabs",
        "minnumf32" => "fminf",
        "minnumf64" => "fmin",
        "maxnumf32" => "fmaxf",
        "maxnumf64" => "fmax",
        "copysignf32" => "copysignf",
        "copysignf64" => "copysign",
        "floorf32" => "floorf",
        "floorf64" => "floor",
        "ceilf32" => "ceilf",
        "ceilf64" => "ceil",
        "truncf32" => "truncf",
        "truncf64" => "trunc",
        "rintf32" => "rintf",
        "rintf64" => "rint",
        "nearbyintf32" => "nearbyintf",
        "nearbyintf64" => "nearbyint",
        "roundf32" => "roundf",
        "roundf64" => "round",
        "abort" => "abort",
        _ => return None,
    };
    Some(cx.context.get_builtin_function(&gcc_name))
}

impl<'a, 'gcc, 'tcx> IntrinsicCallMethods<'tcx> for Builder<'a, 'gcc, 'tcx> {
    fn codegen_intrinsic_call(&mut self, instance: Instance<'tcx>, fn_abi: &FnAbi<'tcx, Ty<'tcx>>, args: &[OperandRef<'tcx, RValue<'gcc>>], llresult: RValue<'gcc>, span: Span) {
        let tcx = self.tcx;
        let callee_ty = instance.monomorphic_ty(tcx);

        let (def_id, substs) = match callee_ty.kind {
            ty::FnDef(def_id, substs) => (def_id, substs),
            _ => bug!("expected fn item type, found {}", callee_ty),
        };

        let sig = callee_ty.fn_sig(tcx);
        let sig = tcx.normalize_erasing_late_bound_regions(ty::ParamEnv::reveal_all(), &sig);
        let arg_tys = sig.inputs();
        let ret_ty = sig.output();
        let name = &*tcx.item_name(def_id).as_str();

        let llret_ty = self.layout_of(ret_ty).gcc_type(self, true);
        let result = PlaceRef::new_sized(llresult, fn_abi.ret.layout);

        let simple = get_simple_intrinsic(self, name);
        let llval =
            match name {
                _ if simple.is_some() => {
                    // FIXME: remove this cast when the API supports function.
                    let func = unsafe { std::mem::transmute(simple.expect("simple")) };
                    self.call(func, &args.iter().map(|arg| arg.immediate()).collect::<Vec<_>>(), None)
                },
                "assume" => {
                    debug_assert_eq!(args.len(), 1);
                    let value = args[0].immediate();
                    self.assume(value);
                    value
                },
                "unreachable" => {
                    return;
                }
                "likely" => {
                    self.expect(args[0].immediate(), true)
                }
                "unlikely" => {
                    self.expect(args[0].immediate(), false)
                }
                "try" => {
                    try_intrinsic(self, args[0].immediate(), args[1].immediate(), args[2].immediate(), llresult);
                    return;
                }
                "breakpoint" => {
                    unimplemented!();
                    /*let llfn = self.get_intrinsic(&("llvm.debugtrap"));
                      self.call(llfn, &[], None)*/
                }
                "va_start" => self.va_start(args[0].immediate()),
                "va_end" => self.va_end(args[0].immediate()),
                "va_copy" => {
                    unimplemented!();
                    /*let intrinsic = self.cx().get_intrinsic(&("llvm.va_copy"));
                      self.call(intrinsic, &[args[0].immediate(), args[1].immediate()], None)*/
                }
                "va_arg" => {
                    unimplemented!();
                    /*match fn_abi.ret.layout.abi {
                      abi::Abi::Scalar(ref scalar) => {
                      match scalar.value {
                      Primitive::Int(..) => {
                      if self.cx().size_of(ret_ty).bytes() < 4 {
                    // `va_arg` should not be called on a integer type
                    // less than 4 bytes in length. If it is, promote
                    // the integer to a `i32` and truncate the result
                    // back to the smaller type.
                    let promoted_result = emit_va_arg(self, args[0], tcx.types.i32);
                    self.trunc(promoted_result, llret_ty)
                    } else {
                    emit_va_arg(self, args[0], ret_ty)
                    }
                    }
                    Primitive::F64 | Primitive::Pointer => {
                    emit_va_arg(self, args[0], ret_ty)
                    }
                    // `va_arg` should never be used with the return type f32.
                    Primitive::F32 => bug!("the va_arg intrinsic does not work with `f32`"),
                    }
                    }
                    _ => bug!("the va_arg intrinsic does not work with non-scalar types"),
                    }*/
                }
                "size_of_val" => {
                    let tp_ty = substs.type_at(0);
                    if let OperandValue::Pair(_, meta) = args[0].val {
                        let (llsize, _) = glue::size_and_align_of_dst(self, tp_ty, Some(meta));
                        llsize
                    } else {
                        self.const_usize(self.size_of(tp_ty).bytes())
                    }
                }
                "min_align_of_val" => {
                    let tp_ty = substs.type_at(0);
                    if let OperandValue::Pair(_, meta) = args[0].val {
                        let (_, llalign) = glue::size_and_align_of_dst(self, tp_ty, Some(meta));
                        llalign
                    } else {
                        self.const_usize(self.align_of(tp_ty).bytes())
                    }
                }
                "size_of" | "pref_align_of" | "min_align_of" | "needs_drop" | "type_id"
                    | "type_name" => {
                        let ty_name = self
                            .tcx
                            .const_eval_instance(ty::ParamEnv::reveal_all(), instance, None)
                            .unwrap();
                        OperandRef::from_const(self, ty_name, ret_ty).immediate_or_packed_pair(self)
                    }
                // Effectively no-op
                "forget" => {
                    return;
                }
                "offset" => {
                    let ptr = args[0].immediate();
                    let offset = args[1].immediate();
                    self.inbounds_gep(ptr, &[offset])
                }
                "arith_offset" => {
                    let ptr = args[0].immediate();
                    let offset = args[1].immediate();
                    self.gep(ptr, &[offset])
                }

                "copy_nonoverlapping" => {
                    copy_intrinsic(
                        self,
                        false,
                        false,
                        substs.type_at(0),
                        args[1].immediate(),
                        args[0].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }
                "copy" => {
                    copy_intrinsic(
                        self,
                        true,
                        false,
                        substs.type_at(0),
                        args[1].immediate(),
                        args[0].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }
                "write_bytes" => {
                    memset_intrinsic(
                        self,
                        false,
                        substs.type_at(0),
                        args[0].immediate(),
                        args[1].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }

                "volatile_copy_nonoverlapping_memory" => {
                    copy_intrinsic(
                        self,
                        false,
                        true,
                        substs.type_at(0),
                        args[0].immediate(),
                        args[1].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }
                "volatile_copy_memory" => {
                    copy_intrinsic(
                        self,
                        true,
                        true,
                        substs.type_at(0),
                        args[0].immediate(),
                        args[1].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }
                "volatile_set_memory" => {
                    memset_intrinsic(
                        self,
                        true,
                        substs.type_at(0),
                        args[0].immediate(),
                        args[1].immediate(),
                        args[2].immediate(),
                    );
                    return;
                }
                "volatile_load" | "unaligned_volatile_load" => {
                    let tp_ty = substs.type_at(0);
                    let mut ptr = args[0].immediate();
                    if let PassMode::Cast(ty) = fn_abi.ret.mode {
                        ptr = self.pointercast(ptr, self.type_ptr_to(ty.gcc_type(self)));
                    }
                    let load = self.volatile_load(ptr);
                    let align = if name == "unaligned_volatile_load" {
                        1
                    } else {
                        self.align_of(tp_ty).bytes() as u32
                    };
                    // TODO
                    /*unsafe {
                      llvm::LLVMSetAlignment(load, align);
                      }*/
                    to_immediate(self, load, self.layout_of(tp_ty))
                }
                "volatile_store" => {
                    let dst = args[0].deref(self.cx());
                    args[1].val.volatile_store(self, dst);
                    return;
                }
                "unaligned_volatile_store" => {
                    let dst = args[0].deref(self.cx());
                    args[1].val.unaligned_volatile_store(self, dst);
                    return;
                }
                "prefetch_read_data"
                    | "prefetch_write_data"
                    | "prefetch_read_instruction"
                    | "prefetch_write_instruction" => {
                        unimplemented!();
                        /*let expect = self.get_intrinsic(&("llvm.prefetch"));
                          let (rw, cache_type) = match name {
                          "prefetch_read_data" => (0, 1),
                          "prefetch_write_data" => (1, 1),
                          "prefetch_read_instruction" => (0, 0),
                          "prefetch_write_instruction" => (1, 0),
                          _ => bug!(),
                          };
                          self.call(
                          expect,
                          &[
                          args[0].immediate(),
                          self.const_i32(rw),
                          args[1].immediate(),
                          self.const_i32(cache_type),
                          ],
                          None,
                          )*/
                    }
                "ctlz" | "ctlz_nonzero" | "cttz" | "cttz_nonzero" | "ctpop" | "bswap"
                    | "bitreverse" | "add_with_overflow" | "sub_with_overflow" | "mul_with_overflow"
                    | "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "unchecked_div"
                    | "unchecked_rem" | "unchecked_shl" | "unchecked_shr" | "unchecked_add"
                    | "unchecked_sub" | "unchecked_mul" | "exact_div" | "rotate_left" | "rotate_right"
                    | "saturating_add" | "saturating_sub" => {
                        let ty = arg_tys[0];
                        match int_type_width_signed(ty, self) {
                            Some((width, signed)) => match name {
                                "ctlz" | "cttz" => {
                                    let func = self.current_func.borrow().expect("func");
                                    let then_block = func.new_block("then");
                                    let else_block = func.new_block("else");
                                    let after_block = func.new_block("after");

                                    let result = func.new_local(None, self.int_type, "zeros");

                                    let arg = args[0].immediate();
                                    let zero = self.cx.context.new_rvalue_zero(arg.get_type());
                                    let cond = self.cx.context.new_comparison(None, ComparisonOp::Equals, arg, zero);
                                    self.block.expect("block").end_with_conditional(None, cond, then_block, else_block);

                                    let zero_result = self.cx.context.new_rvalue_from_long(self.int_type, width as i64);
                                    then_block.add_assignment(None, result, zero_result);
                                    then_block.end_with_jump(None, after_block);

                                    let zeros =
                                        match name {
                                            "ctlz" => self.count_leading_zeroes(width, arg),
                                            "cttz" => self.count_trailing_zeroes(width, arg),
                                            _ => unreachable!(),
                                        };
                                    else_block.add_assignment(None, result, zeros);
                                    else_block.end_with_jump(None, after_block);

                                    // NOTE: since jumps were added in a place rustc does not
                                    // expect, the current blocks in the state need to be updated.
                                    *self.current_block.borrow_mut() = Some(after_block);
                                    self.block = Some(after_block);

                                    result.to_rvalue()

                                    /*let y = self.const_bool(false);
                                    let llfn = self.get_intrinsic(&format!("llvm.{}.i{}", name, width));
                                    self.call(llfn, &[args[0].immediate(), y], None)*/
                                }
                                "ctlz_nonzero" => {
                                    self.count_leading_zeroes(width, args[0].immediate())
                                },
                                "cttz_nonzero" => {
                                    self.count_trailing_zeroes(width, args[0].immediate())
                                }
                                "ctpop" => {
                                    self.pop_count(args[0].immediate())
                                }
                                "bswap" => {
                                    if width == 8 {
                                        args[0].immediate() // byte swap a u8/i8 is just a no-op
                                    }
                                    else {
                                        match width {
                                            128 => {
                                                // TODO: check if it's faster to use string literals and a
                                                // match instead of format!.
                                                // FIXME: support 128-bit ints.
                                                let bswap = self.cx.context.get_builtin_function("__builtin_bswap64");
                                                self.cx.context.new_call(None, bswap, &[self.intcast(args[0].immediate(), self.ulong_type, false)])
                                            },
                                            _ => {
                                                // TODO: check if it's faster to use string literals and a
                                                // match instead of format!.
                                                let bswap = self.cx.context.get_builtin_function(&format!("__builtin_bswap{}", width));
                                                let mut arg = args[0].immediate();
                                                // FIXME: this cast should not be necessary. Remove
                                                // when having proper sized integer types.
                                                let param_type = bswap.get_param(0).to_rvalue().get_type();
                                                if param_type != arg.get_type() {
                                                    arg = self.bitcast(arg, param_type);
                                                }
                                                self.cx.context.new_call(None, bswap, &[arg])
                                            },
                                        }
                                    }
                                }
                                "bitreverse" => self.bit_reverse(width, args[0].immediate()),
                                "add_with_overflow" => {
                                    let func_name =
                                        if signed {
                                            match width {
                                                8 => "__builtin_add_overflow",
                                                16 => "__builtin_add_overflow",
                                                32 => "__builtin_sadd_overflow",
                                                64 => "__builtin_saddll_overflow",
                                                128 => "__builtin_saddll_overflow",
                                                _ => unreachable!(),
                                            }
                                        }
                                        else {
                                            match width {
                                                8 => "__builtin_add_overflow",
                                                16 => "__builtin_add_overflow",
                                                32 => "__builtin_uadd_overflow",
                                                64 => "__builtin_uaddll_overflow",
                                                128 => "__builtin_uaddll_overflow",
                                                _ => unreachable!(),
                                            }
                                        };
                                    self.overflow_intrinsic_call(func_name, args[0].immediate(), args[1].immediate(), &result);
                                    return;
                                },
                                "sub_with_overflow" => {
                                    let func_name =
                                        if signed {
                                            match width {
                                                8 => "__builtin_sub_overflow",
                                                16 => "__builtin_sub_overflow",
                                                32 => "__builtin_ssub_overflow",
                                                64 => "__builtin_ssubll_overflow",
                                                128 => "__builtin_ssubll_overflow",
                                                _ => unreachable!(),
                                            }
                                        }
                                        else {
                                            match width {
                                                8 => "__builtin_sub_overflow",
                                                16 => "__builtin_sub_overflow",
                                                32 => "__builtin_usub_overflow",
                                                64 => "__builtin_usubll_overflow",
                                                128 => "__builtin_usubll_overflow",
                                                _ => unreachable!(),
                                            }
                                        };
                                    self.overflow_intrinsic_call(func_name, args[0].immediate(), args[1].immediate(), &result);
                                    return;
                                },
                                "mul_with_overflow" => {
                                    let func_name =
                                        if signed {
                                            match width {
                                                8 => "__builtin_mul_overflow",
                                                16 => "__builtin_mul_overflow",
                                                32 => "__builtin_smul_overflow",
                                                64 => "__builtin_smulll_overflow",
                                                128 => "__builtin_smulll_overflow",
                                                _ => unreachable!(),
                                            }
                                        }
                                        else {
                                            match width {
                                                8 => "__builtin_mul_overflow",
                                                16 => "__builtin_mul_overflow",
                                                32 => "__builtin_umul_overflow",
                                                64 => "__builtin_umulll_overflow",
                                                128 => "__builtin_umulll_overflow",
                                                _ => unreachable!(),
                                            }
                                        };
                                    self.overflow_intrinsic_call(func_name, args[0].immediate(), args[1].immediate(), &result);
                                    return;
                                },
                                "wrapping_add" => self.add(args[0].immediate(), args[1].immediate()),
                                "wrapping_sub" => self.sub(args[0].immediate(), args[1].immediate()),
                                "wrapping_mul" => self.mul(args[0].immediate(), args[1].immediate()),
                                "exact_div" => {
                                    if signed {
                                        self.exactsdiv(args[0].immediate(), args[1].immediate())
                                    } else {
                                        self.exactudiv(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_div" => {
                                    if signed {
                                        self.sdiv(args[0].immediate(), args[1].immediate())
                                    } else {
                                        self.udiv(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_rem" => {
                                    if signed {
                                        self.srem(args[0].immediate(), args[1].immediate())
                                    } else {
                                        self.urem(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_shl" => self.shl(args[0].immediate(), args[1].immediate()),
                                "unchecked_shr" => {
                                    if signed {
                                        self.ashr(args[0].immediate(), args[1].immediate())
                                    } else {
                                        self.lshr(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_add" => {
                                    if signed {
                                        self.unchecked_sadd(args[0].immediate(), args[1].immediate())
                                    }
                                    else {
                                        self.unchecked_uadd(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_sub" => {
                                    if signed {
                                        self.unchecked_ssub(args[0].immediate(), args[1].immediate())
                                    }
                                    else {
                                        self.unchecked_usub(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "unchecked_mul" => {
                                    if signed {
                                        self.unchecked_smul(args[0].immediate(), args[1].immediate())
                                    }
                                    else {
                                        self.unchecked_umul(args[0].immediate(), args[1].immediate())
                                    }
                                }
                                "rotate_left" | "rotate_right" => {
                                    // TODO: implement using algorithm from:
                                    // https://blog.regehr.org/archives/1063
                                    // for other platforms.
                                    let is_left = name == "rotate_left";
                                    let val = args[0].immediate();
                                    let raw_shift = args[1].immediate();
                                    if is_left {
                                        self.rotate_left(val, raw_shift, width)
                                    }
                                    else {
                                        match width {
                                            8 => unimplemented!(),
                                            16 => unimplemented!(),
                                            32 => unimplemented!(),
                                            64 => unimplemented!(),
                                            _ => unimplemented!("rotate for integer of size {}", width),
                                        }
                                    }
                                }
                                "saturating_add" => {
                                    self.saturating_add(args[0].immediate(), args[1].immediate(), signed, width)
                                },
                                "saturating_sub" => {
                                    self.saturating_sub(args[0].immediate(), args[1].immediate(), signed, width)
                                }
                                _ => bug!(),
                            },
                            None => {
                                span_invalid_monomorphization_error(
                                    tcx.sess,
                                    span,
                                    &format!(
                                        "invalid monomorphization of `{}` intrinsic: \
                                expected basic integer type, found `{}`",
                                name, ty
                                    ),
                                );
                                return;
                            }
                        }
                    }
                "fadd_fast" | "fsub_fast" | "fmul_fast" | "fdiv_fast" | "frem_fast" => {
                    match float_type_width(arg_tys[0]) {
                        Some(_width) => match name {
                            "fadd_fast" => self.fadd_fast(args[0].immediate(), args[1].immediate()),
                            "fsub_fast" => self.fsub_fast(args[0].immediate(), args[1].immediate()),
                            "fmul_fast" => self.fmul_fast(args[0].immediate(), args[1].immediate()),
                            "fdiv_fast" => self.fdiv_fast(args[0].immediate(), args[1].immediate()),
                            "frem_fast" => self.frem_fast(args[0].immediate(), args[1].immediate()),
                            _ => bug!(),
                        },
                        None => {
                            span_invalid_monomorphization_error(
                                tcx.sess,
                                span,
                                &format!(
                                    "invalid monomorphization of `{}` intrinsic: \
                                      expected basic float type, found `{}`",
                                      name, arg_tys[0]
                                ),
                            );
                            return;
                        }
                    }
                }

                "float_to_int_unchecked" => {
                    if float_type_width(arg_tys[0]).is_none() {
                        span_invalid_monomorphization_error(
                            tcx.sess,
                            span,
                            &format!(
                                "invalid monomorphization of `float_to_int_unchecked` \
                                  intrinsic: expected basic float type, \
                                  found `{}`",
                                  arg_tys[0]
                            ),
                        );
                        return;
                    }
                    match int_type_width_signed(ret_ty, self.cx) {
                        Some((width, signed)) => {
                            if signed {
                                self.fptosi(args[0].immediate(), self.cx.type_ix(width))
                            } else {
                                self.fptoui(args[0].immediate(), self.cx.type_ix(width))
                            }
                        }
                        None => {
                            span_invalid_monomorphization_error(
                                tcx.sess,
                                span,
                                &format!(
                                    "invalid monomorphization of `float_to_int_unchecked` \
                                      intrinsic:  expected basic integer type, \
                                      found `{}`",
                                      ret_ty
                                ),
                            );
                            return;
                        }
                    }
                }

                "discriminant_value" => args[0].deref(self.cx()).codegen_get_discr(self, ret_ty),

                name if name.starts_with("simd_") => {
                    unimplemented!();
                    /*match generic_simd_intrinsic(self, name, callee_ty, args, ret_ty, llret_ty, span) {
                      Ok(llval) => llval,
                      Err(()) => return,
                      }*/
                }
                // This requires that atomic intrinsics follow a specific naming pattern:
                // "atomic_<operation>[_<ordering>]", and no ordering means SeqCst
                name if name.starts_with("atomic_") => {
                    use rustc_codegen_ssa::common::AtomicOrdering::*;
                    use rustc_codegen_ssa::common::{AtomicRmwBinOp, SynchronizationScope};

                    let split: Vec<&str> = name.split('_').collect();

                    let is_cxchg = split[1] == "cxchg" || split[1] == "cxchgweak";
                    let (order, failorder) =
                        match split.len() {
                            2 => (SequentiallyConsistent, SequentiallyConsistent),
                            3 => match split[2] {
                                "unordered" => (Unordered, Unordered),
                                "relaxed" => (Monotonic, Monotonic),
                                "acq" => (Acquire, Acquire),
                                "rel" => (Release, Monotonic),
                                "acqrel" => (AcquireRelease, Acquire),
                                "failrelaxed" if is_cxchg => (SequentiallyConsistent, Monotonic),
                                "failacq" if is_cxchg => (SequentiallyConsistent, Acquire),
                                _ => self.sess().fatal("unknown ordering in atomic intrinsic"),
                            },
                            4 => match (split[2], split[3]) {
                                ("acq", "failrelaxed") if is_cxchg => (Acquire, Monotonic),
                                ("acqrel", "failrelaxed") if is_cxchg => (AcquireRelease, Monotonic),
                                _ => self.sess().fatal("unknown ordering in atomic intrinsic"),
                            },
                            _ => self.sess().fatal("Atomic intrinsic not in correct format"),
                        };

                    let invalid_monomorphization = |ty| {
                        span_invalid_monomorphization_error(
                            tcx.sess,
                            span,
                            &format!(
                                "invalid monomorphization of `{}` intrinsic: \
                                  expected basic integer type, found `{}`",
                                  name, ty
                            ),
                        );
                    };

                    match split[1] {
                        "cxchg" | "cxchgweak" => {
                            let ty = substs.type_at(0);
                            if int_type_width_signed(ty, self).is_some() {
                                let weak = split[1] == "cxchgweak";
                                let expected = args[1].immediate();
                                let expected_value = self.current_func().new_local(None, expected.get_type(), "expected");
                                self.llbb().add_assignment(None, expected_value, expected);
                                let success = self.atomic_cmpxchg(
                                    args[0].immediate(),
                                    expected_value.get_address(None),
                                    args[2].immediate(),
                                    order,
                                    failorder,
                                    weak,
                                );

                                let dest = result.project_field(self, 0);
                                self.store(expected_value.to_rvalue(), dest.llval, dest.align);
                                let dest = result.project_field(self, 1);
                                self.store(success, dest.llval, dest.align);
                                return;
                            } else {
                                return invalid_monomorphization(ty);
                            }
                        }

                        "load" => {
                            let ty = substs.type_at(0);
                            if int_type_width_signed(ty, self).is_some() {
                                let size = self.size_of(ty);
                                self.atomic_load(args[0].immediate(), order, size)
                            } else {
                                return invalid_monomorphization(ty);
                            }
                        }

                        "store" => {
                            let ty = substs.type_at(0);
                            if int_type_width_signed(ty, self).is_some() {
                                let size = self.size_of(ty);
                                self.atomic_store(
                                    args[1].immediate(),
                                    args[0].immediate(),
                                    order,
                                    size,
                                );
                                return;
                            } else {
                                return invalid_monomorphization(ty);
                            }
                        }

                        "fence" => {
                            self.atomic_fence(order, SynchronizationScope::CrossThread);
                            return;
                        }

                        "singlethreadfence" => {
                            self.atomic_fence(order, SynchronizationScope::SingleThread);
                            return;
                        }

                        // These are all AtomicRMW ops
                        op => {
                            let atom_op =
                                match op {
                                    "xchg" => AtomicRmwBinOp::AtomicXchg,
                                    "xadd" => AtomicRmwBinOp::AtomicAdd,
                                    "xsub" => AtomicRmwBinOp::AtomicSub,
                                    "and" => AtomicRmwBinOp::AtomicAnd,
                                    "nand" => AtomicRmwBinOp::AtomicNand,
                                    "or" => AtomicRmwBinOp::AtomicOr,
                                    "xor" => AtomicRmwBinOp::AtomicXor,
                                    "max" => AtomicRmwBinOp::AtomicMax,
                                    "min" => AtomicRmwBinOp::AtomicMin,
                                    "umax" => AtomicRmwBinOp::AtomicUMax,
                                    "umin" => AtomicRmwBinOp::AtomicUMin,
                                    _ => self.sess().fatal("unknown atomic operation"),
                                };

                            let ty = substs.type_at(0);
                            if int_type_width_signed(ty, self).is_some() {
                                self.atomic_rmw(
                                    atom_op,
                                    args[0].immediate(),
                                    args[1].immediate(),
                                    order,
                                )
                            } else {
                                return invalid_monomorphization(ty);
                            }
                        }
                    }
                }

                "nontemporal_store" => {
                    let dst = args[0].deref(self.cx());
                    args[1].val.nontemporal_store(self, dst);
                    return;
                }

                "ptr_offset_from" => {
                    let ty = substs.type_at(0);
                    let pointee_size = self.size_of(ty);

                    // This is the same sequence that Clang emits for pointer subtraction.
                    // It can be neither `nsw` nor `nuw` because the input is treated as
                    // unsigned but then the output is treated as signed, so neither works.
                    let a = args[0].immediate();
                    let b = args[1].immediate();
                    let a = self.ptrtoint(a, self.type_isize());
                    let b = self.ptrtoint(b, self.type_isize());
                    let d = self.sub(a, b);
                    let pointee_size = self.const_isize(pointee_size.bytes() as i64);
                    // this is where the signed magic happens (notice the `s` in `exactsdiv`)
                    self.exactsdiv(d, pointee_size)
                }

                _ => bug!("unknown intrinsic '{}'", name),
            };

        if !fn_abi.ret.is_ignore() {
            if let PassMode::Cast(ty) = fn_abi.ret.mode {
                let ptr_llty = self.type_ptr_to(ty.gcc_type(self));
                let ptr = self.pointercast(result.llval, ptr_llty);
                self.store(llval, ptr, result.align);
            }
            else {
                OperandRef::from_immediate_or_packed_pair(self, llval, result.layout)
                    .val
                    .store(self, result);
            }
        }
    }

    fn abort(&mut self) {
        let func = self.context.get_builtin_function("abort");
        let func: RValue<'gcc> = unsafe { std::mem::transmute(func) };
        self.call(func, &[], None);
    }

    fn assume(&mut self, value: Self::Value) {
        // TODO: switch to asumme when it exists.
        // Or use something like this:
        // #define __assume(cond) do { if (!(cond)) __builtin_unreachable(); } while (0)
        self.expect(value, true);
    }

    fn expect(&mut self, cond: Self::Value, expected: bool) -> Self::Value {
        // TODO
        /*let expect = self.context.get_builtin_function("__builtin_expect");
        let expect: RValue<'gcc> = unsafe { std::mem::transmute(expect) };
        self.call(expect, &[cond, self.const_bool(expected)], None)*/
        cond
    }

    fn sideeffect(&mut self) {
        // TODO
        /*if self.tcx().sess.opts.debugging_opts.insert_sideeffect {
            let fnname = self.get_intrinsic(&("llvm.sideeffect"));
            self.call(fnname, &[], None);
        }*/
    }

    fn va_start(&mut self, va_list: RValue<'gcc>) -> RValue<'gcc> {
        unimplemented!();
        /*let intrinsic = self.cx().get_intrinsic("llvm.va_start");
        self.call(intrinsic, &[va_list], None)*/
    }

    fn va_end(&mut self, va_list: RValue<'gcc>) -> RValue<'gcc> {
        unimplemented!();
        /*let intrinsic = self.cx().get_intrinsic("llvm.va_end");
        self.call(intrinsic, &[va_list], None)*/
    }
}

impl<'a, 'gcc, 'tcx> ArgAbiMethods<'tcx> for Builder<'a, 'gcc, 'tcx> {
    fn store_fn_arg(&mut self, arg_abi: &ArgAbi<'tcx, Ty<'tcx>>, idx: &mut usize, dst: PlaceRef<'tcx, Self::Value>) {
        arg_abi.store_fn_arg(self, idx, dst)
    }

    fn store_arg(&mut self, arg_abi: &ArgAbi<'tcx, Ty<'tcx>>, val: RValue<'gcc>, dst: PlaceRef<'tcx, RValue<'gcc>>) {
        arg_abi.store(self, val, dst)
    }

    fn arg_memory_ty(&self, arg_abi: &ArgAbi<'tcx, Ty<'tcx>>) -> Type<'gcc> {
        arg_abi.memory_ty(self)
    }
}

pub trait ArgAbiExt<'gcc, 'tcx> {
    fn memory_ty(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc>;
    fn store(&self, bx: &mut Builder<'_, 'gcc, 'tcx>, val: RValue<'gcc>, dst: PlaceRef<'tcx, RValue<'gcc>>);
    fn store_fn_arg(&self, bx: &mut Builder<'_, 'gcc, 'tcx>, idx: &mut usize, dst: PlaceRef<'tcx, RValue<'gcc>>);
}

impl<'gcc, 'tcx> ArgAbiExt<'gcc, 'tcx> for ArgAbi<'tcx, Ty<'tcx>> {
    /// Gets the LLVM type for a place of the original Rust type of
    /// this argument/return, i.e., the result of `type_of::type_of`.
    fn memory_ty(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc> {
        self.layout.gcc_type(cx, true)
    }

    /// Stores a direct/indirect value described by this ArgAbi into a
    /// place for the original Rust type of this argument/return.
    /// Can be used for both storing formal arguments into Rust variables
    /// or results of call/invoke instructions into their destinations.
    fn store(&self, bx: &mut Builder<'_, 'gcc, 'tcx>, val: RValue<'gcc>, dst: PlaceRef<'tcx, RValue<'gcc>>) {
        if self.is_ignore() {
            return;
        }
        if self.is_sized_indirect() {
            OperandValue::Ref(val, None, self.layout.align.abi).store(bx, dst)
        }
        else if self.is_unsized_indirect() {
            bug!("unsized `ArgAbi` must be handled through `store_fn_arg`");
        }
        else if let PassMode::Cast(cast) = self.mode {
            // FIXME(eddyb): Figure out when the simpler Store is safe, clang
            // uses it for i16 -> {i8, i8}, but not for i24 -> {i8, i8, i8}.
            let can_store_through_cast_ptr = false;
            if can_store_through_cast_ptr {
                let cast_ptr_llty = bx.type_ptr_to(cast.gcc_type(bx));
                let cast_dst = bx.pointercast(dst.llval, cast_ptr_llty);
                bx.store(val, cast_dst, self.layout.align.abi);
            }
            else {
                // The actual return type is a struct, but the ABI
                // adaptation code has cast it into some scalar type.  The
                // code that follows is the only reliable way I have
                // found to do a transform like i64 -> {i32,i32}.
                // Basically we dump the data onto the stack then memcpy it.
                //
                // Other approaches I tried:
                // - Casting rust ret pointer to the foreign type and using Store
                //   is (a) unsafe if size of foreign type > size of rust type and
                //   (b) runs afoul of strict aliasing rules, yielding invalid
                //   assembly under -O (specifically, the store gets removed).
                // - Truncating foreign type to correct integral type and then
                //   bitcasting to the struct type yields invalid cast errors.

                // We instead thus allocate some scratch space...
                let scratch_size = cast.size(bx);
                let scratch_align = cast.align(bx);
                let llscratch = bx.alloca(cast.gcc_type(bx), scratch_align);
                bx.lifetime_start(llscratch, scratch_size);

                // ... where we first store the value...
                bx.store(val, llscratch, scratch_align);

                // ... and then memcpy it to the intended destination.
                bx.memcpy(
                    dst.llval,
                    self.layout.align.abi,
                    llscratch,
                    scratch_align,
                    bx.const_usize(self.layout.size.bytes()),
                    MemFlags::empty(),
                );

                bx.lifetime_end(llscratch, scratch_size);
            }
        }
        else {
            OperandValue::Immediate(val).store(bx, dst);
        }
    }

    fn store_fn_arg<'a>(&self, bx: &mut Builder<'a, 'gcc, 'tcx>, idx: &mut usize, dst: PlaceRef<'tcx, RValue<'gcc>>) {
        let mut next = || {
            let val = bx.current_func().get_param(*idx as i32);
            *idx += 1;
            val.to_rvalue()
        };
        match self.mode {
            PassMode::Ignore => {}
            PassMode::Pair(..) => {
                OperandValue::Pair(next(), next()).store(bx, dst);
            }
            PassMode::Indirect(_, Some(_)) => {
                OperandValue::Ref(next(), Some(next()), self.layout.align.abi).store(bx, dst);
            }
            PassMode::Direct(_) | PassMode::Indirect(_, None) | PassMode::Cast(_) => {
                let next_arg = next();
                self.store(bx, next_arg.to_rvalue(), dst);
            }
        }
    }
}

fn int_type_width_signed<'gcc, 'tcx>(ty: Ty<'tcx>, cx: &CodegenCx<'gcc, 'tcx>) -> Option<(u64, bool)> {
    match ty.kind {
        ty::Int(t) => Some((
            match t {
                ast::IntTy::Isize => u64::from(cx.tcx.sess.target.ptr_width),
                ast::IntTy::I8 => 8,
                ast::IntTy::I16 => 16,
                ast::IntTy::I32 => 32,
                ast::IntTy::I64 => 64,
                ast::IntTy::I128 => 128,
            },
            true,
        )),
        ty::Uint(t) => Some((
            match t {
                ast::UintTy::Usize => u64::from(cx.tcx.sess.target.ptr_width),
                ast::UintTy::U8 => 8,
                ast::UintTy::U16 => 16,
                ast::UintTy::U32 => 32,
                ast::UintTy::U64 => 64,
                ast::UintTy::U128 => 128,
            },
            false,
        )),
        _ => None,
    }
}

fn copy_intrinsic<'cx, 'gcc, 'tcx>(bx: &mut Builder<'cx, 'gcc, 'tcx>, allow_overlap: bool, volatile: bool, ty: Ty<'tcx>, dst: RValue<'gcc>, src: RValue<'gcc>, count: RValue<'gcc>) {
    let (size, align) = bx.size_and_align_of(ty);
    let size = bx.mul(bx.const_usize(size.bytes()), count);
    let flags =
        if volatile {
            MemFlags::VOLATILE
        }
        else {
            MemFlags::empty()
        };
    if allow_overlap {
        bx.memmove(dst, align, src, align, size, flags);
    }
    else {
        bx.memcpy(dst, align, src, align, size, flags);
    }
}

fn memset_intrinsic<'cx, 'gcc, 'tcx>(bx: &mut Builder<'cx, 'gcc, 'tcx>, volatile: bool, ty: Ty<'tcx>, dst: RValue<'gcc>, val: RValue<'gcc>, count: RValue<'gcc>) {
    let (size, align) = bx.size_and_align_of(ty);
    let context = &bx.cx.context;
    let usize_type = bx.cx.usize_type;
    let a = context.new_cast(None, bx.const_usize(size.bytes()), usize_type);
    let count = context.new_cast(None, count, usize_type);
    let size = bx.mul(a, count);
    let flags = if volatile { MemFlags::VOLATILE } else { MemFlags::empty() };
    bx.memset(dst, val, size, align, flags);
}

// Returns the width of a float Ty
// Returns None if the type is not a float
fn float_type_width(ty: Ty<'_>) -> Option<u64> {
    match ty.kind {
        ty::Float(t) => Some(t.bit_width()),
        _ => None,
    }
}

impl<'a, 'gcc, 'tcx> Builder<'a, 'gcc, 'tcx> {
    fn bit_reverse(&mut self, width: u64, value: RValue<'gcc>) -> RValue<'gcc> {
        let typ = value.get_type();
        let context = &self.cx.context;
        match width {
            8 => {
                // First step.
                let left = self.and(value, context.new_rvalue_from_int(typ, 0xF0));
                let left = self.lshr(left, context.new_rvalue_from_int(typ, 4));
                let right = self.and(value, context.new_rvalue_from_int(typ, 0x0F));
                let right = self.shl(right, context.new_rvalue_from_int(typ, 4));
                let step1 = self.or(left, right);

                // Second step.
                let left = self.and(step1, context.new_rvalue_from_int(typ, 0xCC));
                let left = self.lshr(left, context.new_rvalue_from_int(typ, 2));
                let right = self.and(step1, context.new_rvalue_from_int(typ, 0x33));
                let right = self.shl(right, context.new_rvalue_from_int(typ, 2));
                let step2 = self.or(left, right);

                // Third step.
                let left = self.and(step2, context.new_rvalue_from_int(typ, 0xAA));
                let left = self.lshr(left, context.new_rvalue_from_int(typ, 1));
                let right = self.and(step2, context.new_rvalue_from_int(typ, 0x55));
                let right = self.shl(right, context.new_rvalue_from_int(typ, 1));
                let step3 = self.or(left, right);

                step3
            },
            16 => {
                // First step.
                let left = self.and(value, context.new_rvalue_from_int(typ, 0x5555));
                let left = self.shl(left, context.new_rvalue_from_int(typ, 1));
                let right = self.and(value, context.new_rvalue_from_int(typ, 0xAAAA));
                let right = self.lshr(right, context.new_rvalue_from_int(typ, 1));
                let step1 = self.or(left, right);

                // Second step.
                let left = self.and(step1, context.new_rvalue_from_int(typ, 0x3333));
                let left = self.shl(left, context.new_rvalue_from_int(typ, 2));
                let right = self.and(step1, context.new_rvalue_from_int(typ, 0xCCCC));
                let right = self.lshr(right, context.new_rvalue_from_int(typ, 2));
                let step2 = self.or(left, right);

                // Third step.
                let left = self.and(step2, context.new_rvalue_from_int(typ, 0x0F0F));
                let left = self.shl(left, context.new_rvalue_from_int(typ, 4));
                let right = self.and(step2, context.new_rvalue_from_int(typ, 0xF0F0));
                let right = self.lshr(right, context.new_rvalue_from_int(typ, 4));
                let step3 = self.or(left, right);

                // Fourth step.
                let left = self.and(step3, context.new_rvalue_from_int(typ, 0x00FF));
                let left = self.shl(left, context.new_rvalue_from_int(typ, 8));
                let right = self.and(step3, context.new_rvalue_from_int(typ, 0xFF00));
                let right = self.lshr(right, context.new_rvalue_from_int(typ, 8));
                let step4 = self.or(left, right);

                step4
            },
            32 => {
                // TODO: Refactor with other implementations.
                // First step.
                let left = self.and(value, context.new_rvalue_from_long(typ, 0x55555555));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 1));
                let right = self.and(value, context.new_rvalue_from_long(typ, 0xAAAAAAAA));
                let right = self.lshr(right, context.new_rvalue_from_long(typ, 1));
                let step1 = self.or(left, right);

                // Second step.
                let left = self.and(step1, context.new_rvalue_from_long(typ, 0x33333333));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 2));
                let right = self.and(step1, context.new_rvalue_from_long(typ, 0xCCCCCCCC));
                let right = self.lshr(right, context.new_rvalue_from_long(typ, 2));
                let step2 = self.or(left, right);

                // Third step.
                let left = self.and(step2, context.new_rvalue_from_long(typ, 0x0F0F0F0F));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 4));
                let right = self.and(step2, context.new_rvalue_from_long(typ, 0xF0F0F0F0));
                let right = self.lshr(right, context.new_rvalue_from_long(typ, 4));
                let step3 = self.or(left, right);

                // Fourth step.
                let left = self.and(step3, context.new_rvalue_from_long(typ, 0x00FF00FF));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 8));
                let right = self.and(step3, context.new_rvalue_from_long(typ, 0xFF00FF00));
                let right = self.lshr(right, context.new_rvalue_from_long(typ, 8));
                let step4 = self.or(left, right);

                // Fifth step.
                let left = self.and(step4, context.new_rvalue_from_long(typ, 0x0000FFFF));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 16));
                let right = self.and(step4, context.new_rvalue_from_long(typ, 0xFFFF0000));
                let right = self.lshr(right, context.new_rvalue_from_long(typ, 16));
                let step5 = self.or(left, right);

                step5
            },
            64 => {
                // First step.
                let left = self.shl(value, context.new_rvalue_from_long(typ, 32));
                let right = self.lshr(left, context.new_rvalue_from_long(typ, 32));
                let step1 = self.or(left, right);

                // Second step.
                let left = self.and(step1, context.new_rvalue_from_long(typ, 0x0001FFFF0001FFFF));
                let left = self.shl(left, context.new_rvalue_from_long(typ, 15));
                let right = self.and(step1, context.new_rvalue_from_long(typ, 0xFFFE0000FFFE0000u64 as i64)); // TODO: transmute the number instead?
                let right = self.shl(right, context.new_rvalue_from_long(typ, 17));
                let step2 = self.or(left, right);

                // Third step.
                let left = self.lshr(step2, context.new_rvalue_from_long(typ, 10));
                let left = self.xor(step2, left);
                let temp = self.and(left, context.new_rvalue_from_long(typ, 0x003F801F003F801F));

                let left = self.shl(temp, context.new_rvalue_from_long(typ, 10));
                let left = self.or(temp, left);
                let step3 = self.xor(left, step2);

                // Fourth step.
                let left = self.lshr(step3, context.new_rvalue_from_long(typ, 4));
                let left = self.xor(step3, left);
                let temp = self.and(left, context.new_rvalue_from_long(typ, 0x0E0384210E038421));

                let left = self.shl(temp, context.new_rvalue_from_long(typ, 4));
                let left = self.or(temp, left);
                let step4 = self.xor(left, step3);

                // Fifth step.
                let left = self.lshr(step4, context.new_rvalue_from_long(typ, 2));
                let left = self.xor(step4, left);
                let temp = self.and(left, context.new_rvalue_from_long(typ, 0x2248884222488842));

                let left = self.shl(temp, context.new_rvalue_from_long(typ, 2));
                let left = self.or(temp, left);
                let step5 = self.xor(left, step4);

                step5
            },
            _ => {
                panic!("cannot bit reverse with width = {}", width);
            },
        }
    }

    fn count_leading_zeroes(&self, width: u64, arg: RValue<'gcc>) -> RValue<'gcc> {
        let arg_type = arg.get_type();
        let count_leading_zeroes =
            if arg_type.is_uint(&self.cx) {
                "__builtin_clz"
            }
            else if arg_type.is_ulong(&self.cx) {
                "__builtin_clzl"
            }
            else if arg_type.is_ulonglong(&self.cx) {
                "__builtin_clzll"
            }
            else {
                let count_leading_zeroes = self.context.get_builtin_function("__builtin_clz");
                let arg = self.context.new_cast(None, arg, self.uint_type);
                let diff = self.int_width(self.uint_type) - self.int_width(arg_type);
                let diff = self.context.new_rvalue_from_long(self.int_type, diff);
                return self.context.new_call(None, count_leading_zeroes, &[arg]) - diff;
            };
        let count_leading_zeroes = self.context.get_builtin_function(count_leading_zeroes);
        self.context.new_call(None, count_leading_zeroes, &[arg])
    }

    fn count_trailing_zeroes(&self, width: u64, arg: RValue<'gcc>) -> RValue<'gcc> {
        let arg_type = arg.get_type();
        let (count_trailing_zeroes, expected_type) =
            if arg_type.is_uchar(&self.cx) || arg_type.is_ushort(&self.cx) || arg_type.is_uint(&self.cx) {
                // NOTE: we don't need to & 0xFF for uchar because the result is undefined on zero.
                ("__builtin_ctz", self.cx.uint_type)
            }
            else if arg_type.is_ulong(&self.cx) {
                ("__builtin_ctzl", self.cx.ulong_type)
            }
            else if arg_type.is_ulonglong(&self.cx) {
                ("__builtin_ctzll", self.cx.ulonglong_type)
            }
            else {
                unimplemented!("count_trailing_zeroes for {:?}", arg_type);
            };
        let count_trailing_zeroes = self.context.get_builtin_function(count_trailing_zeroes);
        let arg =
            if arg_type != expected_type {
                self.context.new_cast(None, arg, expected_type)
            }
            else {
                arg
            };
        self.context.new_call(None, count_trailing_zeroes, &[arg])
    }

    fn int_width(&self, typ: Type<'gcc>) -> i64 {
        if typ.is_i8(&self.cx) || typ.is_u8(&self.cx) {
            8
        }
        else if typ.is_i16(&self.cx) || typ.is_u16(&self.cx) {
            16
        }
        else if typ.is_i32(&self.cx) || typ.is_u32(&self.cx) {
            32
        }
        else if typ.is_i64(&self.cx) || typ.is_u64(&self.cx) {
            64
        }
        else if typ.is_i128(&self.cx) || typ.is_u128(&self.cx) {
            128
        }
        else {
            unimplemented!();
        }
    }

    fn overflow_intrinsic_call(&mut self, intrinsic: &str, lhs: RValue<'gcc>, rhs: RValue<'gcc>, result: &PlaceRef<'tcx, RValue<'gcc>>) {
        let func = self.context.get_builtin_function(intrinsic);

        // Convert `i1` to a `bool`, and write it to the out parameter
        let res = self.current_func()
            // TODO: is it correct to use rhs type instead of the parameter typ?
            .new_local(None, rhs.get_type(), "binopOverflowResult")
            .get_address(None);
        let overflow = self.overflow_call(func, &[lhs, rhs, res], None);
        let val = res.dereference(None).to_rvalue();

        let dest = result.project_field(self, 0);
        self.store(val, dest.llval, dest.align);
        let dest = result.project_field(self, 1);
        self.store(overflow, dest.llval, dest.align);
    }

    fn pop_count(&self, value: RValue<'gcc>) -> RValue<'gcc> {
        // FIXME: this seems to generate a call to a function from a library that is not linked by
        // core, but linked by std.
        let value_type = value.get_type();
        let (popcount, expected_type) =
            if value_type.is_uchar(&self.cx) || value_type.is_ushort(&self.cx) || value_type.is_uint(&self.cx) {
                // TODO: implement more efficient version for uchar and ushort?
                ("__builtin_popcount", self.cx.uint_type)
            }
            else if value_type.is_ulong(&self.cx) {
                ("__builtin_popcountl", self.cx.ulong_type)
            }
            else if value_type.is_ulonglong(&self.cx) {
                ("__builtin_popcountll", self.cx.ulonglong_type)
            }
            else {
                unimplemented!("popcount for type {:?}", value_type);
            };

        let popcount = self.context.get_builtin_function(popcount);

        let value =
            if value_type != expected_type {
                self.context.new_cast(None, value, expected_type)
            }
            else {
                value
            };
        self.context.new_call(None, popcount, &[value])
    }

    // Algorithm from: https://blog.regehr.org/archives/1063
    fn rotate_left(&mut self, value: RValue<'gcc>, shift: RValue<'gcc>, width: u64) -> RValue<'gcc> {
        let lhs = self.shl(value, shift);
        let result_and =
            self.and(
                self.context.new_unary_op(None, UnaryOp::Minus, shift.get_type(), shift),
                self.context.new_rvalue_from_long(shift.get_type(), width as i64 - 1),
            );
        let rhs = self.lshr(shift, result_and);
        self.or(lhs, rhs)
    }

    fn saturating_add(&mut self, lhs: RValue<'gcc>, rhs: RValue<'gcc>, signed: bool, width: u64) -> RValue<'gcc> {
        let func = self.current_func.borrow().expect("func");

        let after_block = func.new_block("after");

        let result =
            if signed {
                // Algorithm from: https://stackoverflow.com/a/56531252/389119
                let func_name =
                    match width {
                        8 => "__builtin_add_overflow",
                        16 => "__builtin_add_overflow",
                        32 => "__builtin_sadd_overflow",
                        64 => "__builtin_saddll_overflow",
                        128 => "__builtin_saddll_overflow",
                        _ => unreachable!(),
                    };
                let overflow_func = self.context.get_builtin_function(func_name);
                let result_type = lhs.get_type();
                let res = func.new_local(None, result_type, "saturating_sum");
                let overflow = self.overflow_call(overflow_func, &[lhs, rhs, res.get_address(None)], None);

                let then_block = func.new_block("then");

                let unsigned_type = result_type.to_unsigned(&self.cx);
                let shifted = self.context.new_cast(None, lhs, unsigned_type) >> self.context.new_rvalue_from_int(unsigned_type, width as i32 - 1);
                let uint_max = self.context.new_unary_op(None, UnaryOp::BitwiseNegate, unsigned_type,
                    self.context.new_rvalue_from_int(unsigned_type, 0)
                );
                let int_max = uint_max >> self.context.new_rvalue_one(unsigned_type);
                then_block.add_assignment(None, res, self.context.new_cast(None, shifted + int_max, result_type));
                then_block.end_with_jump(None, after_block);

                self.block.expect("block").end_with_conditional(None, overflow, then_block, after_block);

                res.to_rvalue()
            }
            else {
                let res = lhs + rhs;
                let res_type = res.get_type();
                let res = func.new_local(None, res_type, "saturating_sum");
                let cond = self.context.new_comparison(None, ComparisonOp::LessThan, res, lhs);

                let then_block = func.new_block("then");
                let else_block = func.new_block("else");

                then_block.add_assignment(None, res, self.context.new_rvalue_from_long(res_type, 1));
                then_block.end_with_jump(None, after_block);

                else_block.end_with_jump(None, after_block);

                self.block.expect("block").end_with_conditional(None, cond, then_block, else_block);

                res.to_rvalue()
            };

        // NOTE: since jumps were added in a place rustc does not
        // expect, the current blocks in the state need to be updated.
        *self.current_block.borrow_mut() = Some(after_block);
        self.block = Some(after_block);

        result
    }

    // Algorithm from: https://locklessinc.com/articles/sat_arithmetic/
    fn saturating_sub(&mut self, lhs: RValue<'gcc>, rhs: RValue<'gcc>, signed: bool, width: u64) -> RValue<'gcc> {
        if signed {
            // Also based on algorithm from: https://stackoverflow.com/a/56531252/389119
            let func_name =
                match width {
                    8 => "__builtin_sub_overflow",
                    16 => "__builtin_sub_overflow",
                    32 => "__builtin_ssub_overflow",
                    64 => "__builtin_ssubll_overflow",
                    128 => "__builtin_ssubll_overflow",
                    _ => unreachable!(),
                };
            let overflow_func = self.context.get_builtin_function(func_name);
            let result_type = lhs.get_type();
            let func = self.current_func.borrow().expect("func");
            let res = func.new_local(None, result_type, "saturating_diff");
            let overflow = self.overflow_call(overflow_func, &[lhs, rhs, res.get_address(None)], None);

            let then_block = func.new_block("then");
            let after_block = func.new_block("after");

            let unsigned_type = result_type.to_unsigned(&self.cx);
            let shifted = self.context.new_cast(None, lhs, unsigned_type) >> self.context.new_rvalue_from_int(unsigned_type, width as i32 - 1);
            let uint_max = self.context.new_unary_op(None, UnaryOp::BitwiseNegate, unsigned_type,
                self.context.new_rvalue_from_int(unsigned_type, 0)
            );
            let int_max = uint_max >> self.context.new_rvalue_one(unsigned_type);
            then_block.add_assignment(None, res, self.context.new_cast(None, shifted + int_max, result_type));
            then_block.end_with_jump(None, after_block);

            self.block.expect("block").end_with_conditional(None, overflow, then_block, after_block);

            // NOTE: since jumps were added in a place rustc does not
            // expect, the current blocks in the state need to be updated.
            *self.current_block.borrow_mut() = Some(after_block);
            self.block = Some(after_block);

            res.to_rvalue()
        }
        else {
            let res = lhs - rhs;
            let comparison = self.context.new_comparison(None, ComparisonOp::LessThanEquals, res, lhs);
            let comparison = self.context.new_cast(None, comparison, lhs.get_type());
            let unary_op = self.context.new_unary_op(None, UnaryOp::Minus, comparison.get_type(), comparison);
            self.and(res, unary_op)
        }
    }
}

fn try_intrinsic<'gcc, 'tcx>(bx: &mut Builder<'_, 'gcc, 'tcx>, try_func: RValue<'gcc>, data: RValue<'gcc>, catch_func: RValue<'gcc>, dest: RValue<'gcc>) {
    if bx.sess().panic_strategy() == PanicStrategy::Abort {
        bx.call(try_func, &[data], None);
        // Return 0 unconditionally from the intrinsic call;
        // we can never unwind.
        let ret_align = bx.tcx.data_layout.i32_align.abi;
        bx.store(bx.const_i32(0), dest, ret_align);
    }
    else if wants_msvc_seh(bx.sess()) {
        unimplemented!();
        codegen_msvc_try(bx, try_func, data, catch_func, dest);
    }
    else {
        unimplemented!();
        codegen_gnu_try(bx, try_func, data, catch_func, dest);
    }
}

// MSVC's definition of the `rust_try` function.
//
// This implementation uses the new exception handling instructions in LLVM
// which have support in LLVM for SEH on MSVC targets. Although these
// instructions are meant to work for all targets, as of the time of this
// writing, however, LLVM does not recommend the usage of these new instructions
// as the old ones are still more optimized.
fn codegen_msvc_try<'a, 'gcc, 'tcx>(bx: &mut Builder<'a, 'gcc, 'tcx>, try_func: RValue<'gcc>, data: RValue<'gcc>, catch_func: RValue<'gcc>, dest: RValue<'gcc>) {
    unimplemented!();
    /*let llfn = get_rust_try_fn(bx, &mut |mut bx| {
        bx.set_personality_fn(bx.eh_personality());
        bx.sideeffect();

        let mut normal = bx.build_sibling_block("normal");
        let mut catchswitch = bx.build_sibling_block("catchswitch");
        let mut catchpad = bx.build_sibling_block("catchpad");
        let mut caught = bx.build_sibling_block("caught");

        let try_func = llvm::get_param(bx.llfn(), 0);
        let data = llvm::get_param(bx.llfn(), 1);
        let catch_func = llvm::get_param(bx.llfn(), 2);

        // We're generating an IR snippet that looks like:
        //
        //   declare i32 @rust_try(%try_func, %data, %catch_func) {
        //      %slot = alloca u8*
        //      invoke %try_func(%data) to label %normal unwind label %catchswitch
        //
        //   normal:
        //      ret i32 0
        //
        //   catchswitch:
        //      %cs = catchswitch within none [%catchpad] unwind to caller
        //
        //   catchpad:
        //      %tok = catchpad within %cs [%type_descriptor, 0, %slot]
        //      %ptr = load %slot
        //      call %catch_func(%data, %ptr)
        //      catchret from %tok to label %caught
        //
        //   caught:
        //      ret i32 1
        //   }
        //
        // This structure follows the basic usage of throw/try/catch in LLVM.
        // For example, compile this C++ snippet to see what LLVM generates:
        //
        //      #include <stdint.h>
        //
        //      struct rust_panic {
        //          rust_panic(const rust_panic&);
        //          ~rust_panic();
        //
        //          uint64_t x[2];
        //      };
        //
        //      int __rust_try(
        //          void (*try_func)(void*),
        //          void *data,
        //          void (*catch_func)(void*, void*) noexcept
        //      ) {
        //          try {
        //              try_func(data);
        //              return 0;
        //          } catch(rust_panic& a) {
        //              catch_func(data, &a);
        //              return 1;
        //          }
        //      }
        //
        // More information can be found in libstd's seh.rs implementation.
        let ptr_align = bx.tcx().data_layout.pointer_align.abi;
        let slot = bx.alloca(bx.type_i8p(), ptr_align);
        bx.invoke(try_func, &[data], normal.llbb(), catchswitch.llbb(), None);

        normal.ret(bx.const_i32(0));

        let cs = catchswitch.catch_switch(None, None, 1);
        catchswitch.add_handler(cs, catchpad.llbb());

        // We can't use the TypeDescriptor defined in libpanic_unwind because it
        // might be in another DLL and the SEH encoding only supports specifying
        // a TypeDescriptor from the current module.
        //
        // However this isn't an issue since the MSVC runtime uses string
        // comparison on the type name to match TypeDescriptors rather than
        // pointer equality.
        //
        // So instead we generate a new TypeDescriptor in each module that uses
        // `try` and let the linker merge duplicate definitions in the same
        // module.
        //
        // When modifying, make sure that the type_name string exactly matches
        // the one used in src/libpanic_unwind/seh.rs.
        let type_info_vtable = bx.declare_global("??_7type_info@@6B@", bx.type_i8p());
        let type_name = bx.const_bytes(b"rust_panic\0");
        let type_info =
            bx.const_struct(&[type_info_vtable, bx.const_null(bx.type_i8p()), type_name], false);
        let tydesc = bx.declare_global("__rust_panic_type_info", bx.val_ty(type_info));
        unsafe {
            llvm::LLVMRustSetLinkage(tydesc, llvm::Linkage::LinkOnceODRLinkage);
            llvm::SetUniqueComdat(bx.llmod, tydesc);
            llvm::LLVMSetInitializer(tydesc, type_info);
        }

        // The flag value of 8 indicates that we are catching the exception by
        // reference instead of by value. We can't use catch by value because
        // that requires copying the exception object, which we don't support
        // since our exception object effectively contains a Box.
        //
        // Source: MicrosoftCXXABI::getAddrOfCXXCatchHandlerType in clang
        let flags = bx.const_i32(8);
        let funclet = catchpad.catch_pad(cs, &[tydesc, flags, slot]);
        let ptr = catchpad.load(slot, ptr_align);
        catchpad.call(catch_func, &[data, ptr], Some(&funclet));

        catchpad.catch_ret(&funclet, caught.llbb());

        caught.ret(bx.const_i32(1));
    });

    // Note that no invoke is used here because by definition this function
    // can't panic (that's what it's catching).
    let ret = bx.call(llfn, &[try_func, data, catch_func], None);
    let i32_align = bx.tcx().data_layout.i32_align.abi;
    bx.store(ret, dest, i32_align);*/
}

// Definition of the standard `try` function for Rust using the GNU-like model
// of exceptions (e.g., the normal semantics of LLVM's `landingpad` and `invoke`
// instructions).
//
// This codegen is a little surprising because we always call a shim
// function instead of inlining the call to `invoke` manually here. This is done
// because in LLVM we're only allowed to have one personality per function
// definition. The call to the `try` intrinsic is being inlined into the
// function calling it, and that function may already have other personality
// functions in play. By calling a shim we're guaranteed that our shim will have
// the right personality function.
fn codegen_gnu_try<'a, 'gcc, 'tcx>(bx: &mut Builder<'a, 'gcc, 'tcx>, try_func: RValue<'gcc>, data: RValue<'gcc>, catch_func: RValue<'gcc>, dest: RValue<'gcc>) {
    unimplemented!();
    /*let llfn = get_rust_try_fn(bx, &mut |mut bx| {
        // Codegens the shims described above:
        //
        //   bx:
        //      invoke %try_func(%data) normal %normal unwind %catch
        //
        //   normal:
        //      ret 0
        //
        //   catch:
        //      (%ptr, _) = landingpad
        //      call %catch_func(%data, %ptr)
        //      ret 1

        bx.sideeffect();

        let mut then = bx.build_sibling_block("then");
        let mut catch = bx.build_sibling_block("catch");

        let try_func = llvm::get_param(bx.llfn(), 0);
        let data = llvm::get_param(bx.llfn(), 1);
        let catch_func = llvm::get_param(bx.llfn(), 2);
        bx.invoke(try_func, &[data], then.llbb(), catch.llbb(), None);
        then.ret(bx.const_i32(0));

        // Type indicator for the exception being thrown.
        //
        // The first value in this tuple is a pointer to the exception object
        // being thrown.  The second value is a "selector" indicating which of
        // the landing pad clauses the exception's type had been matched to.
        // rust_try ignores the selector.
        let lpad_ty = bx.type_struct(&[bx.type_i8p(), bx.type_i32()], false);
        let vals = catch.landing_pad(lpad_ty, bx.eh_personality(), 1);
        let tydesc = match bx.tcx().lang_items().eh_catch_typeinfo() {
            Some(tydesc) => {
                let tydesc = bx.get_static(tydesc);
                bx.bitcast(tydesc, bx.type_i8p())
            }
            None => bx.const_null(bx.type_i8p()),
        };
        catch.add_clause(vals, tydesc);
        let ptr = catch.extract_value(vals, 0);
        catch.call(catch_func, &[data, ptr], None);
        catch.ret(bx.const_i32(1));
    });

    // Note that no invoke is used here because by definition this function
    // can't panic (that's what it's catching).
    let ret = bx.call(llfn, &[try_func, data, catch_func], None);
    let i32_align = bx.tcx().data_layout.i32_align.abi;
    bx.store(ret, dest, i32_align);*/
}
