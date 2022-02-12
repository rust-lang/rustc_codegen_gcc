use std::cmp::Ordering;

use gccjit::{RValue, Type, ToRValue};
use rustc_codegen_ssa::base::compare_simd_types;
use rustc_codegen_ssa::common::{TypeKind, span_invalid_monomorphization_error};
use rustc_codegen_ssa::mir::operand::OperandRef;
use rustc_codegen_ssa::traits::{BaseTypeMethods, BuilderMethods};
use rustc_hir as hir;
use rustc_middle::span_bug;
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_middle::ty::{self, Ty};
use rustc_span::{Span, Symbol, sym};

use crate::builder::Builder;
use crate::intrinsic;

pub fn generic_simd_intrinsic<'a, 'gcc, 'tcx>(bx: &mut Builder<'a, 'gcc, 'tcx>, name: Symbol, callee_ty: Ty<'tcx>, args: &[OperandRef<'tcx, RValue<'gcc>>], ret_ty: Ty<'tcx>, llret_ty: Type<'gcc>, span: Span) -> Result<RValue<'gcc>, ()> {
    // macros for error handling:
    macro_rules! emit_error {
        ($msg: tt) => {
            emit_error!($msg, )
        };
        ($msg: tt, $($fmt: tt)*) => {
            span_invalid_monomorphization_error(
                bx.sess(), span,
                &format!(concat!("invalid monomorphization of `{}` intrinsic: ", $msg),
                         name, $($fmt)*));
        }
    }

    macro_rules! return_error {
        ($($fmt: tt)*) => {
            {
                emit_error!($($fmt)*);
                return Err(());
            }
        }
    }

    macro_rules! require {
        ($cond: expr, $($fmt: tt)*) => {
            if !$cond {
                return_error!($($fmt)*);
            }
        };
    }

    macro_rules! require_simd {
        ($ty: expr, $position: expr) => {
            require!($ty.is_simd(), "expected SIMD {} type, found non-SIMD `{}`", $position, $ty)
        };
    }

    let tcx = bx.tcx();
    let sig =
        tcx.normalize_erasing_late_bound_regions(ty::ParamEnv::reveal_all(), callee_ty.fn_sig(tcx));
    let arg_tys = sig.inputs();
    let name_str = name.as_str();

    // every intrinsic below takes a SIMD vector as its first argument
    require_simd!(arg_tys[0], "input");
    let in_ty = arg_tys[0];

    let comparison = match name {
        sym::simd_eq => Some(hir::BinOpKind::Eq),
        sym::simd_ne => Some(hir::BinOpKind::Ne),
        sym::simd_lt => Some(hir::BinOpKind::Lt),
        sym::simd_le => Some(hir::BinOpKind::Le),
        sym::simd_gt => Some(hir::BinOpKind::Gt),
        sym::simd_ge => Some(hir::BinOpKind::Ge),
        _ => None,
    };

    let (in_len, in_elem) = arg_tys[0].simd_size_and_type(bx.tcx());
    if let Some(cmp_op) = comparison {
        require_simd!(ret_ty, "return");

        let (out_len, out_ty) = ret_ty.simd_size_and_type(bx.tcx());
        require!(
            in_len == out_len,
            "expected return type with length {} (same as input type `{}`), \
             found `{}` with length {}",
            in_len,
            in_ty,
            ret_ty,
            out_len
        );
        require!(
            bx.type_kind(bx.element_type(llret_ty)) == TypeKind::Integer,
            "expected return type with integer elements, found `{}` with non-integer `{}`",
            ret_ty,
            out_ty
        );

        return Ok(compare_simd_types(
            bx,
            args[0].immediate(),
            args[1].immediate(),
            in_elem,
            llret_ty,
            cmp_op,
        ));
    }

    if let Some(stripped) = name_str.strip_prefix("simd_shuffle") {
        let n: u64 = stripped.parse().unwrap_or_else(|_| {
            span_bug!(span, "bad `simd_shuffle` instruction only caught in codegen?")
        });

        require_simd!(ret_ty, "return");

        let (out_len, out_ty) = ret_ty.simd_size_and_type(bx.tcx());
        require!(
            out_len == n,
            "expected return type of length {}, found `{}` with length {}",
            n,
            ret_ty,
            out_len
        );
        require!(
            in_elem == out_ty,
            "expected return element type `{}` (element of input `{}`), \
             found `{}` with element type `{}`",
            in_elem,
            in_ty,
            ret_ty,
            out_ty
        );

        let vector = args[2].immediate();

        return Ok(bx.shuffle_vector(
            args[0].immediate(),
            args[1].immediate(),
            vector,
        ));
    }

    if name == sym::simd_extract {
        require!(
            ret_ty == in_elem,
            "expected return type `{}` (element of input `{}`), found `{}`",
            in_elem,
            in_ty,
            ret_ty
        );
        let vector = args[0].immediate();
        // FIXME: dyncast_vector() should not need unqualified().
        let vector_type = vector.get_type().unqualified().dyncast_vector().expect("vector type");
        let element_type = vector_type.get_element_type();
        let array_type = bx.context.new_array_type(None, element_type, in_len as i32);
        let array = bx.context.new_bitcast(None, vector, array_type);
        return Ok(bx.context.new_array_access(None, array, args[1].immediate()).to_rvalue());
    }

    if name == sym::simd_cast {
        require_simd!(ret_ty, "return");
        let (out_len, out_elem) = ret_ty.simd_size_and_type(bx.tcx());
        require!(
            in_len == out_len,
            "expected return type with length {} (same as input type `{}`), \
                  found `{}` with length {}",
            in_len,
            in_ty,
            ret_ty,
            out_len
        );
        // casting cares about nominal type, not just structural type
        if in_elem == out_elem {
            return Ok(args[0].immediate());
        }

        enum Style {
            Float,
            Int(/* is signed? */ bool),
            Unsupported,
        }

        let (in_style, in_width) = match in_elem.kind() {
            // vectors of pointer-sized integers should've been
            // disallowed before here, so this unwrap is safe.
            ty::Int(i) => (
                Style::Int(true),
                i.normalize(bx.tcx().sess.target.pointer_width).bit_width().unwrap(),
            ),
            ty::Uint(u) => (
                Style::Int(false),
                u.normalize(bx.tcx().sess.target.pointer_width).bit_width().unwrap(),
            ),
            ty::Float(f) => (Style::Float, f.bit_width()),
            _ => (Style::Unsupported, 0),
        };
        let (out_style, out_width) = match out_elem.kind() {
            ty::Int(i) => (
                Style::Int(true),
                i.normalize(bx.tcx().sess.target.pointer_width).bit_width().unwrap(),
            ),
            ty::Uint(u) => (
                Style::Int(false),
                u.normalize(bx.tcx().sess.target.pointer_width).bit_width().unwrap(),
            ),
            ty::Float(f) => (Style::Float, f.bit_width()),
            _ => (Style::Unsupported, 0),
        };

        match (in_style, out_style) {
            (Style::Int(in_is_signed), Style::Int(_)) => {
                return Ok(match in_width.cmp(&out_width) {
                    Ordering::Greater => bx.trunc(args[0].immediate(), llret_ty),
                    Ordering::Equal => args[0].immediate(),
                    Ordering::Less => {
                        if in_is_signed {
                            match (in_width, out_width) {
                                (8, 16) => {
                                    // FIXME: the function _mm_cvtepi8_epi16 should directly
                                    // call an intrinsic equivalent to __builtin_ia32_pmovsxbw128 so that
                                    // we can generate a call to it.
                                    let vector_type = bx.context.new_vector_type(bx.cx.i16_type, 8);
                                    let vector = args[0].immediate();
                                    let array_type = bx.context.new_array_type(None, bx.cx.i8_type, 8);
                                    let array = bx.context.new_bitcast(None, vector, array_type);

                                    fn cast_vec_element<'a, 'gcc, 'tcx>(bx: &mut Builder<'a, 'gcc, 'tcx>, array: RValue<'gcc>, index: i32) -> RValue<'gcc> {
                                        let index = bx.context.new_rvalue_from_int(bx.int_type, index);
                                        bx.context.new_cast(None, bx.context.new_array_access(None, array, index).to_rvalue(), bx.i16_type)
                                    }

                                    bx.context.new_rvalue_from_vector(None, vector_type, &[
                                        cast_vec_element(bx, array, 0),
                                        cast_vec_element(bx, array, 1),
                                        cast_vec_element(bx, array, 2),
                                        cast_vec_element(bx, array, 3),
                                        cast_vec_element(bx, array, 4),
                                        cast_vec_element(bx, array, 5),
                                        cast_vec_element(bx, array, 6),
                                        cast_vec_element(bx, array, 7),
                                    ])
                                },
                                _ => unimplemented!("in: {}, out: {}", in_width, out_width),
                            }
                            //bx.sext(args[0].immediate(), llret_ty)
                        } else {
                            unimplemented!();
                            //bx.zext(args[0].immediate(), llret_ty)
                        }
                    }
                });
            }
            (Style::Int(in_is_signed), Style::Float) => {
                return Ok(if in_is_signed {
                    unimplemented!();
                    //bx.sitofp(args[0].immediate(), llret_ty)
                } else {
                    unimplemented!();
                    //bx.uitofp(args[0].immediate(), llret_ty)
                });
            }
            (Style::Float, Style::Int(out_is_signed)) => {
                return Ok(match out_is_signed {
                    false => unimplemented!(),
                        //bx.fptoui(args[0].immediate(), llret_ty),
                    true => unimplemented!(),
                        //bx.fptosi(args[0].immediate(), llret_ty),
                });
            }
            (Style::Float, Style::Float) => {
                return Ok(match in_width.cmp(&out_width) {
                    Ordering::Greater => unimplemented!(), //bx.fptrunc(args[0].immediate(), llret_ty),
                    Ordering::Equal => unimplemented!(), //args[0].immediate(),
                    Ordering::Less => unimplemented!(), //bx.fpext(args[0].immediate(), llret_ty),
                });
            }
            _ => { /* Unsupported. Fallthrough. */ }
        }
        require!(
            false,
            "unsupported cast from `{}` with element `{}` to `{}` with element `{}`",
            in_ty,
            in_elem,
            ret_ty,
            out_elem
        );
    }

    macro_rules! arith_binary {
        ($($name: ident: $($($p: ident),* => $call: ident),*;)*) => {
            $(if name == sym::$name {
                match in_elem.kind() {
                    $($(ty::$p(_))|* => {
                        return Ok(bx.$call(args[0].immediate(), args[1].immediate()))
                    })*
                    _ => {},
                }
                require!(false,
                         "unsupported operation on `{}` with element `{}`",
                         in_ty,
                         in_elem)
            })*
        }
    }

    fn simd_simple_float_intrinsic<'gcc, 'tcx>(
        name: Symbol,
        in_elem: &rustc_middle::ty::TyS<'_>,
        in_ty: &rustc_middle::ty::TyS<'_>,
        in_len: u64,
        bx: &mut Builder<'_, 'gcc, 'tcx>,
        span: Span,
        args: &[OperandRef<'tcx, RValue<'gcc>>],
    ) -> Result<RValue<'gcc>, ()> {
        macro_rules! emit_error {
            ($msg: tt) => {
                emit_error!($msg, )
            };
            ($msg: tt, $($fmt: tt)*) => {
                span_invalid_monomorphization_error(
                    bx.sess(), span,
                    &format!(concat!("invalid monomorphization of `{}` intrinsic: ", $msg),
                             name, $($fmt)*));
            }
        }
        macro_rules! return_error {
            ($($fmt: tt)*) => {
                {
                    emit_error!($($fmt)*);
                    return Err(());
                }
            }
        }

        let (elem_ty_str, elem_ty) =
            if let ty::Float(f) = in_elem.kind() {
                let elem_ty = bx.cx.type_float_from_ty(*f);
                match f.bit_width() {
                    32 => ("f32", elem_ty),
                    64 => ("f64", elem_ty),
                    _ => {
                        return_error!(
                            "unsupported element type `{}` of floating-point vector `{}`",
                            f.name_str(),
                            in_ty
                        );
                    }
                }
            }
            else {
                return_error!("`{}` is not a floating-point type", in_ty);
            };

        let vec_ty = bx.cx.type_vector(elem_ty, in_len);

        let (intr_name, fn_ty) =
            match name {
                sym::simd_ceil => ("ceil", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_fabs => ("fabs", bx.type_func(&[vec_ty], vec_ty)), // TODO: pand with 170141183420855150465331762880109871103
                sym::simd_fcos => ("cos", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_fexp2 => ("exp2", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_fexp => ("exp", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_flog10 => ("log10", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_flog2 => ("log2", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_flog => ("log", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_floor => ("floor", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_fma => ("fma", bx.type_func(&[vec_ty, vec_ty, vec_ty], vec_ty)),
                sym::simd_fpowi => ("powi", bx.type_func(&[vec_ty, bx.type_i32()], vec_ty)),
                sym::simd_fpow => ("pow", bx.type_func(&[vec_ty, vec_ty], vec_ty)),
                sym::simd_fsin => ("sin", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_fsqrt => ("sqrt", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_round => ("round", bx.type_func(&[vec_ty], vec_ty)),
                sym::simd_trunc => ("trunc", bx.type_func(&[vec_ty], vec_ty)),
                _ => return_error!("unrecognized intrinsic `{}`", name),
            };
        let llvm_name = &format!("llvm.{0}.v{1}{2}", intr_name, in_len, elem_ty_str);
        let function = intrinsic::llvm::intrinsic(llvm_name, &bx.cx);
        let function: RValue<'gcc> = unsafe { std::mem::transmute(function) };
        let c = bx.call(fn_ty, function, &args.iter().map(|arg| arg.immediate()).collect::<Vec<_>>(), None);
        Ok(c)
    }

    /*if std::matches!(
        name,
        sym::simd_ceil
            | sym::simd_fabs
            | sym::simd_fcos
            | sym::simd_fexp2
            | sym::simd_fexp
            | sym::simd_flog10
            | sym::simd_flog2
            | sym::simd_flog
            | sym::simd_floor
            | sym::simd_fma
            | sym::simd_fpow
            | sym::simd_fpowi
            | sym::simd_fsin
            | sym::simd_fsqrt
            | sym::simd_round
            | sym::simd_trunc
    ) {
        return simd_simple_float_intrinsic(name, in_elem, in_ty, in_len, bx, span, args);
    }*/

    arith_binary! {
        simd_add: Uint, Int => add, Float => fadd;
        simd_sub: Uint, Int => sub, Float => fsub;
        simd_mul: Uint, Int => mul, Float => fmul;
        simd_div: Uint => udiv, Int => sdiv, Float => fdiv;
        simd_rem: Uint => urem, Int => srem, Float => frem;
        simd_shl: Uint, Int => shl;
        simd_shr: Uint => lshr, Int => ashr;
        simd_and: Uint, Int => and;
        simd_or: Uint, Int => or; // FIXME(antoyo): calling `or` might not work on vectors.
        simd_xor: Uint, Int => xor;
    }

    macro_rules! arith_unary {
        ($($name: ident: $($($p: ident),* => $call: ident),*;)*) => {
            $(if name == sym::$name {
                match in_elem.kind() {
                    $($(ty::$p(_))|* => {
                        return Ok(bx.$call(args[0].immediate()))
                    })*
                    _ => {},
                }
                require!(false,
                         "unsupported operation on `{}` with element `{}`",
                         in_ty,
                         in_elem)
            })*
        }
    }

    arith_unary! {
        simd_neg: Int => neg, Float => fneg;
    }

    unimplemented!("simd {}", name);
}
