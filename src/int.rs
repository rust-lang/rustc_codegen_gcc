//! Module to handle integer operations.
//! This module exists because some integer types are not supported on some gcc platforms, e.g.
//! 128-bit integers on 32-bit platforms and thus requires to be handled manually.

// FIXME: this should be rewritten in a recurisve way, i.e. 128-bit integers should be written
// by using 64-bit integer operations. If those are not supported as way, that will recursively
// use 32-bit integer operations.

use std::convert::TryFrom;

use gccjit::{ComparisonOp, FunctionType, RValue, ToRValue, Type, UnaryOp};
use rustc_codegen_ssa::common::{IntPredicate, TypeKind};
use rustc_codegen_ssa::traits::{BackendTypes, BaseTypeMethods, BuilderMethods, OverflowOp};
use rustc_middle::ty::Ty;

use crate::builder::ToGccComp;
use crate::{builder::Builder, common::{SignType, TypeReflection}, context::CodegenCx};

impl<'a, 'gcc, 'tcx> Builder<'a, 'gcc, 'tcx> {
    pub fn gcc_rem(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type(a_type) && self.supports_native_int_type(b_type) {
            a % b
        }
        else {
            let a_int_type = self.get_int_type(a_type);
            /*
             * 32-bit unsigned %:  __umodsi3
             * 32-bit signed %:    __modsi3
             * 64-bit unsigned %:  __umoddi3
             * 64-bit signed %:    __moddi3
             * 128-bit unsigned %: __umodti3
             * 128-bit signed %:   __modti3
             */
            let sign =
                if a_int_type.signed {
                    ""
                }
                else {
                    "u"
                };
            let size =
                match a_int_type.bits {
                    32 => 's',
                    64 => 'd',
                    128 => 't',
                    n => unimplemented!("modulo operation for integer of size {}", n),
                };
            let func_name = format!("__{}mod{}i3", sign, size);
            let param_a = self.context.new_parameter(None, a_type, "n");
            let param_b = self.context.new_parameter(None, b_type, "d");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    pub fn gcc_not(&self, a: RValue<'gcc>) -> RValue<'gcc> {
        let typ = a.get_type();
        let operation =
            if typ.is_bool() {
                UnaryOp::LogicalNegate
            }
            else {
                UnaryOp::BitwiseNegate
            };
        if self.supports_native_int_type_or_bool(typ) {
            self.cx.context.new_unary_op(None, operation, typ, a)
        }
        else {
            // TODO: use __negdi2 and __negti2 instead?
            let int_type = self.cx.get_int_type(typ);
            let src_size = int_type.bits;
            let src_element_size = int_type.element_size;
            let array_type = int_type.typ;
            let element_type = array_type.dyncast_array().expect("element type");
            let element_count = src_size / src_element_size;
            let mut values = vec![];
            for i in 0..element_count {
                let element_value = self.cx.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.int_type, i as i32));
                values.push(self.cx.context.new_unary_op(None, operation, element_type, element_value));
            }
            self.cx.context.new_array_constructor(None, array_type, &values)
        }
    }

    pub fn gcc_neg(&self, a: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        if self.supports_native_int_type(a_type) {
            self.cx.context.new_unary_op(None, UnaryOp::Minus, a.get_type(), a)
        }
        else {
            /*
             * 64-bit -:  __negdi2
             * 128-bit -: __negti2
             */
            //a
            let a_int_type = self.get_int_type(a_type);
            let size =
                match a_int_type.bits {
                    64 => 'd',
                    128 => 't',
                    n => unimplemented!("unary negation for integer of size {}", n),
                };
            let func_name = format!("__neg{}i2", size);
            let param_a = self.context.new_parameter(None, a_type, "a");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a], func_name, false);
            self.context.new_call(None, func, &[a])
        }
    }

    pub fn gcc_and(&self, a: RValue<'gcc>, mut b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            if a_type != b_type {
                b = self.context.new_cast(None, b, a_type);
            }
            a & b
        }
        else {
            let int_type = self.get_int_type(a_type);
            let dest_size = int_type.bits as u32;
            let dest_element_size = int_type.element_size as u32;
            let factor = (dest_size / dest_element_size) as i32;
            let mut values = vec![];
            for i in 0..factor {
                let element_a = self.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.cx.int_type, i));
                let element_b = self.context.new_array_access(None, b, self.context.new_rvalue_from_int(self.cx.int_type, i));
                values.push(element_a.to_rvalue() & element_b.to_rvalue());
            }
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    pub fn gcc_lshr(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        let a_native = self.supports_native_int_type(a_type);
        let b_native = self.supports_native_int_type(b_type);
        if a_native && b_native {
            // FIXME(antoyo): remove the casts when libgccjit can shift an unsigned number by an unsigned number.
            // TODO(antoyo): cast to unsigned to do a logical shift if that does not work.
            if a_type.is_unsigned(self) && b_type.is_signed(self) {
                let a = self.context.new_cast(None, a, b_type);
                let result = a >> b;
                self.context.new_cast(None, result, a_type)
            }
            else if a_type.is_signed(self) && b_type.is_unsigned(self) {
                let b = self.context.new_cast(None, b, a_type);
                a >> b
            }
            else {
                a >> b
            }
        }
        else if a_native && !b_native {
            self.gcc_lshr(a, self.gcc_int_cast(b, a_type))
        }
        else {
            // NOTE: we cannot use the lshr builtin because it's calling hi() (to get the most
            // significant half of the number) which uses lshr.

            let int_type = self.cx.get_int_type(a_type);
            let size = int_type.bits;
            let element_size = int_type.element_size;
            let element_type = int_type.typ.dyncast_array().expect("element type");

            let casted_b = self.gcc_int_cast(b, element_type);

            let casted_b_var = self.current_func().new_local(None, casted_b.get_type(), "casted_b"); // TODO: remove.
            self.llbb().add_assignment(None, casted_b_var, casted_b); // TODO: remove.

            // FIXME: the reverse shift won't work if shifting for more than element_size.
            let element_size_value = self.context.new_rvalue_from_int(element_type, element_size as i32);
            let reverse_shift = element_size_value - casted_b;

            let reverse_shift_var = self.current_func().new_local(None, casted_b.get_type(), "reverse_shift"); // TODO: remove.
            self.llbb().add_assignment(None, reverse_shift_var, reverse_shift); // TODO: remove.

            // TODO: take endianness into account.
            let mut current_index = (size / element_size - 1) as i32;
            let mut overflow = self.context.new_rvalue_zero(element_type);
            let mut values = vec![];
            // TODO: remove all the temporary variables created here for debugging purposes.
            while current_index >= 0 {
                let current_element = self.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.int_type, current_index)).to_rvalue();

                let current_element_var = self.current_func().new_local(None, current_element.get_type(), &format!("current_element_{}", current_index)); // TODO: remove.
                self.llbb().add_assignment(None, current_element_var, current_element); // TODO: remove.

                let shifted_var = self.current_func().new_local(None, current_element.get_type(), &format!("shifted_var_{}", current_index)); // TODO: remove.

                // NOTE: shifting an integer by more than its width is undefined behavior.
                // So we apply a mask to get a value of 0 in this case.
                let shifted_value = current_element_var.to_rvalue() >> casted_b_var.to_rvalue();
                let mask = self.context.new_comparison(None, ComparisonOp::LessThan, casted_b_var.to_rvalue(), element_size_value);
                let mask = self.context.new_cast(None, mask, element_type);
                let mask = self.context.new_unary_op(None, UnaryOp::Minus, element_type, mask);
                self.llbb().add_assignment(None, shifted_var, shifted_value & mask); // TODO: remove.

                let new_element = shifted_var.to_rvalue() | overflow;
                values.push(new_element);
                current_index -= 1;

                let overflow_var = self.current_func().new_local(None, current_element.get_type(), &format!("overflow_var_{}", current_index)); // TODO: remove.
                // TODO: check if we need to apply a mask for the reverse shift as well.
                self.llbb().add_assignment(None, overflow_var, current_element_var.to_rvalue() << reverse_shift_var.to_rvalue()); // TODO: remove.

                overflow = overflow_var.to_rvalue();
            }
            // TODO: do I need to use overflow here?
            // NOTE: reverse because we inserted in the reverse order, i.e. we added the last
            // element at the start.
            values.reverse();
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    pub fn gcc_add(&self, a: RValue<'gcc>, mut b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            // FIXME(antoyo): this should not be required.
            // TODO(antoyo): explain why it is required for now.
            if format!("{:?}", a_type) != format!("{:?}", b_type) {
                b = self.context.new_cast(None, b, a_type);
            }
            a + b
        }
        else {
            let int_type = self.get_int_type(a_type);
            let func_name =
                match (int_type.signed, int_type.bits) {
                    (true, 32) => "__addvsi3", // FIXME: that's trapping on overflow.
                    (true, 64) => "__addvdi3", // FIXME: that's trapping on overflow.
                    (true, 128) => "__rust_i128_add",
                    (false, 128) => "__rust_u128_add",
                    (_, size) => unimplemented!("addition for integer of size {}", size),
                };
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    pub fn gcc_mul(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            a * b
        }
        else {
            /*
             * 64-bit, signed: __muldi3
             * 128-bit, signed: __multi3
             */
            let int_type = self.get_int_type(a_type);
            let func_name =
                match int_type.bits {
                    64 => "__muldi3",
                    128 => "__multi3",
                    size => unimplemented!("multiplication for integer of size {}", size),
                };
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    pub fn gcc_sub(&self, a: RValue<'gcc>, mut b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            if a.get_type() != b.get_type() {
                b = self.context.new_cast(None, b, a.get_type());
            }
            a - b
        }
        else {
            let int_type = self.get_int_type(a_type);
            let func_name =
                match (int_type.signed, int_type.bits) {
                    (true, 32) => "__subvsi3", // FIXME: that's trapping on overflow.
                    (true, 64) => "__subvdi3", // FIXME: that's trapping on overflow.
                    (true, 128) => "__rust_i128_sub",
                    (false, 128) => "__rust_u128_sub",
                    (_, size) => unimplemented!("subtraction for integer of size {}", size),
                };
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    // TODO: merge with gcc_udiv.
    pub fn gcc_sdiv(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            // TODO(antoyo): convert the arguments to signed?
            a / b
        }
        else {
            /*
             * 32-bit, signed: __divsi3
             * 64-bit, signed: __divdi3
             * 128-bit, signed: __divti3
             */
            let int_type = self.get_int_type(a_type);
            // TODO: check if the type is unsigned?
            let size =
                match int_type.bits {
                    32 => 's',
                    64 => 'd',
                    128 => 't',
                    size => unimplemented!("signed division not implemented for integers of size {}", size),
                };
            let func_name = format!("__div{}i3", size);
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    pub fn gcc_udiv(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            // TODO(antoyo): convert the arguments to unsigned?
            a / b
        }
        else {
            /*
             * 32-bit, unsigned: __udivsi3
             * 64-bit, unsigned: __udivdi3
             * 128-bit, unsigned: __udivti3
             */
            let int_type = self.get_int_type(a_type);
            // TODO: check if the type is unsigned?
            let size =
                match int_type.bits {
                    32 => 's',
                    64 => 'd',
                    128 => 't',
                    size => unimplemented!("unsigned division not implemented for integers of size {}", size),
                };
            let func_name = format!("__udiv{}i3", size);
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, a_type, &[param_a, param_b], func_name, false);
            self.context.new_call(None, func, &[a, b])
        }
    }

    pub fn gcc_checked_binop(&self, oop: OverflowOp, typ: Ty<'_>, lhs: <Self as BackendTypes>::Value, rhs: <Self as BackendTypes>::Value) -> (<Self as BackendTypes>::Value, <Self as BackendTypes>::Value) {
        use rustc_middle::ty::{Int, IntTy::*, Uint, UintTy::*};

        let new_kind =
            match typ.kind() {
                Int(t @ Isize) => Int(t.normalize(self.tcx.sess.target.pointer_width)),
                Uint(t @ Usize) => Uint(t.normalize(self.tcx.sess.target.pointer_width)),
                t @ (Uint(_) | Int(_)) => t.clone(),
                _ => panic!("tried to get overflow intrinsic for op applied to non-int type"),
            };

        // TODO(antoyo): remove duplication with intrinsic?
        let name =
            if self.supports_native_int_type(lhs.get_type()) {
                match oop {
                    OverflowOp::Add =>
                        match new_kind {
                            Int(I8) => "__builtin_add_overflow",
                            Int(I16) => "__builtin_add_overflow",
                            Int(I32) => "__builtin_sadd_overflow",
                            Int(I64) => "__builtin_saddll_overflow",
                            Int(I128) => "__builtin_add_overflow",

                            Uint(U8) => "__builtin_add_overflow",
                            Uint(U16) => "__builtin_add_overflow",
                            Uint(U32) => "__builtin_uadd_overflow",
                            Uint(U64) => "__builtin_uaddll_overflow",
                            Uint(U128) => "__builtin_add_overflow",

                            _ => unreachable!(),
                        },
                    OverflowOp::Sub =>
                        match new_kind {
                            Int(I8) => "__builtin_sub_overflow",
                            Int(I16) => "__builtin_sub_overflow",
                            Int(I32) => "__builtin_ssub_overflow",
                            Int(I64) => "__builtin_ssubll_overflow",
                            Int(I128) => "__builtin_sub_overflow",

                            Uint(U8) => "__builtin_sub_overflow",
                            Uint(U16) => "__builtin_sub_overflow",
                            Uint(U32) => "__builtin_usub_overflow",
                            Uint(U64) => "__builtin_usubll_overflow",
                            Uint(U128) => "__builtin_sub_overflow",

                            _ => unreachable!(),
                        },
                    OverflowOp::Mul =>
                        match new_kind {
                            Int(I8) => "__builtin_mul_overflow",
                            Int(I16) => "__builtin_mul_overflow",
                            Int(I32) => "__builtin_smul_overflow",
                            Int(I64) => "__builtin_smulll_overflow",
                            Int(I128) => "__builtin_mul_overflow",

                            Uint(U8) => "__builtin_mul_overflow",
                            Uint(U16) => "__builtin_mul_overflow",
                            Uint(U32) => "__builtin_umul_overflow",
                            Uint(U64) => "__builtin_umulll_overflow",
                            Uint(U128) => "__builtin_mul_overflow",

                            _ => unreachable!(),
                        },
                }
            }
            else {
                match new_kind {
                    Int(I128) | Uint(U128) => {
                        let func_name =
                            match oop {
                                OverflowOp::Add =>
                                    match new_kind {
                                        Int(I128) => "__rust_i128_addo",
                                        Uint(U128) => "__rust_u128_addo",
                                        _ => unreachable!(),
                                    },
                                OverflowOp::Sub =>
                                    match new_kind {
                                        Int(I128) => "__rust_i128_subo",
                                        Uint(U128) => "__rust_u128_subo",
                                        _ => unreachable!(),
                                    },
                                OverflowOp::Mul =>
                                    match new_kind {
                                        Int(I128) => "__rust_i128_mulo", // TODO(antoyo): use __muloti4d instead?
                                        Uint(U128) => "__rust_u128_mulo",
                                        _ => unreachable!(),
                                    },
                            };
                        let a_type = lhs.get_type();
                        let b_type = rhs.get_type();
                        let param_a = self.context.new_parameter(None, a_type, "a");
                        let param_b = self.context.new_parameter(None, b_type, "b");
                        let result_field = self.context.new_field(None, a_type, "result");
                        let overflow_field = self.context.new_field(None, self.bool_type, "overflow");
                        let return_type = self.context.new_struct_type(None, "result_overflow", &[result_field, overflow_field]);
                        let func = self.context.new_function(None, FunctionType::Extern, return_type.as_type(), &[param_a, param_b], func_name, false);
                        let result = self.context.new_call(None, func, &[lhs, rhs]);
                        let overflow = result.access_field(None, overflow_field);
                        let int_result = result.access_field(None, result_field);
                        return (int_result, overflow);
                    },
                    _ => {
                        match oop {
                            OverflowOp::Mul =>
                                match new_kind {
                                    Int(I32) => "__mulosi4",
                                    Int(I64) => "__mulodi4",
                                    _ => unreachable!(),
                                },
                            _ => unimplemented!("overflow operation for {:?}", new_kind),
                        }
                    }
                }
            };

        let intrinsic = self.context.get_builtin_function(&name);
        let res = self.current_func()
            // TODO(antoyo): is it correct to use rhs type instead of the parameter typ?
            .new_local(None, rhs.get_type(), "binopResult")
            .get_address(None);
        let overflow = self.overflow_call(intrinsic, &[lhs, rhs, res], None);
        (res.dereference(None).to_rvalue(), overflow)
    }

    pub fn gcc_icmp(&self, op: IntPredicate, lhs: RValue<'gcc>, rhs: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = lhs.get_type();
        let b_type = rhs.get_type();
        if self.is_non_native_int_type(a_type) || self.is_non_native_int_type(b_type) {
            let a_int_type = self.get_int_type(a_type);
            let sign =
                if a_int_type.signed {
                    ""
                }
                else {
                    "u"
                };
            let size =
                match a_int_type.bits {
                    64 => 'd',
                    128 => 't',
                    size => unimplemented!("icmp not implemented for integers of size {}", size),
                };
            let func_name = format!("__{}cmp{}i2", sign, size);
            let param_a = self.context.new_parameter(None, a_type, "a");
            let param_b = self.context.new_parameter(None, b_type, "b");
            let func = self.context.new_function(None, FunctionType::Extern, self.int_type, &[param_a, param_b], func_name, false);
            let cmp = self.context.new_call(None, func, &[lhs, rhs]);
            let (op, limit) =
                match op {
                    IntPredicate::IntEQ => {
                        return self.context.new_comparison(None, ComparisonOp::Equals, cmp, self.context.new_rvalue_one(self.int_type));
                    },
                    IntPredicate::IntNE => {
                        return self.context.new_comparison(None, ComparisonOp::NotEquals, cmp, self.context.new_rvalue_one(self.int_type));
                    },
                    IntPredicate::IntUGT => (ComparisonOp::Equals, 2),
                    IntPredicate::IntUGE => (ComparisonOp::GreaterThanEquals, 1),
                    IntPredicate::IntULT => (ComparisonOp::Equals, 0),
                    IntPredicate::IntULE => (ComparisonOp::LessThanEquals, 1),
                    IntPredicate::IntSGT => (ComparisonOp::Equals, 2),
                    IntPredicate::IntSGE => (ComparisonOp::GreaterThanEquals, 1),
                    IntPredicate::IntSLT => (ComparisonOp::Equals, 0),
                    IntPredicate::IntSLE => (ComparisonOp::LessThanEquals, 1),
                };
            self.context.new_comparison(None, op, cmp, self.context.new_rvalue_from_int(self.int_type, limit))
        }
        else {
            self.context.new_comparison(None, op.to_gcc_comparison(), lhs, rhs)
        }
    }

    pub fn gcc_xor(&self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        if self.supports_native_int_type_or_bool(a_type) && self.supports_native_int_type_or_bool(b_type) {
            a ^ b
        }
        else {
            let int_type = self.get_int_type(a_type);
            let dest_size = int_type.bits as u32;
            let dest_element_size = int_type.element_size as u32;
            let factor = (dest_size / dest_element_size) as i32;
            let mut values = vec![];
            for i in 0..factor {
                let element_a = self.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.cx.int_type, i));
                let element_b = self.context.new_array_access(None, b, self.context.new_rvalue_from_int(self.cx.int_type, i));
                values.push(element_a.to_rvalue() ^ element_b.to_rvalue());
            }
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    pub fn gcc_shl(&mut self, a: RValue<'gcc>, b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        let a_native = self.supports_native_int_type(a_type);
        let b_native = self.supports_native_int_type(b_type);
        if a_native && b_native {
            // FIXME(antoyo): remove the casts when libgccjit can shift an unsigned number by an unsigned number.
            if a_type.is_unsigned(self) && b_type.is_signed(self) {
                let a = self.context.new_cast(None, a, b_type);
                let result = a << b;
                self.context.new_cast(None, result, a_type)
            }
            else if a_type.is_signed(self) && b_type.is_unsigned(self) {
                let b = self.context.new_cast(None, b, a_type);
                a << b
            }
            else {
                a << b
            }
        }
        else if a_native && !b_native {
            self.gcc_shl(a, self.gcc_int_cast(b, a_type))
        }
        else {
            // NOTE: we cannot use the ashl builtin because it's calling widen_hi() which uses ashl.
            let int_type = self.get_int_type(a_type);
            let size = int_type.bits;
            let element_size = int_type.element_size;
            let element_type = int_type.typ.dyncast_array().expect("element type");
            let element_size_value = self.context.new_rvalue_from_int(element_type, element_size as i32);

            let casted_b = self.gcc_int_cast(b, element_type);
            // NOTE: to support shift by more than the width of an element, we modulo the shift
            // value by the width and later, we move the elements to take this reduction of the
            // shift into account.
            let adjusted_shift = casted_b % element_size_value;
            let reverse_shift = element_size_value - adjusted_shift;

            // TODO: take endianness into account.
            let end = (size / element_size) as i32;
            let mut overflow = self.context.new_rvalue_zero(element_type);
            let mut values = vec![];
            for current_index in 0..end {
                let current_element = self.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.int_type, current_index)).to_rvalue();
                let shifted_value = current_element << adjusted_shift;
                let new_element = shifted_value | overflow;
                values.push(new_element);
                overflow = current_element >> reverse_shift;
            }

            let current_func = self.current_func.borrow().expect("current func");
            let current_block = self.current_block.borrow().expect("current block");
            let while_block = current_func.new_block("while");

            let result = current_func.new_local(None, int_type.typ, "shiftResult");
            let array_value = self.context.new_array_constructor(None, int_type.typ, &values);
            current_block.add_assignment(None, result, array_value);

            let casted_b_var = current_func.new_local(None, casted_b.get_type(), "current_shift_value");
            current_block.add_assignment(None, casted_b_var, casted_b);

            current_block.end_with_jump(None, while_block);

            // NOTE: if shifting by WIDTH or more, shift the elements in the array by one until the
            // values are at the right location.
            let cond = self.context.new_comparison(None, ComparisonOp::GreaterThanEquals, casted_b_var.to_rvalue(), element_size_value);

            let loop_block = current_func.new_block("loop");
            let after_block = current_func.new_block("after");

            while_block.end_with_conditional(None, cond, loop_block, after_block);

            for current_index in 0..end - 1 {
                let target = self.context.new_array_access(None, result, self.context.new_rvalue_from_int(self.int_type, current_index + 1));
                let source = self.context.new_array_access(None, result, self.context.new_rvalue_from_int(self.int_type, current_index));
                loop_block.add_assignment(None, target, source);
                loop_block.add_assignment_op(None, casted_b_var, gccjit::BinaryOp::Minus, element_size_value);
            }
            // TODO: handle endianness.
            let target = self.context.new_array_access(None, result, self.context.new_rvalue_from_int(self.int_type, 0));
            loop_block.add_assignment(None, target, self.context.new_rvalue_zero(element_type));

            loop_block.end_with_jump(None, while_block);

            // NOTE: since jumps were added in a place rustc does not expect, the current block in the
            // state need to be updated.
            self.block = Some(after_block);
            *self.cx.current_block.borrow_mut() = Some(after_block);

            result.to_rvalue()
        }
    }

    pub fn gcc_bswap(&mut self, mut arg: RValue<'gcc>, width: u64) -> RValue<'gcc> {
        let arg_type = arg.get_type();
        if !self.supports_native_int_type(arg_type) {
            // TODO
            return arg;
        }

        // TODO(antoyo): check if it's faster to use string literals and a
        // match instead of format!.
        let bswap = self.cx.context.get_builtin_function(&format!("__builtin_bswap{}", width));
        // FIXME(antoyo): this cast should not be necessary. Remove
        // when having proper sized integer types.
        let param_type = bswap.get_param(0).to_rvalue().get_type();
        if param_type != arg_type {
            arg = self.bitcast(arg, param_type);
        }
        self.cx.context.new_call(None, bswap, &[arg])
    }
}

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    pub fn gcc_int(&self, typ: Type<'gcc>, mut int: i64) -> RValue<'gcc> {
        if self.supports_native_int_type_or_bool(typ) {
            self.context.new_rvalue_from_long(typ, i64::try_from(int).expect("i64::try_from"))
        }
        else {
            // TODO: set the sign.
            let int_type = self.get_int_type(typ);
            let dest_size = int_type.bits as u32;
            let dest_element_size = int_type.element_size as u32;
            let mask = 2_i64.wrapping_pow(dest_element_size).wrapping_sub(1);
            let native_int_type = self.get_unsigned_int_type_by_size(dest_element_size as u8).typ;
            let mut bit_set = 0;
            let mut values = vec![];
            // FIXME: if dest_element_size < dest_size, this loop is infinite.
            while bit_set /*% dest_element_size*/ < dest_size {
                let value = int & mask;
                int = int.overflowing_shr(dest_size).0; // TODO: check if that overflows and if it does, check that we're done?
                //int >>= dest_size;
                values.push(self.context.new_rvalue_from_long(native_int_type, value as i64));
                bit_set += dest_element_size;
            }
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    pub fn gcc_uint(&self, typ: Type<'gcc>, mut int: u64) -> RValue<'gcc> {
        if self.supports_native_int_type_or_bool(typ) {
            self.context.new_rvalue_from_long(typ, u64::try_from(int).expect("u64::try_from") as i64)
        }
        else {
            let int_type = self.get_int_type(typ);
            let dest_size = int_type.bits as u32;
            let dest_element_size = int_type.element_size as u32;
            let mask = 2_u64.wrapping_pow(dest_element_size).wrapping_sub(1);
            let native_int_type = self.get_unsigned_int_type_by_size(dest_element_size as u8).typ;
            let mut bit_set = 0;
            let mut values = vec![];
            // FIXME: if dest_element_size < dest_size, this loop is infinite.
            while bit_set /*% dest_element_size*/ < dest_size {
                let value = int & mask;
                int = int.overflowing_shr(dest_size).0; // TODO: check if that overflows and if it does, check that we're done?
                //int >>= dest_size;
                values.push(self.context.new_rvalue_from_long(native_int_type, value as i64));
                bit_set += dest_element_size;
            }
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    pub fn gcc_uint_big(&self, typ: Type<'gcc>, mut num: u128) -> RValue<'gcc> {
        if num >> 64 != 0 {
            // FIXME(antoyo): use a new function new_rvalue_from_unsigned_long()?
            // FIXME: calling new_rvalue_from_long directly could not work if the type is
            // non-native.
            // TODO: make this code generic by using the parts of the non-native type if it is
            // non-native.
            if self.supports_native_int_type(typ) {
                let low = self.context.new_rvalue_from_long(self.u64_type, num as u64 as i64);
                let high = self.context.new_rvalue_from_long(typ, (num >> 64) as u64 as i64);

                let sixty_four = self.context.new_rvalue_from_long(typ, 64);
                let shift = high << sixty_four;
                shift | self.context.new_cast(None, low, typ)
            }
            else {
                let int_type = self.get_int_type(typ);
                let element_size = int_type.element_size as u32;
                let mask = (element_size - 1) as u128;
                let element_type = int_type.typ.dyncast_array().expect("get element type");
                let element_count = int_type.bits as u32 / element_size;
                let mut values = vec![];
                for _ in 0..element_count {
                    let value = num & mask;
                    num >>= element_size; // TODO: switch to overflowing_shr()?
                    values.push(self.context.new_rvalue_from_long(element_type, value as i64));
                }
                self.context.new_array_constructor(None, int_type.typ, &values)
            }
        }
        else if typ.is_i128(self) {
            let num = self.context.new_rvalue_from_long(self.u64_type, num as u64 as i64);
            // FIXME: that cast is probably going to fail for non-native types.
            self.gcc_int_cast(num, typ)
        }
        else {
            self.gcc_uint(typ, num as u64)
        }
    }

    pub fn gcc_zero(&self, typ: Type<'gcc>) -> RValue<'gcc> {
        if self.supports_native_int_type_or_bool(typ) {
            self.context.new_rvalue_zero(typ)
        }
        else {
            let int_type = self.get_int_type(typ);
            let size = int_type.bits;
            let factor = (size / int_type.element_size) as usize;
            let element_type = int_type.typ.dyncast_array().expect("get element type");
            let zero = self.context.new_rvalue_zero(element_type);
            let zeroes = vec![zero; factor];
            self.context.new_array_constructor(None, int_type.typ, &zeroes)
        }
    }

    pub fn gcc_int_width(&self, typ: Type<'gcc>) -> u64 {
        if self.supports_native_int_type_or_bool(typ) {
            typ.get_size() as u64 * 8
        }
        else {
            let int_type = self.get_int_type(typ);
            int_type.bits as u64
        }
    }

    pub fn gcc_or(&self, a: RValue<'gcc>, mut b: RValue<'gcc>) -> RValue<'gcc> {
        let a_type = a.get_type();
        let b_type = b.get_type();
        let a_native = self.supports_native_int_type_or_bool(a_type);
        let b_native = self.supports_native_int_type_or_bool(b_type);
        if a_native && b_native {
            if a.get_type() != b.get_type() {
                b = self.context.new_cast(None, b, a.get_type());
            }
            a | b
        }
        else {
            assert!(!a_native && !b_native, "both types should either be native or non-native for or operation");
            let int_type = self.get_int_type(a_type);
            let dest_size = int_type.bits as u32;
            let dest_element_size = int_type.element_size as u32;
            let factor = (dest_size / dest_element_size) as i32;
            let mut values = vec![];
            for i in 0..factor {
                let element_a = self.context.new_array_access(None, a, self.context.new_rvalue_from_int(self.int_type, i));
                let element_b = self.context.new_array_access(None, b, self.context.new_rvalue_from_int(self.int_type, i));
                values.push(element_a.to_rvalue() | element_b.to_rvalue());
            }
            self.context.new_array_constructor(None, int_type.typ, &values)
        }
    }

    // TODO: can we use https://github.com/rust-lang/compiler-builtins/blob/master/src/int/mod.rs#L379 instead?
    pub fn gcc_int_cast(&self, value: RValue<'gcc>, dest_typ: Type<'gcc>) -> RValue<'gcc> {
        let value_type = value.get_type();
        if self.supports_native_int_type_or_bool(dest_typ) && self.supports_native_int_type_or_bool(value_type) {
            self.context.new_cast(None, value, dest_typ)
        }
        else if self.supports_native_int_type_or_bool(dest_typ) {
            // FIXME: this is assuming a cast to a smaller type.
            let dest_size = self.get_int_type(dest_typ).bits as u32;
            let int_type = self.get_int_type(value_type);
            let src_element_size = int_type.element_size as u32;
            let mut casted_value = self.context.new_rvalue_zero(dest_typ);
            let shift_value = self.context.new_rvalue_from_int(dest_typ, src_element_size as i32);
            let mut current_index = 0;

            let mut current_bit_count = 0;

            while current_bit_count < dest_size {
                let element = self.context.new_array_access(None, value, self.context.new_rvalue_from_int(self.int_type, current_index));
                casted_value = casted_value << shift_value;
                casted_value = casted_value + self.context.new_cast(None, element.to_rvalue(), dest_typ);
                current_bit_count += src_element_size;
                current_index += 1;
            }

            casted_value
        }
        else if self.supports_native_int_type_or_bool(value_type) {
            // FIXME: this is assuming the value fits in a single element of the destination type.
            let dest_int_type = self.get_int_type(dest_typ);
            let dest_element_type = dest_int_type.typ.dyncast_array().expect("get element type");
            let dest_size = dest_int_type.bits;
            let factor = (dest_size / dest_int_type.element_size) as usize;

            let mut values = vec![self.context.new_rvalue_zero(dest_element_type); factor];
            values[0] = self.context.new_cast(None, value, dest_element_type);
            self.context.new_array_constructor(None, dest_int_type.typ, &values)
        }
        else {
            let int_type = self.get_int_type(value_type);
            let src_size = int_type.bits;
            let src_element_size = int_type.element_size;
            let dest_int_type = self.get_int_type(dest_typ);
            let dest_size = dest_int_type.bits;
            // FIXME: the following is probably wrong. It should be dest_size /
            // dest_int_type.element_size.
            let factor = (dest_size / src_size) as usize;
            let array_type = dest_int_type.typ;

            if src_size < dest_size {
                // TODO: initialize to -1 if negative.
                let mut values = vec![self.context.new_rvalue_zero(value_type); factor];
                // TODO: take endianness into account.
                // FIXME: this is assuming that value is not an array and that it fits in one array
                // element.
                values[0] = value;
                let array_value = self.context.new_array_constructor(None, array_type, &values);
                self.context.new_bitcast(None, array_value, dest_typ)
            }
            else if src_size == dest_size {
                self.context.new_bitcast(None, value, dest_typ)
            }
            else {
                // TODO: also implement casting from a native integer type.
                let mut current_size = 0;
                // TODO: take endianness into account.
                let mut current_index = src_size / src_element_size - 1;
                let mut values = vec![];
                while current_size < dest_size {
                    values.push(self.context.new_array_access(None, value, self.context.new_rvalue_from_int(self.int_type, current_index as i32)).to_rvalue());
                    current_size += src_element_size;
                    current_index -= 1;
                }
                values.reverse(); // TODO: check that doing this is correct.
                let array_value = self.context.new_array_constructor(None, array_type, &values);
                // FIXME: that's not working since we can cast from u8 to struct u128.
                self.context.new_bitcast(None, array_value, dest_typ)
            }
        }
    }

    pub fn gcc_int_to_float_cast(&self, value: RValue<'gcc>, dest_typ: Type<'gcc>) -> RValue<'gcc> {
        let value_type = value.get_type();
        if self.supports_native_int_type_or_bool(value_type) {
            return self.context.new_cast(None, value, dest_typ);
        }

        let int_type = self.get_int_type(value_type);

        let func_name =
            match (int_type.bits, self.type_kind(dest_typ)) {
                (64, TypeKind::Float) => "__floatdisf",
                (64, TypeKind::Double) => "__floatdidf",
                (128, TypeKind::Float) => "__floattisf",
                (128, TypeKind::Double) => "__floattidf",
                (size, kind) => panic!("cannot cast a non-native signed integer of size {} to type {:?}", size, kind),
            };
        let param = self.context.new_parameter(None, value_type, "n");
        let func = self.context.new_function(None, FunctionType::Extern, dest_typ, &[param], func_name, false);
        self.context.new_call(None, func, &[value])
    }

    pub fn gcc_uint_to_float_cast(&self, value: RValue<'gcc>, dest_typ: Type<'gcc>) -> RValue<'gcc> {
        let value_type = value.get_type();
        if self.supports_native_int_type_or_bool(value_type) {
            return self.context.new_cast(None, value, dest_typ);
        }

        let int_type = self.get_int_type(value_type);

        let func_name =
            match (int_type.bits, self.type_kind(dest_typ)) {
                (64, TypeKind::Float) => "__floatundisf",
                (64, TypeKind::Double) => "__floatundidf",
                (128, TypeKind::Float) => "__floatuntisf",
                (128, TypeKind::Double) => "__floatuntidf",
                (size, kind) => panic!("cannot cast a non-native unsigned integer of size {} to type {:?}", size, kind),
            };
        let param = self.context.new_parameter(None, value_type, "n");
        let func = self.context.new_function(None, FunctionType::Extern, dest_typ, &[param], func_name, false);
        self.context.new_call(None, func, &[value])
    }

    pub fn gcc_float_to_int_cast(&self, value: RValue<'gcc>, dest_typ: Type<'gcc>) -> RValue<'gcc> {
        let value_type = value.get_type();
        if self.supports_native_int_type_or_bool(dest_typ) {
            return self.context.new_cast(None, value, dest_typ);
        }

        let int_type = self.get_int_type(dest_typ);

        let func_name =
            match (int_type.bits, self.type_kind(value_type)) {
                (64, TypeKind::Float) => "__fixsfdi",
                (64, TypeKind::Double) => "__fixdfdi",
                (128, TypeKind::Float) => "__fixsfti",
                (128, TypeKind::Double) => "__fixdfti",
                (size, kind) => panic!("cannot cast a {:?} to non-native integer of size {}", kind, size),
            };
        let param = self.context.new_parameter(None, value_type, "n");
        let func = self.context.new_function(None, FunctionType::Extern, dest_typ, &[param], func_name, false);
        self.context.new_call(None, func, &[value])
    }

    pub fn gcc_float_to_uint_cast(&self, value: RValue<'gcc>, dest_typ: Type<'gcc>) -> RValue<'gcc> {
        let value_type = value.get_type();
        if self.supports_native_int_type_or_bool(dest_typ) {
            return self.context.new_cast(None, value, dest_typ);
        }

        let int_type = self.get_int_type(dest_typ);

        let func_name =
            match (int_type.bits, self.type_kind(value_type)) {
                (64, TypeKind::Float) => "__fixunssfdi",
                (64, TypeKind::Double) => "__fixunsdfdi",
                (128, TypeKind::Float) => "__fixunssfti",
                (128, TypeKind::Double) => "__fixunsdfti",
                (size, kind) => panic!("cannot cast a {:?} to non-native unsigned integer of size {}", kind, size),
            };
        let param = self.context.new_parameter(None, value_type, "n");
        let func = self.context.new_function(None, FunctionType::Extern, dest_typ, &[param], func_name, false);
        self.context.new_call(None, func, &[value])
    }
}
