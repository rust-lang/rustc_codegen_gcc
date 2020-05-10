use std::convert::TryFrom;

use gccjit::{Block, RValue, Type, ToRValue};
use rustc_codegen_ssa::mir::place::PlaceRef;
use rustc_codegen_ssa::traits::{
    BaseTypeMethods,
    ConstMethods,
    DeclareMethods,
    DerivedTypeMethods,
    MiscMethods,
    StaticMethods,
};
use rustc_middle::bug;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::layout::TyAndLayout;
use rustc_mir::interpret::{Allocation, GlobalAlloc, Scalar};
use rustc_span::Symbol;
use rustc_target::abi::{self, HasDataLayout, LayoutOf, Pointer, Size};

use crate::consts::{self, const_alloc_to_gcc};
use crate::context::CodegenCx;
use crate::type_of::LayoutGccExt;

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    pub fn const_bytes(&self, bytes: &[u8]) -> RValue<'gcc> {
        bytes_in_context(self, bytes)
    }

    fn const_cstr(&self, symbol: Symbol, null_terminated: bool) -> RValue<'gcc> {
        if let Some(&value) = self.const_cstr_cache.borrow().get(&symbol) {
            return value.to_rvalue();
        }

        let global = self.global_string(&*symbol.as_str());

        self.const_cstr_cache.borrow_mut().insert(symbol, global.dereference(None));
        global
    }

    fn global_string(&self, string: &str) -> RValue<'gcc> {
        // TODO: handle non-null-terminated strings.
        let string = self.context.new_string_literal(&*string);
        let sym = self.generate_local_symbol_name("str");
        let global = self.define_global(&sym, self.val_ty(string))
            .unwrap_or_else(|| bug!("symbol `{}` is already defined", sym));
        self.global_init_block.add_assignment(None, global.dereference(None), string);
        global.to_rvalue()
        //llvm::LLVMRustSetLinkage(global, llvm::Linkage::InternalLinkage);
    }

    pub fn inttoptr(&self, block: Block<'gcc>, value: RValue<'gcc>, dest_ty: Type<'gcc>) -> RValue<'gcc> {
        let func = block.get_function();
        let local = func.new_local(None, value.get_type(), "intLocal");
        block.add_assignment(None, local, value);
        let value_address = local.get_address(None);

        let ptr = self.context.new_cast(None, value_address, dest_ty.make_pointer());
        ptr.dereference(None).to_rvalue()
    }

    pub fn ptrtoint(&self, block: Block<'gcc>, value: RValue<'gcc>, dest_ty: Type<'gcc>) -> RValue<'gcc> {
        // TODO: when libgccjit allow casting from pointer to int, remove this.
        let func = block.get_function();
        let local = func.new_local(None, value.get_type(), "ptrLocal");
        block.add_assignment(None, local, value);
        let ptr_address = local.get_address(None);

        let ptr = self.context.new_cast(None, ptr_address, dest_ty.make_pointer());
        ptr.dereference(None).to_rvalue()
    }

    pub fn const_isize(&self, i: i64) -> RValue<'gcc> {
        let bit_size = self.data_layout().pointer_size.bits();
        if bit_size < 64 {
            // make sure it doesn't overflow
            assert!(i < (1 << bit_size));
        }

        self.const_int(self.isize_type, i)
    }
}

pub fn bytes_in_context<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, bytes: &[u8]) -> RValue<'gcc> {
    // TODO: use gcc_jit_context_new_blob when it's merged?
    // https://gcc.gnu.org/pipermail/jit/2020q2/001214.html
    let context = &cx.context;
    let typ = context.new_array_type(None, context.new_type::<u8>(), bytes.len() as i32);
    let value = cx.global_init_func.new_local(None, typ, "bytesTODO");
    let block = cx.global_init_block;
    for (index, byte) in bytes.iter().enumerate() {
        let index = context.new_rvalue_from_long(cx.i32_type, index as i64);
        let byte = context.new_rvalue_from_long(context.new_type::<u8>(), *byte as i64);
        block.add_assignment(None, context.new_array_access(None, value, index), byte);
    }
    value.to_rvalue()
}

pub fn type_is_pointer<'gcc>(typ: Type<'gcc>) -> bool {
    // TODO: fix when having proper type reflection.
    // TODO: put all pointer types in a HashSet and check if it's there instead of relying on
    // string comparison.
    format!("{:?}", typ).ends_with('*')
}

impl<'gcc, 'tcx> ConstMethods<'tcx> for CodegenCx<'gcc, 'tcx> {
    fn const_null(&self, typ: Type<'gcc>) -> RValue<'gcc> {
        if type_is_pointer(typ) {
            self.context.new_null(typ)
        }
        else {
            self.const_int(typ, 0)
        }
    }

    fn const_undef(&self, typ: Type<'gcc>) -> RValue<'gcc> {
        self.current_func.borrow().expect("func")
            .new_local(None, typ, "undefined")
            .to_rvalue()
    }

    fn const_int(&self, typ: Type<'gcc>, int: i64) -> RValue<'gcc> {
        self.context.new_rvalue_from_long(typ, i64::try_from(int).expect("i64::try_from"))
    }

    fn const_uint(&self, typ: Type<'gcc>, int: u64) -> RValue<'gcc> {
        self.context.new_rvalue_from_long(typ, u64::try_from(int).expect("u64::try_from") as i64)
    }

    fn const_uint_big(&self, typ: Type<'gcc>, num: u128) -> RValue<'gcc> {
        // TODO: support u128.
        //self.context.new_rvalue_from_long(typ, i64::try_from(num).expect("i64::try_from"))
        // TODO: does that require a function new_rvalue_from_unsigned_long()?
        self.context.new_rvalue_from_long(typ, u64::try_from(num).unwrap_or_default() as i64)

        /*unsafe {
            let words = [u as u64, (u >> 64) as u64];
            llvm::LLVMConstIntOfArbitraryPrecision(t, 2, words.as_ptr())
        }*/
    }

    fn const_bool(&self, val: bool) -> RValue<'gcc> {
        self.const_uint(self.type_i1(), val as u64)
    }

    fn const_i32(&self, i: i32) -> RValue<'gcc> {
        self.const_int(self.type_i32(), i as i64)
    }

    fn const_u32(&self, i: u32) -> RValue<'gcc> {
        self.const_uint(self.type_u32(), i as u64)
    }

    fn const_u64(&self, i: u64) -> RValue<'gcc> {
        self.const_uint(self.type_u64(), i)
    }

    fn const_usize(&self, i: u64) -> RValue<'gcc> {
        let bit_size = self.data_layout().pointer_size.bits();
        if bit_size < 64 {
            // make sure it doesn't overflow
            assert!(i < (1 << bit_size));
        }

        self.const_uint(self.usize_type, i)
    }

    fn const_u8(&self, i: u8) -> RValue<'gcc> {
        unimplemented!();
        //self.const_uint(self.type_i8(), i as u64)
    }

    fn const_real(&self, t: Type<'gcc>, val: f64) -> RValue<'gcc> {
        unimplemented!();
        //unsafe { llvm::LLVMConstReal(t, val) }
    }

    fn const_str(&self, s: Symbol) -> (RValue<'gcc>, RValue<'gcc>) {
        let len = s.as_str().len();
        let cs = self.const_ptrcast(self.const_cstr(s, false),
            self.type_ptr_to(self.layout_of(self.tcx.mk_str()).gcc_type(self, true)),
        );
        (cs, self.const_usize(len as u64))
    }

    fn const_struct(&self, values: &[RValue<'gcc>], packed: bool) -> RValue<'gcc> {
        let fields: Vec<_> = values.iter()
            .map(|value| value.get_type())
            .collect();
        // TODO: cache the type? It's anonymous, so probably not.
        let name = fields.iter().map(|typ| format!("{:?}", typ)).collect::<Vec<_>>().join("_");
        let typ = self.type_struct(&fields, packed);
        let structure = self.global_init_func.new_local(None, typ, &name);
        let fields = &self.fields.borrow()[&typ];
        for (value, field) in values.iter().zip(fields.iter()) {
            let field_lvalue = structure.access_field(None, *field);
            self.global_init_block.add_assignment(None, field_lvalue, *value);
        }
        self.lvalue_to_rvalue(structure)
    }

    fn const_to_opt_uint(&self, v: RValue<'gcc>) -> Option<u64> {
        // TODO
        None
        //try_as_const_integral(v).map(|v| unsafe { llvm::LLVMConstIntGetZExtValue(v) })
    }

    fn const_to_opt_u128(&self, v: RValue<'gcc>, sign_ext: bool) -> Option<u128> {
        // TODO
        None
        /*try_as_const_integral(v).and_then(|v| unsafe {
            let (mut lo, mut hi) = (0u64, 0u64);
            let success = llvm::LLVMRustConstInt128Get(v, sign_ext, &mut hi, &mut lo);
            success.then_some(hi_lo_to_u128(lo, hi))
        })*/
    }

    fn scalar_to_backend(&self, cv: Scalar, layout: &abi::Scalar, ty: Type<'gcc>) -> RValue<'gcc> {
        let bitsize = if layout.is_bool() { 1 } else { layout.value.size(self).bits() };
        match cv {
            Scalar::Raw { size: 0, .. } => {
                unimplemented!();
                /*assert_eq!(0, layout.value.size(self).bytes());
                self.const_undef(self.type_ix(0))*/
            }
            Scalar::Raw { data, size } => {
                assert_eq!(size as u64, layout.value.size(self).bytes());
                if ty.is_f32(self) {
                    self.context.new_rvalue_from_double(ty, f32::from_bits(data as u32) as f64)
                }
                else if ty.is_f64(self) {
                    self.context.new_rvalue_from_double(ty, f64::from_bits(data as u64))
                }
                else {
                    let value = self.const_uint_big(self.type_ix(bitsize), data);
                    if layout.value == Pointer {
                        self.inttoptr(self.current_block.borrow().expect("block"), value, ty)
                    }
                    else {
                        self.const_bitcast(value, ty)
                    }
                }
            }
            Scalar::Ptr(ptr) => {
                let base_addr =
                    match self.tcx.global_alloc(ptr.alloc_id) {
                        GlobalAlloc::Memory(alloc) => {
                            let init = const_alloc_to_gcc(self, alloc);
                            let value =
                                match alloc.mutability {
                                    Mutability::Mut => self.static_addr_of_mut(init, alloc.align, None),
                                    _ => self.static_addr_of(init, alloc.align, None),
                                };
                            if !self.sess().fewer_names() {
                                // TODO
                                //llvm::set_value_name(value, format!("{:?}", ptr.alloc_id).as_bytes());
                            }
                            value
                        },
                        GlobalAlloc::Function(fn_instance) => {
                            self.get_fn_addr(fn_instance)
                        },
                        GlobalAlloc::Static(def_id) => {
                            assert!(self.tcx.is_static(def_id));
                            self.get_static(def_id)
                        },
                    };
                let value = self.context.new_array_access(None, base_addr, self.const_usize(ptr.offset.bytes()));
                if layout.value != Pointer {
                    //unsafe { llvm::LLVMConstPtrToInt(value, ty) }
                    self.const_bitcast(value.to_rvalue(), ty)
                }
                else {
                    self.const_bitcast(value.get_address(None), ty)
                }
            }
        }
    }

    fn from_const_alloc(&self, layout: TyAndLayout<'tcx>, alloc: &Allocation, offset: Size) -> PlaceRef<'tcx, RValue<'gcc>> {
        assert_eq!(alloc.align, layout.align.abi);
        let ty = self.type_ptr_to(layout.gcc_type(self, true));
        let value =
            if layout.size == Size::ZERO {
                let value = self.const_usize(alloc.align.bytes());
                self.context.new_cast(None, value, ty)
            }
            else {
                let init = const_alloc_to_gcc(self, alloc);
                let base_addr = self.static_addr_of(init, alloc.align, None);

                let array = self.const_bitcast(base_addr, self.type_i8p());
                let value = self.context.new_array_access(None, array, self.const_usize(offset.bytes())).get_address(None);
                self.const_bitcast(value, ty)
            };
        PlaceRef::new_sized(value, layout)
    }

    fn const_ptrcast(&self, val: RValue<'gcc>, ty: Type<'gcc>) -> RValue<'gcc> {
        self.context.new_cast(None, val, ty)
    }
}

pub trait SignType<'gcc, 'tcx> {
    fn is_signed(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_unsigned(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;

    fn to_unsigned(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc>;
}

impl<'gcc, 'tcx> SignType<'gcc, 'tcx> for Type<'gcc> {
    fn is_signed(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        self.is_i8(cx) || self.is_i16(cx) || self.is_i32(cx) || self.is_i64(cx) || self.is_i128(cx)
    }

    fn is_unsigned(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        self.is_u8(cx) || self.is_u16(cx) || self.is_u32(cx) || self.is_u64(cx) || self.is_u128(cx)
    }

    fn to_unsigned(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc> {
        if self.is_i8(cx) {
            cx.u8_type
        }
        else if self.is_i16(cx) {
            cx.u16_type
        }
        else if self.is_i32(cx) {
            cx.u32_type
        }
        else if self.is_i64(cx) {
            cx.u64_type
        }
        else if self.is_i128(cx) {
            cx.u128_type
        }
        else {
            *self
        }
    }
}

pub trait TypeReflection<'gcc, 'tcx>  {
    fn is_bool(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_uchar(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_ushort(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_uint(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_ulong(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_ulonglong(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;

    fn is_i8(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_u8(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_i16(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_u16(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_i32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_u32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_i64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_u64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_i128(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_u128(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;

    fn is_f32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
    fn is_f64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool;
}

// TODO: remove all this when libgccjit has a reflection API.
impl<'gcc, 'tcx> TypeReflection<'gcc, 'tcx> for Type<'gcc> {
    fn is_bool(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.bool_type))
    }

    fn is_uchar(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u8_type))
    }

    fn is_ushort(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u16_type))
    }

    fn is_uint(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.uint_type))
    }

    fn is_ulong(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        !self.is_ulonglong(cx) && format!("{:?}", self).starts_with(&format!("{:?}", cx.ulong_type))
    }

    fn is_ulonglong(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.ulonglong_type))
    }

    fn is_i8(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.i8_type))
    }

    fn is_u8(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u8_type))
    }

    fn is_i16(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.i16_type))
    }

    fn is_u16(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u16_type))
    }

    fn is_i32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.i32_type))
    }

    fn is_u32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u32_type))
    }

    fn is_i64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.i64_type))
    }

    fn is_u64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u64_type))
    }

    fn is_i128(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.i128_type))
    }

    fn is_u128(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.u128_type))
    }

    fn is_f32(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.context.new_type::<f32>()))
    }

    fn is_f64(&self, cx: &CodegenCx<'gcc, 'tcx>) -> bool {
        format!("{:?}", self).starts_with(&format!("{:?}", cx.context.new_type::<f64>()))
    }
}
