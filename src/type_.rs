use gccjit::{RValue, Struct, Type};
use rustc_codegen_ssa::traits::{BaseTypeMethods, DerivedTypeMethods};
use rustc_codegen_ssa::common::TypeKind;
use rustc_middle::bug;
use rustc_middle::ty::layout::TyAndLayout;
use rustc_target::abi::{Align, Integer, Size};

use crate::common::TypeReflection;
use crate::context::CodegenCx;
use crate::type_of::LayoutGccExt;

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    pub fn type_ix(&self, num_bits: u64) -> Type<'gcc> {
        // gcc only supports 1, 2, 4 or 8-byte integers.
        let bytes = (num_bits / 8).next_power_of_two() as i32;
        match bytes {
            1 => self.i8_type,
            2 => self.i16_type,
            4 => self.i32_type,
            8 => self.i64_type,
            16 => self.i128_type,
            _ => panic!("unexpected num_bits: {}", num_bits),
        }
        /*
        let bytes = (num_bits / 8).next_power_of_two() as i32;
        println!("num_bits: {}, bytes: {}", num_bits, bytes);
        self.context.new_int_type(bytes, true) // TODO: check if it is indeed a signed integer.
        */
    }

    pub fn type_bool(&self) -> Type<'gcc> {
        self.bool_type
    }

    pub fn type_void(&self) -> Type<'gcc> {
        self.context.new_type::<()>()
    }

    pub fn type_size_t(&self) -> Type<'gcc> {
        self.context.new_type::<usize>()
    }

    pub fn type_u8(&self) -> Type<'gcc> {
        self.u8_type
    }

    pub fn type_u16(&self) -> Type<'gcc> {
        self.u16_type
    }

    pub fn type_u32(&self) -> Type<'gcc> {
        self.u32_type
    }

    pub fn type_u64(&self) -> Type<'gcc> {
        self.u64_type
    }

    pub fn type_u128(&self) -> Type<'gcc> {
        self.u128_type
    }

    pub fn type_pointee_for_align(&self, align: Align) -> Type<'gcc> {
        // FIXME(eddyb) We could find a better approximation if ity.align < align.
        let ity = Integer::approximate_align(self, align);
        self.type_from_integer(ity)
    }
}

impl<'gcc, 'tcx> BaseTypeMethods<'tcx> for CodegenCx<'gcc, 'tcx> {
    fn type_i1(&self) -> Type<'gcc> {
        self.bool_type
    }

    fn type_i8(&self) -> Type<'gcc> {
        self.i8_type
    }

    fn type_i16(&self) -> Type<'gcc> {
        self.i16_type
    }

    fn type_i32(&self) -> Type<'gcc> {
        self.i32_type
    }

    fn type_i64(&self) -> Type<'gcc> {
        self.i64_type
    }

    fn type_i128(&self) -> Type<'gcc> {
        self.i128_type
    }

    fn type_isize(&self) -> Type<'gcc> {
        self.isize_type
    }

    fn type_f32(&self) -> Type<'gcc> {
        self.context.new_type::<f32>()
    }

    fn type_f64(&self) -> Type<'gcc> {
        self.context.new_type::<f64>()
    }

    fn type_func(&self, params: &[Type<'gcc>], return_type: Type<'gcc>) -> Type<'gcc> {
        let pointer_type = self.context.new_function_pointer_type(None, return_type, params, false);
        // TODO: check if necessary.
        /*self.function_type_param_return_value.borrow_mut().insert(pointer_type, crate::context::FuncSig {
            params: params.to_vec(),
            return_type,
        });*/
        pointer_type
    }

    fn type_struct(&self, fields: &[Type<'gcc>], packed: bool) -> Type<'gcc> {
        let types = fields.to_vec();
        if let Some(typ) = self.struct_types.borrow().get(fields) {
            return typ.clone();
        }
        let fields: Vec<_> = fields.iter().enumerate()
            .map(|(index, field)| self.context.new_field(None, *field, &format!("field{}_TODO", index)))
            .collect();
        // TODO: use packed.
        let name = types.iter().map(|typ| format!("{:?}", typ)).collect::<Vec<_>>().join("_");
        //let typ = self.context.new_struct_type(None, format!("struct{}", name), &fields).as_type();
        let typ = self.context.new_struct_type(None, "struct", &fields).as_type();
        self.fields.borrow_mut().insert(typ, fields);
        self.struct_types.borrow_mut().insert(types, typ);
        typ
    }

    fn type_kind(&self, typ: Type<'gcc>) -> TypeKind {
        // TODO: find a better way to compare types without taking alignment into account.
        if typ.is_i8(self) || typ.is_u8(self) ||
            typ.is_i16(self) || typ.is_u16(self) ||
            typ.is_i32(self) || typ.is_u32(self) ||
            typ.is_i64(self) || typ.is_u64(self) ||
            typ.is_i128(self) || typ.is_u128(self)
        {
            TypeKind::Integer
        }
        // TODO: find a better way to do that.
        else if format!("{:?}", typ).contains("__attribute__ ((vector_size") {
            TypeKind::Vector
        }
        else {
            if format!("{:?}", typ).contains("vector_size") {
                panic!("missed vector type");
            }
            // TODO
            TypeKind::Void
        }
    }

    fn type_ptr_to(&self, ty: Type<'gcc>) -> Type<'gcc> {
        // TODO
        /*assert_ne!(self.type_kind(ty), TypeKind::Function,
            "don't call ptr_to on function types, use ptr_to_gcc_type on FnAbi instead"
        );*/
        ty.make_pointer()
    }

    fn element_type(&self, ty: Type<'gcc>) -> Type<'gcc> {
        unimplemented!();
        //unsafe { llvm::LLVMGetElementType(ty) }
    }

    fn vector_length(&self, ty: Type<'gcc>) -> usize {
        unimplemented!();
        //unsafe { llvm::LLVMGetVectorSize(ty) as usize }
    }

    fn float_width(&self, typ: Type<'gcc>) -> usize {
        let f32 = self.context.new_type::<f32>();
        let f64 = self.context.new_type::<f64>();
        if typ == f32 {
            32
        }
        else if typ == f64 {
            64
        }
        else {
            panic!("Cannot get width of float type {:?}", typ);
        }
        // TODO: support other sizes.
        /*match self.type_kind(ty) {
            TypeKind::Float => 32,
            TypeKind::Double => 64,
            TypeKind::X86_FP80 => 80,
            TypeKind::FP128 | TypeKind::PPC_FP128 => 128,
            _ => bug!("llvm_float_width called on a non-float type"),
        }*/
    }

    fn int_width(&self, typ: Type<'gcc>) -> u64 {
        if typ.is_i8(self) || typ.is_u8(self) {
            8
        }
        else if typ.is_i16(self) || typ.is_u16(self) {
            16
        }
        else if typ.is_i32(self) || typ.is_u32(self) {
            32
        }
        else if typ.is_i64(self) || typ.is_u64(self) {
            64
        }
        else if typ.is_i128(self) || typ.is_u128(self) {
            128
        }
        else {
            panic!("Cannot get width of int type {:?}", typ);
        }
    }

    fn val_ty(&self, value: RValue<'gcc>) -> Type<'gcc> {
        value.get_type()
    }
}

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    pub fn type_padding_filler(&self, size: Size, align: Align) -> Type<'gcc> {
        let unit = Integer::approximate_align(self, align);
        let size = size.bytes();
        let unit_size = unit.size().bytes();
        assert_eq!(size % unit_size, 0);
        self.type_array(self.type_from_integer(unit), size / unit_size)
    }

    pub fn set_struct_body(&self, typ: Struct<'gcc>, fields: &[Type<'gcc>], packed: bool) {
        // TODO: use packed.
        let fields: Vec<_> = fields.iter()
            .map(|field| self.context.new_field(None, *field, "field"))
            .collect();
        typ.set_fields(None, &fields);
        self.fields.borrow_mut().insert(typ.as_type(), fields);
    }

    fn type_struct(&self, fields: &[Type<'gcc>], packed: bool) -> Type<'gcc> {
        // TODO: use packed.
        let fields: Vec<_> = fields.iter()
            .map(|field| self.context.new_field(None, *field, "field"))
            .collect();
        let typ = self.context.new_struct_type(None, "unnamedStruct", &fields).as_type();
        self.fields.borrow_mut().insert(typ, fields);
        typ
    }

    pub fn type_named_struct(&self, name: &str) -> Struct<'gcc> {
        self.context.new_opaque_struct_type(None, name)
    }

    pub fn type_array(&self, ty: Type<'gcc>, len: u64) -> Type<'gcc> {
        let array_type = self.context.new_array_type(None, ty, len as i32);
        self.array_types.borrow_mut().insert(array_type);
        array_type
    }
}

pub fn struct_fields<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, layout: TyAndLayout<'tcx>) -> (Vec<Type<'gcc>>, bool) {
    //debug!("struct_fields: {:#?}", layout);
    let field_count = layout.fields.count();

    let mut packed = false;
    let mut offset = Size::ZERO;
    let mut prev_effective_align = layout.align.abi;
    let mut result: Vec<_> = Vec::with_capacity(1 + field_count * 2);
    for i in layout.fields.index_by_increasing_offset() {
        let target_offset = layout.fields.offset(i as usize);
        let field = layout.field(cx, i);
        let effective_field_align =
            layout.align.abi.min(field.align.abi).restrict_for_offset(target_offset);
        packed |= effective_field_align < field.align.abi;

        /*debug!(
            "struct_fields: {}: {:?} offset: {:?} target_offset: {:?} \
                effective_field_align: {}",
            i,
            field,
            offset,
            target_offset,
            effective_field_align.bytes()
        );*/
        assert!(target_offset >= offset);
        let padding = target_offset - offset;
        let padding_align = prev_effective_align.min(effective_field_align);
        assert_eq!(offset.align_to(padding_align) + padding, target_offset);
        result.push(cx.type_padding_filler(padding, padding_align));
        //debug!("    padding before: {:?}", padding);

        result.push(field.gcc_type(cx, !field.ty.is_any_ptr())); // FIXME: might need to check if the type is inside another, like Box<Type>.
        offset = target_offset + field.size;
        prev_effective_align = effective_field_align;
    }
    if !layout.is_unsized() && field_count > 0 {
        if offset > layout.size {
            bug!("layout: {:#?} stride: {:?} offset: {:?}", layout, layout.size, offset);
        }
        let padding = layout.size - offset;
        let padding_align = prev_effective_align;
        assert_eq!(offset.align_to(padding_align) + padding, layout.size);
        /*debug!(
            "struct_fields: pad_bytes: {:?} offset: {:?} stride: {:?}",
            padding, offset, layout.size
        );*/
        result.push(cx.type_padding_filler(padding, padding_align));
        assert_eq!(result.len(), 1 + field_count * 2);
    } else {
        //debug!("struct_fields: offset: {:?} stride: {:?}", offset, layout.size);
    }

    (result, packed)
}
