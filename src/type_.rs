#[cfg(feature = "master")]
use std::convert::TryInto;

#[cfg(feature = "master")]
use gccjit::{CType, TypeAttribute};
use gccjit::{RValue, Struct, Type};
use rustc_abi::{AddressSpace, Align, Integer, Size};
use rustc_codegen_ssa::common::TypeKind;
use rustc_codegen_ssa::traits::{
    BaseTypeCodegenMethods, DerivedTypeCodegenMethods, TypeMembershipCodegenMethods,
};
use rustc_middle::ty::layout::TyAndLayout;
use rustc_middle::{bug, ty};

use crate::common::TypeReflection;
use crate::context::{CodegenCx, new_array_type};
use crate::type_of::LayoutGccExt;

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    pub fn type_ix(&self, num_bits: u64) -> Type<'gcc> {
        // gcc only supports 1, 2, 4 or 8-byte integers.
        // FIXME(antoyo): this is misleading to use the next power of two as rustc_codegen_ssa
        // sometimes use 96-bit numbers and the following code will give an integer of a different
        // size.
        let bytes = (num_bits / 8).next_power_of_two() as i32;
        match bytes {
            1 => self.i8_type,
            2 => self.i16_type,
            4 => self.i32_type,
            8 => self.i64_type,
            16 => self.i128_type,
            _ => panic!("unexpected num_bits: {}", num_bits),
        }
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

    pub fn type_ptr_to(&self, ty: Type<'gcc>) -> Type<'gcc> {
        ty.make_pointer()
    }

    pub fn type_ptr_to_ext(&self, ty: Type<'gcc>, _address_space: AddressSpace) -> Type<'gcc> {
        // FIXME(antoyo): use address_space, perhaps with TYPE_ADDR_SPACE?
        ty.make_pointer()
    }

    pub fn type_i8p(&self) -> Type<'gcc> {
        self.type_ptr_to(self.type_i8())
    }

    pub fn type_i8p_ext(&self, address_space: AddressSpace) -> Type<'gcc> {
        self.type_ptr_to_ext(self.type_i8(), address_space)
    }

    pub fn type_pointee_for_align(&self, align: Align) -> Type<'gcc> {
        // FIXME(eddyb) We could find a better approximation if ity.align < align.
        let ity = Integer::approximate_align(self, align);
        self.type_from_integer(ity)
    }

    pub fn type_vector(&self, ty: Type<'gcc>, len: u64) -> Type<'gcc> {
        self.context.new_vector_type(ty, len)
    }

    pub fn type_float_from_ty(&self, t: ty::FloatTy) -> Type<'gcc> {
        match t {
            ty::FloatTy::F16 => self.type_f16(),
            ty::FloatTy::F32 => self.type_f32(),
            ty::FloatTy::F64 => self.type_f64(),
            ty::FloatTy::F128 => self.type_f128(),
        }
    }

    pub fn type_i1(&self) -> Type<'gcc> {
        self.bool_type
    }

    pub fn type_struct(
        &self,
        fields: &[Type<'gcc>],
        packed: bool,
        align: Option<Align>,
    ) -> Type<'gcc> {
        let align = normalize_struct_alignment(align);
        let key = StructTypeKey { fields: fields.to_vec(), packed, align };
        if let Some(typ) = self.struct_types.borrow().get(&key) {
            return *typ;
        }
        let fields: Vec<_> = fields
            .iter()
            .enumerate()
            .map(|(index, field)| {
                self.context.new_field(None, *field, format!("field{}_FIXME", index))
            })
            .collect();
        let typ = self.context.new_struct_type(None, "struct", &fields).as_type();
        if packed {
            #[cfg(feature = "master")]
            typ.add_attribute(TypeAttribute::Packed);
        }
        set_struct_alignment(typ, align);
        self.struct_types.borrow_mut().insert(key, typ);
        typ
    }
}

/// Identifies an anonymous struct type in `CodegenCx::struct_types`.
///
/// Everything that can make two of them distinct has to be part of it. In particular the
/// alignment: two Rust types can have the same field list and still differ in alignment (for
/// instance `struct { a: u64, b: u64 }` with and without `repr(align(16))`), and they must not
/// end up sharing a GCC type.
#[derive(Clone, Eq, Hash, PartialEq)]
pub struct StructTypeKey<'gcc> {
    pub fields: Vec<Type<'gcc>>,
    pub packed: bool,
    pub align: Option<Align>,
}

/// Discard an alignment that GCC would give the struct anyway.
///
/// One byte is the minimum alignment of a GCC struct, so requesting it explicitly changes
/// nothing; mapping it to `None` keeps types that do not care about their alignment sharing a
/// single entry in `CodegenCx::struct_types`.
fn normalize_struct_alignment(align: Option<Align>) -> Option<Align> {
    align.filter(|align| align.bytes() > 1)
}

/// Give a struct type the alignment that Rust computed for it.
///
/// GCC derives a struct's alignment from its field list, so a `repr(align(N))` that is larger
/// than what the fields require would otherwise be lost. That is not only a layout concern: the
/// ABI of a by-value ("byval") argument depends on it, since `ix86_function_arg_boundary` reads
/// `TYPE_ALIGN` to pick the argument's stack slot. An over-aligned aggregate whose GCC type has
/// lost its alignment is therefore passed at an offset a C caller does not agree on.
///
/// This has to be set on the struct type itself. `Type::get_aligned` is not enough: it builds a
/// type *variant*, and the argument-passing code looks at `TYPE_MAIN_VARIANT` first, which
/// discards it.
///
/// This never under-aligns a struct whose fields need more: GCC starts the record layout from
/// `TYPE_ALIGN` and the fields can only raise it.
#[cfg(feature = "master")]
fn set_struct_alignment(typ: Type<'_>, align: Option<Align>) {
    if let Some(align) = normalize_struct_alignment(align) {
        typ.add_attribute(TypeAttribute::Aligned(align.bytes() as u32));
    }
}

/// Without the `master` feature, libgccjit has no way to set a type's alignment.
#[cfg(not(feature = "master"))]
fn set_struct_alignment(_typ: Type<'_>, _align: Option<Align>) {}

impl<'gcc, 'tcx> BaseTypeCodegenMethods for CodegenCx<'gcc, 'tcx> {
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

    fn type_f16(&self) -> Type<'gcc> {
        #[cfg(feature = "master")]
        if self.supports_f16_type {
            return self.context.new_c_type(CType::Float16);
        }
        self.u16_type
    }

    fn type_f32(&self) -> Type<'gcc> {
        #[cfg(feature = "master")]
        if self.supports_f32_type {
            return self.context.new_c_type(CType::Float32);
        }
        self.float_type
    }

    fn type_f64(&self) -> Type<'gcc> {
        #[cfg(feature = "master")]
        if self.supports_f64_type {
            return self.context.new_c_type(CType::Float64);
        }
        self.double_type
    }

    fn type_f128(&self) -> Type<'gcc> {
        #[cfg(feature = "master")]
        if self.supports_f128_type {
            return self.context.new_c_type(CType::Float128);
        }
        bug!("unsupported float width 128")
    }

    fn type_func(&self, params: &[Type<'gcc>], return_type: Type<'gcc>) -> Type<'gcc> {
        self.context.new_function_pointer_type(None, return_type, params, false)
    }

    #[cfg(feature = "master")]
    fn type_kind(&self, typ: Type<'gcc>) -> TypeKind {
        if self.is_int_type_or_bool(typ) {
            TypeKind::Integer
        } else if typ.get_pointee().is_some() {
            TypeKind::Pointer
        } else if typ.is_vector() {
            TypeKind::Vector
        } else if typ.dyncast_array().is_some() {
            TypeKind::Array
        } else if typ.is_struct().is_some() {
            TypeKind::Struct
        } else if typ.dyncast_function_ptr_type().is_some() {
            TypeKind::Function
        } else if typ.is_compatible_with(self.float_type) {
            TypeKind::Float
        } else if typ.is_compatible_with(self.double_type) {
            TypeKind::Double
        } else if typ.is_floating_point() {
            match typ.get_size() {
                2 => TypeKind::Half,
                4 => TypeKind::Float,
                8 => TypeKind::Double,
                16 => TypeKind::FP128,
                size => unreachable!("Floating-point type of size {}", size),
            }
        } else if typ == self.type_void() {
            TypeKind::Void
        } else {
            // FIXME(antoyo): support other types.
            unimplemented!();
        }
    }

    #[cfg(not(feature = "master"))]
    fn type_kind(&self, typ: Type<'gcc>) -> TypeKind {
        if self.is_int_type_or_bool(typ) {
            TypeKind::Integer
        } else if typ.is_compatible_with(self.float_type) {
            TypeKind::Float
        } else if typ.is_compatible_with(self.double_type) {
            TypeKind::Double
        } else if typ.is_vector() {
            TypeKind::Vector
        } else if typ.get_pointee().is_some() {
            TypeKind::Pointer
        } else if typ.dyncast_array().is_some() {
            TypeKind::Array
        } else if typ.is_struct().is_some() {
            TypeKind::Struct
        } else if typ.dyncast_function_ptr_type().is_some() {
            TypeKind::Function
        } else if typ == self.type_void() {
            TypeKind::Void
        } else {
            // FIXME(antoyo): support other types.
            unimplemented!();
        }
    }

    fn type_ptr(&self) -> Type<'gcc> {
        self.type_ptr_to(self.type_void())
    }

    fn type_ptr_ext(&self, address_space: AddressSpace) -> Type<'gcc> {
        self.type_ptr_to_ext(self.type_void(), address_space)
    }

    fn element_type(&self, ty: Type<'gcc>) -> Type<'gcc> {
        if let Some(typ) = ty.dyncast_array() {
            typ
        } else if let Some(vector_type) = ty.dyncast_vector() {
            vector_type.get_element_type()
        } else if let Some(typ) = ty.get_pointee() {
            typ
        } else {
            unreachable!()
        }
    }

    fn vector_length(&self, _ty: Type<'gcc>) -> usize {
        unimplemented!();
    }

    #[cfg(feature = "master")]
    fn float_width(&self, typ: Type<'gcc>) -> usize {
        if typ.is_floating_point() {
            (typ.get_size() * u8::BITS).try_into().unwrap()
        } else {
            panic!("Cannot get width of float type {:?}", typ);
        }
    }

    #[cfg(not(feature = "master"))]
    fn float_width(&self, typ: Type<'gcc>) -> usize {
        let f32 = self.context.new_type::<f32>();
        let f64 = self.context.new_type::<f64>();
        if typ.is_compatible_with(f32) {
            32
        } else if typ.is_compatible_with(f64) {
            64
        } else {
            panic!("Cannot get width of float type {:?}", typ);
        }
        // FIXME(antoyo): support other sizes.
    }

    fn int_width(&self, typ: Type<'gcc>) -> u64 {
        self.gcc_int_width(typ)
    }

    fn val_ty(&self, value: RValue<'gcc>) -> Type<'gcc> {
        value.get_type()
    }

    #[cfg_attr(feature = "master", expect(unused_mut))]
    fn type_array(&self, ty: Type<'gcc>, mut len: u64) -> Type<'gcc> {
        #[cfg(not(feature = "master"))]
        if let Some(struct_type) = ty.is_struct()
            && struct_type.get_field_count() == 0
        {
            // NOTE: since gccjit only supports i32 for the array size and libcore's tests uses a
            // size of usize::MAX in test_binary_search, we workaround this by setting the size to
            // zero for ZSTs.
            len = 0;
        }

        new_array_type(self.context, None, ty, len)
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

    pub fn set_struct_body(
        &self,
        typ: Struct<'gcc>,
        fields: &[Type<'gcc>],
        packed: bool,
        align: Option<Align>,
    ) {
        let fields: Vec<_> = fields
            .iter()
            .enumerate()
            .map(|(index, field)| self.context.new_field(None, *field, format!("field_{}", index)))
            .collect();
        typ.set_fields(None, &fields);
        if packed {
            #[cfg(feature = "master")]
            typ.as_type().add_attribute(TypeAttribute::Packed);
        }
        set_struct_alignment(typ.as_type(), align);
    }

    pub fn type_named_struct(&self, name: &str) -> Struct<'gcc> {
        self.context.new_opaque_struct_type(None, name)
    }
}

pub fn struct_fields<'gcc, 'tcx>(
    cx: &CodegenCx<'gcc, 'tcx>,
    layout: TyAndLayout<'tcx>,
) -> (Vec<Type<'gcc>>, bool) {
    let field_count = layout.fields.count();

    let mut packed = false;
    let mut offset = Size::ZERO;
    let mut prev_effective_align = layout.align.abi;
    let mut result: Vec<_> = Vec::with_capacity(1 + field_count * 2);
    for i in layout.fields.index_by_increasing_offset() {
        let target_offset = layout.fields.offset(i);
        let field = layout.field(cx, i);
        let effective_field_align =
            layout.align.abi.min(field.align.abi).restrict_for_offset(target_offset);
        packed |= effective_field_align < field.align.abi;

        assert!(target_offset >= offset);
        let padding = target_offset - offset;
        let padding_align = prev_effective_align.min(effective_field_align);
        assert_eq!(offset.align_to(padding_align) + padding, target_offset);
        result.push(cx.type_padding_filler(padding, padding_align));

        result.push(field.gcc_type(cx));
        offset = target_offset + field.size;
        prev_effective_align = effective_field_align;
    }
    if layout.is_sized() && field_count > 0 {
        if offset > layout.size {
            bug!("layout: {:#?} stride: {:?} offset: {:?}", layout, layout.size, offset);
        }
        let padding = layout.size - offset;
        let padding_align = prev_effective_align;
        assert_eq!(offset.align_to(padding_align) + padding, layout.size);
        result.push(cx.type_padding_filler(padding, padding_align));
        assert_eq!(result.len(), 1 + field_count * 2);
    }

    (result, packed)
}

impl<'gcc, 'tcx> TypeMembershipCodegenMethods<'tcx> for CodegenCx<'gcc, 'tcx> {}
