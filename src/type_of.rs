use std::fmt::Write;

use gccjit::{Struct, Type};
use crate::rustc_codegen_ssa::traits::{BaseTypeMethods, DerivedTypeMethods, LayoutTypeMethods};
use rustc_middle::bug;
use rustc_middle::ty::{self, Ty, TypeFoldable};
use rustc_middle::ty::layout::{FnAbiOf, LayoutOf, TyAndLayout};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_target::abi::{self, Abi, F32, F64, FieldsShape, Int, Integer, Pointer, PointeeInfo, Size, TyAbiInterface, Variants};
use rustc_target::abi::call::{CastTarget, FnAbi, Reg};

use smallvec::{SmallVec, smallvec};

use crate::abi::{FnAbiGccExt, GccType};
use crate::context::{CodegenCx, TypeLowering};

impl<'gcc, 'tcx> CodegenCx<'gcc, 'tcx> {
    fn type_from_unsigned_integer(&self, i: Integer) -> Type<'gcc> {
        use Integer::*;
        match i {
            I8 => self.type_u8(),
            I16 => self.type_u16(),
            I32 => self.type_u32(),
            I64 => self.type_u64(),
            I128 => self.type_u128(),
        }
    }

    pub fn type_int_from_ty(&self, t: ty::IntTy) -> Type<'gcc> {
        match t {
            ty::IntTy::Isize => self.type_isize(),
            ty::IntTy::I8 => self.type_i8(),
            ty::IntTy::I16 => self.type_i16(),
            ty::IntTy::I32 => self.type_i32(),
            ty::IntTy::I64 => self.type_i64(),
            ty::IntTy::I128 => self.type_i128(),
        }
    }

    pub fn type_uint_from_ty(&self, t: ty::UintTy) -> Type<'gcc> {
        match t {
            ty::UintTy::Usize => self.type_isize(),
            ty::UintTy::U8 => self.type_i8(),
            ty::UintTy::U16 => self.type_i16(),
            ty::UintTy::U32 => self.type_i32(),
            ty::UintTy::U64 => self.type_i64(),
            ty::UintTy::U128 => self.type_i128(),
        }
    }
}

pub fn uncached_gcc_type<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, layout: TyAndLayout<'tcx>, defer: &mut Option<(Struct<'gcc>, TyAndLayout<'tcx>)>, field_remapping: &mut Option<SmallVec<[u32; 4]>>) -> Type<'gcc> {
    match layout.abi {
        Abi::Scalar(_) => bug!("handled elsewhere"),
        Abi::Vector { ref element, count } => {
            let element = layout.scalar_gcc_type_at(cx, element, Size::ZERO);
            return cx.context.new_vector_type(element, count);
        },
        Abi::ScalarPair(..) => {
            return cx.type_struct(
                &[
                    layout.scalar_pair_element_gcc_type(cx, 0, false),
                    layout.scalar_pair_element_gcc_type(cx, 1, false),
                ],
                false,
            );
        }
        Abi::Uninhabited | Abi::Aggregate { .. } => {}
    }

    let name = match layout.ty.kind() {
        // FIXME(eddyb) producing readable type names for trait objects can result
        // in problematically distinct types due to HRTB and subtyping (see #47638).
        // ty::Dynamic(..) |
        ty::Adt(..) | ty::Closure(..) | ty::Foreign(..) | ty::Generator(..) | ty::Str
            if !cx.sess().fewer_names() =>
        {
            let mut name = with_no_trimmed_paths!(layout.ty.to_string());
            if let (&ty::Adt(def, _), &Variants::Single { index }) =
                (layout.ty.kind(), &layout.variants)
            {
                if def.is_enum() && !def.variants().is_empty() {
                    write!(&mut name, "::{}", def.variant(index).name).unwrap();
                }
            }
            if let (&ty::Generator(_, _, _), &Variants::Single { index }) =
                (layout.ty.kind(), &layout.variants)
            {
                write!(&mut name, "::{}", ty::GeneratorSubsts::variant_name(index)).unwrap();
            }
            Some(name)
        }
        ty::Adt(..) => {
            // If `Some` is returned then a named struct is created in LLVM. Name collisions are
            // avoided by LLVM (with increasing suffixes). If rustc doesn't generate names then that
            // can improve perf.
            // FIXME(antoyo): I don't think that's true for libgccjit.
            Some(String::new())
        }
        _ => None,
    };

    match layout.fields {
        FieldsShape::Primitive | FieldsShape::Union(_) => {
            let fill = cx.type_padding_filler(layout.size, layout.align.abi);
            let packed = false;
            match name {
                None => cx.type_struct(&[fill], packed),
                Some(ref name) => {
                    let gcc_type = cx.type_named_struct(name);
                    cx.set_struct_body(gcc_type, &[fill], packed);
                    gcc_type.as_type()
                },
            }
        }
        FieldsShape::Array { count, .. } => cx.type_array(layout.field(cx, 0).gcc_type(cx), count),
        FieldsShape::Arbitrary { .. } =>
            match name {
                None => {
                    let (gcc_fields, packed, new_field_remapping) = struct_fields(cx, layout);
                    *field_remapping = new_field_remapping;
                    cx.type_struct(&gcc_fields, packed)
                },
                Some(ref name) => {
                    let gcc_type = cx.type_named_struct(name);
                    *defer = Some((gcc_type, layout));
                    gcc_type.as_type()
                },
            },
    }
}

fn struct_fields<'gcc, 'tcx>(cx: &CodegenCx<'gcc, 'tcx>, layout: TyAndLayout<'tcx>) -> (Vec<Type<'gcc>>, bool, Option<SmallVec<[u32; 4]>>) {
    let field_count = layout.fields.count();

    let mut packed = false;
    let mut offset = Size::ZERO;
    let mut prev_effective_align = layout.align.abi;
    let mut result: Vec<_> = Vec::with_capacity(1 + field_count * 2);
    let mut field_remapping = smallvec![0; field_count];
    for i in layout.fields.index_by_increasing_offset() {
        let target_offset = layout.fields.offset(i as usize);
        let field = layout.field(cx, i);
        let effective_field_align =
            layout.align.abi.min(field.align.abi).restrict_for_offset(target_offset);
        packed |= effective_field_align < field.align.abi;

        assert!(target_offset >= offset);
        let padding = target_offset - offset;
        if padding != Size::ZERO {
            let padding_align = prev_effective_align.min(effective_field_align);
            assert_eq!(offset.align_to(padding_align) + padding, target_offset);
            result.push(cx.type_padding_filler(padding, padding_align));
        }
        field_remapping[i] = result.len() as u32;
        result.push(field.gcc_type(cx));
        offset = target_offset + field.size;
        prev_effective_align = effective_field_align;
    }
    let padding_used = result.len() > field_count;
    if !layout.is_unsized() && field_count > 0 {
        if offset > layout.size {
            bug!("layout: {:#?} stride: {:?} offset: {:?}", layout, layout.size, offset);
        }
        let padding = layout.size - offset;
        if padding != Size::ZERO {
            let padding_align = prev_effective_align;
            assert_eq!(offset.align_to(padding_align) + padding, layout.size);
            result.push(cx.type_padding_filler(padding, padding_align));
        }
    }
    let field_remapping = if padding_used { Some(field_remapping) } else { None };
    (result, packed, field_remapping)
}

pub trait LayoutGccExt<'tcx> {
    fn is_gcc_immediate(&self) -> bool;
    fn is_gcc_scalar_pair(&self) -> bool;
    fn gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc>;
    fn immediate_gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc>;
    fn scalar_gcc_type_at<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, scalar: &abi::Scalar, offset: Size) -> Type<'gcc>;
    fn scalar_pair_element_gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, index: usize, immediate: bool) -> Type<'gcc>;
    fn gcc_field_index<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, index: usize) -> u64;
    fn pointee_info_at<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, offset: Size) -> Option<PointeeInfo>;
}

impl<'tcx> LayoutGccExt<'tcx> for TyAndLayout<'tcx> {
    fn is_gcc_immediate(&self) -> bool {
        match self.abi {
            Abi::Scalar(_) | Abi::Vector { .. } => true,
            Abi::ScalarPair(..) => false,
            Abi::Uninhabited | Abi::Aggregate { .. } => self.is_zst(),
        }
    }

    fn is_gcc_scalar_pair(&self) -> bool {
        match self.abi {
            Abi::ScalarPair(..) => true,
            Abi::Uninhabited | Abi::Scalar(_) | Abi::Vector { .. } | Abi::Aggregate { .. } => false,
        }
    }

    /// Gets the GCC type corresponding to a Rust type, i.e., `rustc_middle::ty::Ty`.
    /// The pointee type of the pointer in `PlaceRef` is always this type.
    /// For sized types, it is also the right LLVM type for an `alloca`
    /// containing a value of that type, and most immediates (except `bool`).
    /// Unsized types, however, are represented by a "minimal unit", e.g.
    /// `[T]` becomes `T`, while `str` and `Trait` turn into `i8` - this
    /// is useful for indexing slices, as `&[T]`'s data pointer is `T*`.
    /// If the type is an unsized struct, the regular layout is generated,
    /// with the inner-most trailing unsized field using the "minimal unit"
    /// of that field's type - this is useful for taking the address of
    /// that field and ensuring the struct has the right alignment.
    fn gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc> {
        if let Abi::Scalar(ref scalar) = self.abi {
            // Use a different cache for scalars because pointers to DSTs
            // can be either fat or thin (data pointers of fat pointers).
            if let Some(&ty) = cx.scalar_types.borrow().get(&self.ty) {
                return ty;
            }
            let ty =
                match *self.ty.kind() {
                    ty::Ref(_, ty, _) | ty::RawPtr(ty::TypeAndMut { ty, .. }) => {
                        cx.type_ptr_to(cx.layout_of(ty).gcc_type(cx))
                    }
                    ty::Adt(def, _) if def.is_box() => {
                        cx.type_ptr_to(cx.layout_of(self.ty.boxed_ty()).gcc_type(cx))
                    }
                    ty::FnPtr(sig) => cx.fn_ptr_backend_type(&cx.fn_abi_of_fn_ptr(sig, ty::List::empty())),
                    _ => self.scalar_gcc_type_at(cx, scalar, Size::ZERO),
                };
            cx.scalar_types.borrow_mut().insert(self.ty, ty);
            return ty;
        }

        // Check the cache.
        let variant_index =
            match self.variants {
                Variants::Single { index } => Some(index),
                _ => None,
            };
        if let Some(gcc_type) = cx.type_lowering.borrow().get(&(self.ty, variant_index)) {
            return gcc_type.gcc_type;
        }

        assert!(!self.ty.has_escaping_bound_vars(), "{:?} has escaping bound vars", self.ty);

        // Make sure lifetimes are erased, to avoid generating distinct GCC
        // types for Rust types that only differ in the choice of lifetimes.
        let normal_ty = cx.tcx.erase_regions(self.ty);

        let mut defer = None;
        let mut field_remapping = None;
        let ty =
            if self.ty != normal_ty {
                let mut layout = cx.layout_of(normal_ty);
                if let Some(v) = variant_index {
                    layout = layout.for_variant(cx, v);
                }
                layout.gcc_type(cx)
            }
            else {
                uncached_gcc_type(cx, *self, &mut defer, &mut field_remapping)
            };

        cx.type_lowering
            .borrow_mut()
            .insert((self.ty, variant_index), TypeLowering { gcc_type: ty, field_remapping });

        if let Some((ty, layout)) = defer {
            let (fields, packed, new_field_remapping) = struct_fields(cx, layout);
            cx.set_struct_body(ty, &fields, packed);
            cx.type_lowering
                .borrow_mut()
                .get_mut(&(self.ty, variant_index))
                .unwrap()
                .field_remapping = new_field_remapping;
        }

        ty
    }

    fn immediate_gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>) -> Type<'gcc> {
        if let Abi::Scalar(ref scalar) = self.abi {
            if scalar.is_bool() {
                return cx.type_i1();
            }
        }
        self.gcc_type(cx)
    }

    fn scalar_gcc_type_at<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, scalar: &abi::Scalar, offset: Size) -> Type<'gcc> {
        match scalar.value {
            Int(i, true) => cx.type_from_integer(i),
            Int(i, false) => cx.type_from_unsigned_integer(i),
            F32 => cx.type_f32(),
            F64 => cx.type_f64(),
            Pointer => {
                // If we know the alignment, pick something better than i8.
                let pointee =
                    if let Some(pointee) = self.pointee_info_at(cx, offset) {
                        cx.type_pointee_for_align(pointee.align)
                    }
                    else {
                        cx.type_i8()
                    };
                cx.type_ptr_to(pointee)
            }
        }
    }

    fn scalar_pair_element_gcc_type<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, index: usize, immediate: bool) -> Type<'gcc> {
        // TODO(antoyo): remove llvm hack:
        // HACK(eddyb) special-case fat pointers until LLVM removes
        // pointee types, to avoid bitcasting every `OperandRef::deref`.
        match self.ty.kind() {
            ty::Ref(..) | ty::RawPtr(_) => {
                return self.field(cx, index).gcc_type(cx);
            }
            // only wide pointer boxes are handled as pointers
            // thin pointer boxes with scalar allocators are handled by the general logic below
            ty::Adt(def, substs) if def.is_box() && cx.layout_of(substs.type_at(1)).is_zst() => {
                let ptr_ty = cx.tcx.mk_mut_ptr(self.ty.boxed_ty());
                return cx.layout_of(ptr_ty).scalar_pair_element_gcc_type(cx, index, immediate);
            }
            _ => {}
        }

        let (a, b) = match self.abi {
            Abi::ScalarPair(ref a, ref b) => (a, b),
            _ => bug!("TyAndLayout::scalar_pair_element_llty({:?}): not applicable", self),
        };
        let scalar = [a, b][index];

        // Make sure to return the same type `immediate_gcc_type` would when
        // dealing with an immediate pair.  This means that `(bool, bool)` is
        // effectively represented as `{i8, i8}` in memory and two `i1`s as an
        // immediate, just like `bool` is typically `i8` in memory and only `i1`
        // when immediate.  We need to load/store `bool` as `i8` to avoid
        // crippling LLVM optimizations or triggering other LLVM bugs with `i1`.
        // TODO(antoyo): this bugs certainly don't happen in this case since the bool type is used instead of i1.
        if scalar.is_bool() {
            return cx.type_i1();
        }

        let offset =
            if index == 0 {
                Size::ZERO
            }
            else {
                a.value.size(cx).align_to(b.value.align(cx).abi)
            };
        self.scalar_gcc_type_at(cx, scalar, offset)
    }

    fn gcc_field_index<'gcc>(&self, cx: &CodegenCx<'gcc, 'tcx>, index: usize) -> u64 {
        match self.abi {
            Abi::Scalar(_) | Abi::ScalarPair(..) => {
                bug!("TyAndLayout::gcc_field_index({:?}): not applicable", self)
            }
            _ => {}
        }
        match self.fields {
            FieldsShape::Primitive | FieldsShape::Union(_) => {
                bug!("TyAndLayout::gcc_field_index({:?}): not applicable", self)
            }

            FieldsShape::Array { .. } => index as u64,

            FieldsShape::Arbitrary { .. } => {
                let variant_index = match self.variants {
                    Variants::Single { index } => Some(index),
                    _ => None,
                };

                // Look up gcc field if indexes do not match memory order due to padding. If
                // `field_remapping` is `None` no padding was used and the gcc field index
                // matches the memory index.
                match cx.type_lowering.borrow().get(&(self.ty, variant_index)) {
                    Some(TypeLowering { field_remapping: Some(ref remap), .. }) => {
                        remap[index] as u64
                    }
                    Some(_) => self.fields.memory_index(index) as u64,
                    None => {
                        bug!("TyAndLayout::gcc_field_index({:?}): type info not found", self)
                    }
                }
            }
        }
    }

    fn pointee_info_at<'a>(&self, cx: &CodegenCx<'a, 'tcx>, offset: Size) -> Option<PointeeInfo> {
        if let Some(&pointee) = cx.pointee_infos.borrow().get(&(self.ty, offset)) {
            return pointee;
        }

        let result = Ty::ty_and_layout_pointee_info_at(*self, cx, offset);

        cx.pointee_infos.borrow_mut().insert((self.ty, offset), result);
        result
    }
}

impl<'gcc, 'tcx> LayoutTypeMethods<'tcx> for CodegenCx<'gcc, 'tcx> {
    fn backend_type(&self, layout: TyAndLayout<'tcx>) -> Type<'gcc> {
        layout.gcc_type(self)
    }

    fn immediate_backend_type(&self, layout: TyAndLayout<'tcx>) -> Type<'gcc> {
        layout.immediate_gcc_type(self)
    }

    fn is_backend_immediate(&self, layout: TyAndLayout<'tcx>) -> bool {
        layout.is_gcc_immediate()
    }

    fn is_backend_scalar_pair(&self, layout: TyAndLayout<'tcx>) -> bool {
        layout.is_gcc_scalar_pair()
    }

    fn backend_field_index(&self, layout: TyAndLayout<'tcx>, index: usize) -> u64 {
        layout.gcc_field_index(self, index)
    }

    fn scalar_pair_element_backend_type(&self, layout: TyAndLayout<'tcx>, index: usize, immediate: bool) -> Type<'gcc> {
        layout.scalar_pair_element_gcc_type(self, index, immediate)
    }

    fn cast_backend_type(&self, ty: &CastTarget) -> Type<'gcc> {
        ty.gcc_type(self)
    }

    fn fn_ptr_backend_type(&self, fn_abi: &FnAbi<'tcx, Ty<'tcx>>) -> Type<'gcc> {
        fn_abi.ptr_to_gcc_type(self)
    }

    fn reg_backend_type(&self, _ty: &Reg) -> Type<'gcc> {
        unimplemented!();
    }

    fn fn_decl_backend_type(&self, _fn_abi: &FnAbi<'tcx, Ty<'tcx>>) -> Type<'gcc> {
        // FIXME(antoyo): return correct type.
        self.type_void()
    }
}
