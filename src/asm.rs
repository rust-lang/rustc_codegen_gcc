use gccjit::RValue;
use rustc_ast::ast::{InlineAsmOptions, InlineAsmTemplatePiece};
use rustc_codegen_ssa::mir::place::PlaceRef;
use rustc_codegen_ssa::traits::{AsmBuilderMethods, AsmMethods, InlineAsmOperandRef};
use rustc_hir::{GlobalAsm, LlvmInlineAsmInner};
use rustc_span::Span;

use crate::builder::Builder;
use crate::context::CodegenCx;

impl<'a, 'gcc, 'tcx> AsmBuilderMethods<'tcx> for Builder<'a, 'gcc, 'tcx> {
    fn codegen_llvm_inline_asm(&mut self, ia: &LlvmInlineAsmInner, outputs: Vec<PlaceRef<'tcx, RValue<'gcc>>>, mut inputs: Vec<RValue<'gcc>>, span: Span) -> bool {
        // TODO
        return true;

        /*let mut ext_constraints = vec![];
        let mut output_types = vec![];

        // Prepare the output operands
        let mut indirect_outputs = vec![];
        for (i, (out, &place)) in ia.outputs.iter().zip(&outputs).enumerate() {
            if out.is_rw {
                let operand = self.load_operand(place);
                if let OperandValue::Immediate(_) = operand.val {
                    inputs.push(operand.immediate());
                }
                ext_constraints.push(i.to_string());
            }
            if out.is_indirect {
                let operand = self.load_operand(place);
                if let OperandValue::Immediate(_) = operand.val {
                    indirect_outputs.push(operand.immediate());
                }
            } else {
                output_types.push(place.layout.gcc_type(self.cx()));
            }
        }
        if !indirect_outputs.is_empty() {
            indirect_outputs.extend_from_slice(&inputs);
            inputs = indirect_outputs;
        }

        let clobbers = ia.clobbers.iter().map(|s| format!("~{{{}}}", &s));

        // Default per-arch clobbers
        // Basically what clang does
        let arch_clobbers = match &self.sess().target.target.arch[..] {
            "x86" | "x86_64" => vec!["~{dirflag}", "~{fpsr}", "~{flags}"],
            "mips" | "mips64" => vec!["~{$1}"],
            _ => Vec::new(),
        };

        let all_constraints = ia
            .outputs
            .iter()
            .map(|out| out.constraint.to_string())
            .chain(ia.inputs.iter().map(|s| s.to_string()))
            .chain(ext_constraints)
            .chain(clobbers)
            .chain(arch_clobbers.iter().map(|s| (*s).to_string()))
            .collect::<Vec<String>>()
            .join(",");

        debug!("Asm Constraints: {}", &all_constraints);

        // Depending on how many outputs we have, the return type is different
        let num_outputs = output_types.len();
        let output_type = match num_outputs {
            0 => self.type_void(),
            1 => output_types[0],
            _ => self.type_struct(&output_types, false),
        };

        let asm = ia.asm.as_str();
        let r = inline_asm_call(
            self,
            &asm,
            &all_constraints,
            &inputs,
            output_type,
            ia.volatile,
            ia.alignstack,
            ia.dialect,
        );
        if r.is_none() {
            return false;
        }
        let r = r.unwrap();

        // Again, based on how many outputs we have
        let outputs = ia.outputs.iter().zip(&outputs).filter(|&(ref o, _)| !o.is_indirect);
        for (i, (_, &place)) in outputs.enumerate() {
            let v = if num_outputs == 1 { r } else { self.extract_value(r, i as u64) };
            OperandValue::Immediate(v).store(self, place);
        }

        // Store mark in a metadata node so we can map LLVM errors
        // back to source locations.  See #17552.
        unsafe {
            let key = "srcloc";
            let kind = llvm::LLVMGetMDKindIDInContext(
                self.llcx,
                key.as_ptr() as *const c_char,
                key.len() as c_uint,
            );

            let val: &'ll Value = self.const_i32(span.ctxt().outer_expn().as_u32() as i32);

            llvm::LLVMSetMetadata(r, kind, llvm::LLVMMDNodeInContext(self.llcx, &val, 1));
        }

        true*/
    }

    fn codegen_inline_asm(&mut self, template: &[InlineAsmTemplatePiece], operands: &[InlineAsmOperandRef<'tcx, Self>], options: InlineAsmOptions, span: Span) {
        unimplemented!();
        /*let asm_arch = self.tcx.sess.asm_arch.unwrap();

        // Collect the types of output operands
        let mut constraints = vec![];
        let mut output_types = vec![];
        let mut op_idx = FxHashMap::default();
        for (idx, op) in operands.iter().enumerate() {
            match *op {
                InlineAsmOperandRef::Out { reg, late, place } => {
                    let ty = if let Some(place) = place {
                        llvm_fixup_output_type(self.cx, reg.reg_class(), &place.layout)
                    } else {
                        // If the output is discarded, we don't really care what
                        // type is used. We're just using this to tell LLVM to
                        // reserve the register.
                        dummy_output_type(self.cx, reg.reg_class())
                    };
                    output_types.push(ty);
                    op_idx.insert(idx, constraints.len());
                    let prefix = if late { "=" } else { "=&" };
                    constraints.push(format!("{}{}", prefix, reg_to_llvm(reg)));
                }
                InlineAsmOperandRef::InOut { reg, late, in_value, out_place } => {
                    let ty = if let Some(ref out_place) = out_place {
                        llvm_fixup_output_type(self.cx, reg.reg_class(), &out_place.layout)
                    } else {
                        // LLVM required tied operands to have the same type,
                        // so we just use the type of the input.
                        llvm_fixup_output_type(self.cx, reg.reg_class(), &in_value.layout)
                    };
                    output_types.push(ty);
                    op_idx.insert(idx, constraints.len());
                    let prefix = if late { "=" } else { "=&" };
                    constraints.push(format!("{}{}", prefix, reg_to_llvm(reg)));
                }
                _ => {}
            }
        }

        // Collect input operands
        let mut inputs = vec![];
        for (idx, op) in operands.iter().enumerate() {
            match *op {
                InlineAsmOperandRef::In { reg, value } => {
                    let value =
                        llvm_fixup_input(self, value.immediate(), reg.reg_class(), &value.layout);
                    inputs.push(value);
                    op_idx.insert(idx, constraints.len());
                    constraints.push(reg_to_llvm(reg));
                }
                InlineAsmOperandRef::InOut { reg, late: _, in_value, out_place: _ } => {
                    let value = llvm_fixup_input(
                        self,
                        in_value.immediate(),
                        reg.reg_class(),
                        &in_value.layout,
                    );
                    inputs.push(value);
                    constraints.push(format!("{}", op_idx[&idx]));
                }
                InlineAsmOperandRef::SymFn { instance } => {
                    inputs.push(self.cx.get_fn(instance));
                    op_idx.insert(idx, constraints.len());
                    constraints.push("s".to_string());
                }
                InlineAsmOperandRef::SymStatic { def_id } => {
                    inputs.push(self.cx.get_static(def_id));
                    op_idx.insert(idx, constraints.len());
                    constraints.push("s".to_string());
                }
                _ => {}
            }
        }

        // Build the template string
        let mut template_str = String::new();
        for piece in template {
            match *piece {
                InlineAsmTemplatePiece::String(ref s) => {
                    if s.contains('$') {
                        for c in s.chars() {
                            if c == '$' {
                                template_str.push_str("$$");
                            } else {
                                template_str.push(c);
                            }
                        }
                    } else {
                        template_str.push_str(s)
                    }
                }
                InlineAsmTemplatePiece::Placeholder { operand_idx, modifier, span: _ } => {
                    match operands[operand_idx] {
                        InlineAsmOperandRef::In { reg, .. }
                        | InlineAsmOperandRef::Out { reg, .. }
                        | InlineAsmOperandRef::InOut { reg, .. } => {
                            let modifier = modifier_to_llvm(asm_arch, reg.reg_class(), modifier);
                            if let Some(modifier) = modifier {
                                template_str.push_str(&format!(
                                    "${{{}:{}}}",
                                    op_idx[&operand_idx], modifier
                                ));
                            } else {
                                template_str.push_str(&format!("${{{}}}", op_idx[&operand_idx]));
                            }
                        }
                        InlineAsmOperandRef::Const { ref string } => {
                            // Const operands get injected directly into the template
                            template_str.push_str(string);
                        }
                        InlineAsmOperandRef::SymFn { .. }
                        | InlineAsmOperandRef::SymStatic { .. } => {
                            // Only emit the raw symbol name
                            template_str.push_str(&format!("${{{}:c}}", op_idx[&operand_idx]));
                        }
                    }
                }
            }
        }

        if !options.contains(InlineAsmOptions::PRESERVES_FLAGS) {
            match asm_arch {
                InlineAsmArch::AArch64 | InlineAsmArch::Arm => {
                    constraints.push("~{cc}".to_string());
                }
                InlineAsmArch::X86 | InlineAsmArch::X86_64 => {
                    constraints.extend_from_slice(&[
                        "~{dirflag}".to_string(),
                        "~{fpsr}".to_string(),
                        "~{flags}".to_string(),
                    ]);
                }
                InlineAsmArch::RiscV32 | InlineAsmArch::RiscV64 => {}
            }
        }
        if !options.contains(InlineAsmOptions::NOMEM) {
            // This is actually ignored by LLVM, but it's probably best to keep
            // it just in case. LLVM instead uses the ReadOnly/ReadNone
            // attributes on the call instruction to optimize.
            constraints.push("~{memory}".to_string());
        }
        let volatile = !options.contains(InlineAsmOptions::PURE);
        let alignstack = !options.contains(InlineAsmOptions::NOSTACK);
        let output_type = match &output_types[..] {
            [] => self.type_void(),
            [ty] => ty,
            tys => self.type_struct(&tys, false),
        };
        let dialect = match asm_arch {
            InlineAsmArch::X86 | InlineAsmArch::X86_64
                if !options.contains(InlineAsmOptions::ATT_SYNTAX) =>
            {
                LlvmAsmDialect::Intel
            }
            _ => LlvmAsmDialect::Att,
        };
        let result = inline_asm_call(
            self,
            &template_str,
            &constraints.join(","),
            &inputs,
            output_type,
            volatile,
            alignstack,
            dialect,
            span,
        )
        .unwrap_or_else(|| span_bug!(span, "LLVM asm constraint validation failed"));

        if options.contains(InlineAsmOptions::PURE) {
            if options.contains(InlineAsmOptions::NOMEM) {
                llvm::Attribute::ReadNone.apply_callsite(llvm::AttributePlace::Function, result);
            } else if options.contains(InlineAsmOptions::READONLY) {
                llvm::Attribute::ReadOnly.apply_callsite(llvm::AttributePlace::Function, result);
            }
        } else {
            if options.contains(InlineAsmOptions::NOMEM) {
                llvm::Attribute::InaccessibleMemOnly
                    .apply_callsite(llvm::AttributePlace::Function, result);
            } else {
                // LLVM doesn't have an attribute to represent ReadOnly + SideEffect
            }
        }

        // Write results to outputs
        for (idx, op) in operands.iter().enumerate() {
            if let InlineAsmOperandRef::Out { reg, place: Some(place), .. }
            | InlineAsmOperandRef::InOut { reg, out_place: Some(place), .. } = *op
            {
                let value = if output_types.len() == 1 {
                    result
                } else {
                    self.extract_value(result, op_idx[&idx] as u64)
                };
                let value = llvm_fixup_output(self, value, reg.reg_class(), &place.layout);
                OperandValue::Immediate(value).store(self, place);
            }
        }*/
    }
}

impl<'gcc, 'tcx> AsmMethods for CodegenCx<'gcc, 'tcx> {
    fn codegen_global_asm(&self, ga: &GlobalAsm) {
        let asm = ga.asm.as_str();
        // TODO
        //unsafe {
            //llvm::LLVMRustAppendModuleInlineAsm(self.llmod, asm.as_ptr().cast(), asm.len());
        //}
    }
}
