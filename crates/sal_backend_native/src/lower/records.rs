use std::fmt::Write;

use sal_ir::{CRecordLayout, TypeRef};
use sal_syntax::{Diagnostic, Expr};

use super::{abi, Function, Local, Ty};

impl Function<'_> {
    pub(super) fn resolve(&self, ty: &TypeRef) -> Option<Ty> {
        Ty::resolve(ty, self.layouts, self.internal)
    }

    pub(super) fn record_layout(&self, ty: Ty) -> Option<&CRecordLayout> {
        abi::record(self.layouts, ty)
    }

    /// Ignore unspecified ABI upper bits; internal scalar values are canonical.
    pub(super) fn normalize(&mut self, ty: Ty) {
        let instruction = match ty {
            Ty::Bool => "    testb %al, %al\n    setne %al\n    movzbl %al, %eax\n",
            Ty::I8 => "    movsbq %al, %rax\n",
            Ty::I16 => "    movswq %ax, %rax\n",
            Ty::I32 => "    movslq %eax, %rax\n",
            Ty::U8 => "    movzbl %al, %eax\n",
            Ty::U16 => "    movzwl %ax, %eax\n",
            Ty::U32 => "    movl %eax, %eax\n",
            _ => "",
        };
        self.code.push_str(instruction);
    }

    /// RAX points to a record; destination is an address expression. Storage
    /// never aliases a different live value, so a forward copy is sufficient.
    pub(super) fn copy_record_to(&mut self, ty: Ty, destination: &str) {
        let size = self
            .record_layout(ty)
            .map(|layout| layout.size)
            .or_else(|| self.internal_layout(ty).map(|layout| layout.size))
            .expect("validated record");
        let _ = writeln!(self.code, "    movq %rax, %rsi\n    leaq {destination}, %rdi\n    movq ${size}, %rcx\n    rep movsb");
        // Never load unrelated frame bytes in the last INTEGER eightbyte.
        for offset in 0..(size.div_ceil(8) * 8 - size) {
            let _ = writeln!(self.code, "    movb $0, {offset}(%rdi)");
        }
        let _ = writeln!(self.code, "    leaq {destination}, %rax");
    }

    pub(super) fn construct(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        let layouts = self.layouts;
        let ty = Ty::Record(
            layouts
                .keys()
                .position(|record| record == name)
                .expect("known record"),
        );
        let layout = &layouts[name];
        if args.len() != layout.fields.len() {
            return Err(self.error(
                "B101",
                format!("record `{name}` constructor has wrong arity"),
            ));
        }
        let slot = self.allocate(ty);
        let size = abi::bytes(self.layouts, self.internal, ty);
        let _ = writeln!(self.code, "    leaq -{slot}(%rbp), %rdi\n    xorl %eax, %eax\n    movq ${size}, %rcx\n    rep stosb");
        for (field, arg) in layout.fields.iter().zip(args) {
            let expected = self.resolve(&field.ty).expect("validated field");
            let actual = self.expression(arg, Some(expected))?;
            self.require(actual, expected, "record field")?;
            let destination = format!("{}(%rbp)", -(slot as i64) + field.offset as i64);
            if matches!(expected, Ty::Record(_) | Ty::Internal(_)) {
                // A nested field has its actual size, not rounded slot size.
                // copy_record_to also clears its unused last slot bytes, which
                // could overlap the following field. Copy exactly here.
                let size = self
                    .record_layout(expected)
                    .map(|layout| layout.size)
                    .or_else(|| self.internal_layout(expected).map(|layout| layout.size))
                    .expect("validated record");
                let _ = writeln!(self.code, "    movq %rax, %rsi\n    leaq {destination}, %rdi\n    movq ${size}, %rcx\n    rep movsb");
            } else if expected.pair() {
                let _ = writeln!(
                    self.code,
                    "    movq %rax, {destination}\n    movq %rdx, {}(%rbp)",
                    -(slot as i64) + field.offset as i64 + 8
                );
            } else {
                let (instruction, register) = match expected.bits() {
                    8 => ("movb", "%al"),
                    16 => ("movw", "%ax"),
                    32 => ("movl", "%eax"),
                    _ => ("movq", "%rax"),
                };
                let _ = writeln!(self.code, "    {instruction} {register}, {destination}");
            }
        }
        let _ = writeln!(self.code, "    leaq -{slot}(%rbp), %rax");
        Ok(ty)
    }

    pub(super) fn field(&mut self, base: &Expr, name: &str) -> Result<Ty, Diagnostic> {
        let base_ty = self.expression(base, None)?;
        let found = abi::record(self.layouts, base_ty)
            .and_then(|layout| {
                layout
                    .fields
                    .iter()
                    .find(|field| field.name == name)
                    .map(|field| (field.offset, field.ty.clone()))
            })
            .or_else(|| {
                self.internal_layout(base_ty).and_then(|layout| {
                    layout
                        .fields
                        .iter()
                        .find(|field| field.name == *name)
                        .map(|field| (field.offset, field.ty.clone()))
                })
            })
            .ok_or_else(|| self.error("N100", format!("unknown record field `{name}`")))?;
        let (offset, field_ty) = found;
        let ty = self.resolve(&field_ty).expect("validated field");
        if matches!(ty, Ty::Record(_) | Ty::Internal(_)) {
            let _ = writeln!(self.code, "    addq ${offset}, %rax");
        } else if ty.pair() {
            // Pair widths are exact words: move, never narrow-extend, and
            // load the length before the pointer overwrites the base.
            let _ = writeln!(
                self.code,
                "    movq {}(%rax), %rdx\n    movq {offset}(%rax), %rax",
                offset + 8
            );
        } else {
            let instruction = match (ty.bits(), ty.signed()) {
                (8, true) => "movsbq",
                (8, false) => "movzbq",
                (16, true) => "movswq",
                (16, false) => "movzwq",
                (32, true) => "movslq",
                (32, false) => "movl",
                _ => "movq",
            };
            let register = if ty.bits() == 32 && !ty.signed() {
                "%eax"
            } else {
                "%rax"
            };
            let _ = writeln!(self.code, "    {instruction} {offset}(%rax), {register}");
            self.normalize(ty);
        }
        Ok(ty)
    }

    pub(super) fn reflection(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        let arity = if name == "offset_of" { 2 } else { 1 };
        if args.len() != arity {
            return Err(self.error("N100", format!("{name} has invalid operands")));
        }
        let Expr::Var(record) = &args[0] else {
            return Err(self.error("N100", "layout reflection requires a C record type"));
        };
        let layout = self
            .layouts
            .get(record)
            .ok_or_else(|| self.error("N100", "layout reflection requires a C record type"))?;
        let value = match name {
            "size_of" => layout.size,
            "align_of" => layout.align,
            "offset_of" => {
                let Expr::Lit(field) = &args[1] else {
                    return Err(self.error("N100", "offset_of requires a literal field name"));
                };
                layout
                    .fields
                    .iter()
                    .find(|candidate| candidate.name == *field)
                    .ok_or_else(|| self.error("N100", "offset_of names an unknown field"))?
                    .offset
            }
            _ => unreachable!("reflection dispatch"),
        };
        let _ = writeln!(self.code, "    movabsq ${value}, %rax");
        Ok(Ty::Usize)
    }

    pub(super) fn return_record(&mut self, ty: Ty) {
        let size = self
            .record_layout(ty)
            .map(|layout| layout.size)
            .or_else(|| self.internal_layout(ty).map(|layout| layout.size))
            .expect("record result");
        if let Some(slot) = self.hidden_result {
            let _ = writeln!(self.code, "    movq %rax, %rsi\n    movq -{slot}(%rbp), %rdi\n    movq ${size}, %rcx\n    rep movsb\n    movq -{slot}(%rbp), %rax");
        } else {
            self.code.push_str("    movq %rax, %r11\n");
            for (word, register) in ["%rax", "%rdx"].iter().enumerate().take(size.div_ceil(8)) {
                let offset = word * 8;
                let count = (size - offset).min(8);
                if count == 8 {
                    let _ = writeln!(self.code, "    movq {offset}(%r11), {register}");
                } else {
                    // A nested record may end at the final byte of its parent.
                    // Do not read a full eightbyte past the record's storage.
                    let _ = writeln!(self.code, "    xorq {register}, {register}");
                    for byte in 0..count {
                        let _ = writeln!(self.code, "    movzbl {}(%r11), %r10d", offset + byte);
                        if byte != 0 {
                            let _ = writeln!(self.code, "    shlq ${}, %r10", byte * 8);
                        }
                        let _ = writeln!(self.code, "    orq %r10, {register}");
                    }
                }
            }
        }
    }

    pub(super) fn copy_argument_to_stack(&mut self, local: Local, offset: usize) {
        if matches!(local.ty, Ty::Record(_) | Ty::Internal(_)) {
            self.load(local);
            self.copy_record_to(local.ty, &format!("{offset}(%rsp)"));
        } else {
            for word in 0..local.ty.slots() {
                let _ = writeln!(
                    self.code,
                    "    movq -{}(%rbp), %rax\n    movq %rax, {}(%rsp)",
                    local.slot + word * 8,
                    offset + word * 8
                );
            }
        }
    }
}
