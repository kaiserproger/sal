use std::fmt::Write;

use sal_syntax::{Diagnostic, Expr};

use super::{Function, Local, Ty};

impl Function<'_> {
    pub(super) fn builtin_result(name: &str) -> Option<Ty> {
        match name {
            "len" | "usize" | "address" | "load64" | "operation_address" | "concurrency_state" => {
                Some(Ty::Usize)
            }
            "bytes" | "slice" | "bytes_at" => Some(Ty::Bytes),
            "byte" | "u8" | "load8" => Some(Ty::U8),
            "i8" => Some(Ty::I8),
            "i16" => Some(Ty::I16),
            "i32" => Some(Ty::I32),
            "i64" | "syscall" | "thread_launch" => Some(Ty::I64),
            "isize" => Some(Ty::Isize),
            "u16" => Some(Ty::U16),
            "u32" | "atomic_load" | "atomic_cas" => Some(Ty::U32),
            "u64" => Some(Ty::U64),
            "size_of" | "align_of" | "offset_of" => Some(Ty::Usize),
            "store8" | "store64" | "atomic_store" => Some(Ty::Void),
            _ => None,
        }
    }

    // Evaluate and spill each operand before the next one. Nested SAL calls
    // may clobber every caller-saved register, including span lengths.
    pub(super) fn builtin_args(
        &mut self,
        name: &str,
        args: &[Expr],
        expected: &[Option<Ty>],
    ) -> Result<Vec<Local>, Diagnostic> {
        if args.len() != expected.len() {
            return Err(self.error(
                "B108",
                format!(
                    "native {name} requires exactly {} arguments",
                    expected.len()
                ),
            ));
        }
        let mut spills = Vec::with_capacity(args.len());
        for (arg, expected) in args.iter().zip(expected) {
            let ty = self.expression(arg, *expected)?;
            if let Some(expected) = expected {
                self.require(ty, *expected, "builtin argument")?;
            }
            if ty == Ty::Void {
                return Err(self.error("N100", "Void cannot be a builtin argument"));
            }
            let local = Local {
                ty,
                slot: self.allocate(ty),
                mutable: false,
            };
            self.store(local);
            spills.push(local);
        }
        Ok(spills)
    }

    // Dynamic range check for a value already loaded in RAX. Operands are
    // canonical sign/zero-extended words, so narrow checks compare the full
    // word; unsigned compares also reject negative signed inputs.
    fn conversion_check(&mut self, target: Ty, source: Ty) {
        if source.signed() == target.signed() && source.bits() <= target.bits() {
            return;
        }
        if !source.signed() && target.signed() && source.bits() < target.bits() {
            return;
        }
        if source.signed() && !target.signed() && source.bits() <= target.bits() {
            let _ = writeln!(
                self.code,
                "    testq %rax, %rax\n    js .Lsal_trap_{}",
                self.index
            );
            return;
        }
        match target {
            Ty::I8 => {
                if !source.signed() {
                    let _ = writeln!(
                        self.code,
                        "    cmpq $127, %rax\n    ja .Lsal_trap_{}",
                        self.index
                    );
                    return;
                }
                let _ = writeln!(
                    self.code,
                    "    cmpq $-128, %rax\n    jl .Lsal_trap_{}\n    cmpq $127, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::I16 => {
                if !source.signed() {
                    let _ = writeln!(
                        self.code,
                        "    cmpq $32767, %rax\n    ja .Lsal_trap_{}",
                        self.index
                    );
                    return;
                }
                let _ = writeln!(
                    self.code,
                    "    cmpq $-32768, %rax\n    jl .Lsal_trap_{}\n    cmpq $32767, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::I32 => {
                if !source.signed() {
                    let _ = writeln!(
                        self.code,
                        "    cmpq $2147483647, %rax\n    ja .Lsal_trap_{}",
                        self.index
                    );
                    return;
                }
                let _ = writeln!(
                    self.code,
                    "    cmpq $-2147483648, %rax\n    jl .Lsal_trap_{}\n    cmpq $2147483647, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::I64 | Ty::Isize => {
                if !matches!(source, Ty::U64 | Ty::Usize) {
                    return;
                }
                let _ = writeln!(
                    self.code,
                    "    testq %rax, %rax\n    js .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U8 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $255, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U16 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $65535, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U32 => {
                // 4294967295 does not fit a sign-extended imm32; compare
                // against a full 64-bit constant instead.
                let _ = writeln!(
                    self.code,
                    "    movabsq $4294967295, %rcx\n    cmpq %rcx, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U64 | Ty::Usize => {
                if !source.signed() {
                    return;
                }
                let _ = writeln!(
                    self.code,
                    "    testq %rax, %rax\n    js .Lsal_trap_{}",
                    self.index
                );
            }
            _ => {}
        }
    }

    pub(super) fn builtin(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if matches!(
            name,
            "atomic_load"
                | "atomic_store"
                | "atomic_cas"
                | "load64"
                | "store64"
                | "operation_address"
                | "thread_launch"
                | "concurrency_state"
        ) {
            return self.concurrency_builtin(name, args);
        }
        if name == "address" {
            if args.len() != 1 {
                return Err(self.error(
                    "B108",
                    "native address requires exactly 1 arguments".to_owned(),
                ));
            }
            // A single evaluation: records already leave a stable fixed-frame
            // pointer in RAX, spans leave (pointer, length). Either way RAX
            // is the address, so no spill or copy is needed or wanted.
            // `MutBytes` is allowed only at an explicit raw OS boundary;
            // `Buffer` addresses NEVER escape, even inside `unsafe`.
            let ty = self.expression(&args[0], None)?;
            if ty == Ty::Void {
                return Err(self.error("N100", "Void cannot be a builtin argument"));
            }
            if matches!(ty, Ty::Record(_) | Ty::Internal(_)) {
                return Ok(Ty::Usize);
            }
            if ty != Ty::MutBytes && ty != Ty::Text && ty != Ty::Bytes {
                return Err(self.error(
                    "N100",
                    "native address requires Text, Bytes, MutBytes, or a record",
                ));
            }
            if ty == Ty::Text || ty == Ty::Bytes {
                return Ok(Ty::Usize);
            }
            if !self.unsafe_context() {
                return Err(self.error(
                    "N100",
                    "native address of MutBytes requires an explicit unsafe raw OS boundary",
                ));
            }
            return Ok(Ty::Usize);
        }
        match name {
            "len" | "bytes" => {
                let values = self.builtin_args(name, args, &[None])?;
                let mut value = values[0];
                if name == "len" && value.ty == Ty::Borrow {
                    // Length of the original owner slot behind a Borrow.
                    self.load(value);
                    self.code
                        .push_str("    movq -8(%rax), %rdx\n    movq (%rax), %rax\n");
                    value = Local {
                        ty: Ty::Buffer,
                        slot: self.allocate(Ty::Buffer),
                        mutable: false,
                    };
                    self.store(value);
                }
                if name == "bytes" {
                    if value.ty != Ty::Text {
                        return Err(self.error("N100", "native bytes requires Text".to_owned()));
                    }
                } else if !matches!(value.ty, Ty::Text | Ty::Bytes | Ty::Buffer | Ty::MutBytes) {
                    return Err(self.error(
                        "N100",
                        "native len requires Text, Bytes, Buffer, or MutBytes".to_owned(),
                    ));
                }
                self.load(value);
                if name == "len" {
                    self.code.push_str("    movq %rdx, %rax\n");
                }
            }
            "byte" => {
                let values = self.builtin_args(name, args, &[None, Some(Ty::Usize)])?;
                let span = values[0];
                let index = values[1];
                if span.ty != Ty::Bytes && span.ty != Ty::MutBytes {
                    return Err(self.error("N100", "native byte requires Bytes or MutBytes"));
                }
                self.load(index);
                let _ = writeln!(self.code, "    cmpq -{}(%rbp), %rax\n    jae .Lsal_trap_{}\n    addq -{}(%rbp), %rax\n    jc .Lsal_trap_{}\n    movzbl (%rax), %eax", span.slot + 8, self.index, span.slot, self.index);
            }
            "slice" => {
                let values = self.builtin_args(
                    name,
                    args,
                    &[Some(Ty::Bytes), Some(Ty::Usize), Some(Ty::Usize)],
                )?;
                let span = values[0];
                let start = values[1];
                let count = values[2];
                // Subtract only after proving start <= length. Comparing count
                // to the remainder avoids start+count overflow altogether.
                let _ = writeln!(self.code, "    movq -{}(%rbp), %rcx\n    movq -{}(%rbp), %rax\n    cmpq %rax, %rcx\n    ja .Lsal_trap_{}\n    subq %rcx, %rax\n    movq -{}(%rbp), %rdx\n    cmpq %rax, %rdx\n    ja .Lsal_trap_{}\n    movq -{}(%rbp), %rax\n    addq %rcx, %rax\n    jc .Lsal_trap_{}", start.slot, span.slot + 8, self.index, count.slot, self.index, span.slot, self.index);
            }
            "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" => {
                let target = Self::builtin_result(name).expect("known conversion");
                if let [Expr::Int(value)] = args {
                    if target.fits_literal(*value) {
                        let _ = writeln!(self.code, "    movabsq ${value}, %rax");
                        return Ok(target);
                    }
                    let _ = writeln!(self.code, "    jmp .Lsal_trap_{}", self.index);
                    return Ok(target);
                }
                let [arg] = args else {
                    return Err(
                        self.error("B108", format!("native {name} requires exactly 1 argument"))
                    );
                };
                let source = self.expression(arg, None)?;
                if !source.integer() {
                    return Err(self.error("N100", "checked native conversions require an integer"));
                }
                self.conversion_check(target, source);
            }
            "syscall" => {
                let values = self.builtin_args(name, args, &[None; 7])?;
                if values.iter().any(|value| !value.ty.integer()) {
                    return Err(
                        self.error("N100", "syscall arguments must be machineword integers")
                    );
                }
                // Linux's fourth argument is r10 (not SysV rcx). Loading only
                // after all operands are spilled preserves seven operands even
                // across nested calls and syscall's rcx/r11 clobbers.
                for (value, register) in values
                    .iter()
                    .zip(["%rax", "%rdi", "%rsi", "%rdx", "%r10", "%r8", "%r9"])
                {
                    let _ = writeln!(self.code, "    movq -{}(%rbp), {register}", value.slot);
                }
                self.code.push_str("    syscall\n");
            }
            "bytes_at" => {
                let values = self.builtin_args(name, args, &[Some(Ty::Usize), Some(Ty::Usize)])?;
                let _ = writeln!(
                    self.code,
                    "    movq -{}(%rbp), %rax\n    movq -{}(%rbp), %rdx",
                    values[0].slot, values[1].slot
                );
            }
            "load8" => {
                let values = self.builtin_args(name, args, &[Some(Ty::Usize)])?;
                self.load(values[0]);
                self.code.push_str("    movzbl (%rax), %eax\n");
            }
            "store8" => {
                let values = self.builtin_args(name, args, &[Some(Ty::Usize), Some(Ty::U8)])?;
                let _ = writeln!(
                    self.code,
                    "    movq -{}(%rbp), %rcx\n    movq -{}(%rbp), %rax\n    movb %al, (%rcx)",
                    values[0].slot, values[1].slot
                );
            }
            _ => unreachable!("builtin dispatch uses builtin_result"),
        }
        Ok(Self::builtin_result(name).expect("known builtin"))
    }
}
