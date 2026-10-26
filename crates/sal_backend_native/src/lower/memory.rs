//! Safe-memory pairs, borrows, contracts and internal records.
//!
//! `Buffer`/`MutBytes` lower as `(ptr, len)` pairs in `%rax`/`%rdx`, exactly
//! like spans at the machine level, but they are NEVER general spans: no
//! equality, no `bytes`/`slice` projection, no C ABI, and `address` is refused
//! for `Buffer` even inside `unsafe` (allowed for `MutBytes` only at an
//! explicit unsafe raw OS boundary). `Borrow<T>` lowers to the address of the
//! original owner slot (one word); every use aliases the original metadata,
//! so passing a `Borrow` forward preserves the alias and generated collection
//! wrappers observe the caller's slot through `load64`/`store64`.
//!
//! Internal non-`C` records lower with native layouts that recursively permit
//! integers, `bool`, spans, pairs, borrows and nested records. They are never
//! C-facing: no header, no import/export, no `address`/`bytes_at` escape.
//! Declared-`C` geometry stays strict via the shared layout map.
//!
//! Allocation and UTF-8 validation are SAL runtime policy, never Rust: this
//! file only marshals proof-valid metadata to `SalBufferAllocate`,
//! `SalBufferRelease` and `SalTextValidate`, failing closed when their
//! signatures are absent. Zero-length `0/0` is valid; OOM policy is SAL's
//! (nonzero exit), never a faked owner.
use std::collections::BTreeMap;
use std::fmt::Write;

use sal_ir::{CRecordLayout, TypeRef};
use sal_syntax::{Diagnostic, Expr};

use super::{Function, Local, Ty};

#[derive(Debug, Clone)]
pub(crate) struct InternalField {
    pub name: String,
    pub offset: usize,
    pub ty: TypeRef,
}

#[derive(Debug, Clone)]
pub(crate) struct InternalLayout {
    pub size: usize,
    pub align: usize,
    pub fields: Vec<InternalField>,
}

fn align_up(value: usize, align: usize) -> Option<usize> {
    value
        .checked_add(align - 1)
        .map(|value| value & !(align - 1))
}

fn primitive_size_align(name: &str) -> Option<(usize, usize)> {
    match name {
        "bool" | "u8" | "i8" => Some((1, 1)),
        "u16" | "i16" => Some((2, 2)),
        "u32" | "i32" => Some((4, 4)),
        "u64" | "i64" | "usize" | "isize" => Some((8, 8)),
        "Text" | "Bytes" | "Buffer" | "MutBytes" => Some((16, 8)),
        _ => None,
    }
}

fn field_size_align(
    ty: &TypeRef,
    layouts: &BTreeMap<String, CRecordLayout>,
    internal: &BTreeMap<String, InternalLayout>,
) -> Option<(usize, usize)> {
    match ty {
        TypeRef::Named(name) => {
            if let Some(pair) = primitive_size_align(name) {
                return Some(pair);
            }
            if let Some(layout) = layouts.get(name) {
                return Some((layout.size, layout.align));
            }
            if let Some(layout) = internal.get(name) {
                return Some((layout.size, layout.align));
            }
            None
        }
        TypeRef::Generic { name, args } => {
            if name == "Borrow" && args.len() == 1 {
                return Some((8, 8));
            }
            None
        }
    }
}

fn is_reserved_primitive(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "String"
            | "UUID"
            | "Character"
            | "Word"
            | "Text"
            | "Bytes"
            | "Buffer"
            | "MutBytes"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "f32"
            | "f64"
            | "usize"
            | "isize"
            | "Borrow"
            | "Vector"
            | "Map"
            | "ValueResult"
            | "Void"
    )
}

/// Best-effort native layouts for non-`C` entities. Cycles, empty records,
/// primitive collisions and unsupported fields stay unlaid out so their uses
/// fail closed in `Ty::resolve`; unused specification entities stay silent.
pub(crate) fn internal_layouts(
    ir: &sal_ir::Ir,
    layouts: &BTreeMap<String, CRecordLayout>,
) -> BTreeMap<String, InternalLayout> {
    let mut candidates: Vec<(&String, &sal_syntax::EntityDecl)> = ir
        .entities
        .iter()
        .filter(|(_, entity)| !entity.c_layout)
        .filter(|(name, _)| !is_reserved_primitive(name))
        .collect();
    candidates.sort_by(|a, b| a.0.cmp(b.0));
    let mut done: BTreeMap<String, InternalLayout> = BTreeMap::new();
    let mut progress = true;
    while progress {
        progress = false;
        for (name, entity) in &candidates {
            if done.contains_key(*name) {
                continue;
            }
            if entity.fields.is_empty() {
                continue;
            }
            let mut size = 0usize;
            let mut align = 1usize;
            let mut fields = Vec::with_capacity(entity.fields.len());
            let mut ok = true;
            for field in &entity.fields {
                let Some((field_size, field_align)) = field_size_align(&field.ty, layouts, &done)
                else {
                    ok = false;
                    break;
                };
                let Some(offset) = align_up(size, field_align) else {
                    ok = false;
                    break;
                };
                let Some(end) = offset.checked_add(field_size) else {
                    ok = false;
                    break;
                };
                size = end;
                align = align.max(field_align);
                fields.push(InternalField {
                    name: field.name.clone(),
                    offset,
                    ty: field.ty.clone(),
                });
            }
            if !ok {
                continue;
            }
            let Some(padded) = align_up(size, align) else {
                continue;
            };
            if padded == 0 || padded > i32::MAX as usize - 32 {
                continue;
            }
            done.insert(
                (*name).clone(),
                InternalLayout {
                    size: padded,
                    align,
                    fields,
                },
            );
            progress = true;
        }
    }
    done
}

/// True for the checked safe-memory surface plus the two pure contract
/// intrinsics. Vector/Map names are included only to fail closed with an
/// explicit collections message; erasure must run before native lowering.
pub(crate) fn memory_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "buffer"
            | "buffer_drop"
            | "borrow_mut"
            | "slice_mut"
            | "view"
            | "borrow"
            | "put"
            | "borrow_end"
            | "text"
            | "SalContractAssert"
            | "SalMemoryAssertDisjoint"
            | "vector"
            | "vector_drop"
            | "vector_len"
            | "vector_capacity"
            | "vector_reserve"
            | "vector_push"
            | "vector_get"
            | "vector_set"
            | "vector_pop"
            | "map"
            | "map_drop"
            | "map_len"
            | "map_capacity"
            | "map_reserve"
            | "map_insert"
            | "map_get"
            | "map_remove"
            | "map_contains"
    )
}

impl Function<'_> {
    pub(super) fn internal_layout(&self, ty: Ty) -> Option<&InternalLayout> {
        match ty {
            Ty::Internal(index) => self.internal.values().nth(index),
            _ => None,
        }
    }

    /// Result-type hint for a memory call. Void builtins need no hint;
    /// collections names hint nothing because they never reach lowering.
    pub(super) fn memory_hint(&self, name: &str, _args: &[Expr]) -> Option<Ty> {
        match name {
            "buffer" => Some(Ty::Buffer),
            "borrow_mut" | "slice_mut" => Some(Ty::MutBytes),
            "view" => Some(Ty::Bytes),
            "borrow" => Some(Ty::Borrow),
            "text" => Some(Ty::Text),
            _ => None,
        }
    }

    pub(super) fn memory_builtin(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        match name {
            "buffer" => self.memory_buffer(args),
            "buffer_drop" => self.memory_buffer_drop(args),
            "borrow_mut" | "slice_mut" => self.memory_borrow_mut(name, args),
            "view" => self.memory_view(args),
            "borrow" => self.memory_borrow(args),
            "put" => self.memory_put(args),
            "borrow_end" => self.memory_borrow_end(args),
            "text" => self.memory_text(args),
            "SalContractAssert" => self.memory_contract_assert(args),
            "SalMemoryAssertDisjoint" => self.memory_assert_disjoint(args),
            _ => Err(self.error(
                "N100",
                format!(
                    "native `{name}` requires collections lowering; Vector/Map must be erased before native"
                ),
            )),
        }
    }

    fn memory_buffer(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error("B108", "native buffer requires exactly 1 argument"));
        }
        let ty = self.expression(&args[0], Some(Ty::Usize))?;
        self.require(ty, Ty::Usize, "builtin argument")?;
        let signature = self.signatures.get("SalBufferAllocate").ok_or_else(|| {
            self.error(
                "N100",
                "native buffer requires the SAL runtime `SalBufferAllocate(usize)->SalBufferStorage`; missing runtime signature",
            )
        })?;
        if signature.params != [Ty::Usize] || signature.foreign.is_some() {
            return Err(self.error(
                "N100",
                "native buffer requires the SAL runtime `SalBufferAllocate(usize)->SalBufferStorage`; missing runtime signature",
            ));
        }
        let storage = self
            .record_layout(signature.result)
            .filter(|layout| layout.size == 16 && layout.fields.len() == 2);
        if storage.is_none() {
            return Err(self.error(
                "N100",
                "native buffer requires the SAL runtime `SalBufferAllocate(usize)->SalBufferStorage`; missing runtime signature",
            ));
        }
        let index = signature.index;
        // Length already canonical in RAX; the SAL allocator returns the
        // (address, length) pair in RAX/RDX, which is exactly a Buffer.
        self.code.push_str("    movq %rax, %rdi\n");
        let _ = writeln!(self.code, "    call .Lsal_fn_{index}");
        Ok(Ty::Buffer)
    }

    fn memory_buffer_drop(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error(
                "B108",
                "native buffer_drop requires exactly 1 argument",
            ));
        }
        let ty = self.expression(&args[0], Some(Ty::Buffer))?;
        self.require(ty, Ty::Buffer, "builtin argument")?;
        let local = Local {
            ty,
            slot: self.allocate(ty),
            mutable: false,
        };
        self.store(local);
        let signature = self.signatures.get("SalBufferRelease").ok_or_else(|| {
            self.error(
                "N100",
                "native buffer_drop requires the SAL runtime `SalBufferRelease(usize,usize)`; missing runtime signature",
            )
        })?;
        if signature.params != [Ty::Usize, Ty::Usize]
            || signature.result != Ty::Void
            || signature.foreign.is_some()
        {
            return Err(self.error(
                "N100",
                "native buffer_drop requires the SAL runtime `SalBufferRelease(usize,usize)`; missing runtime signature",
            ));
        }
        let index = signature.index;
        let _ = writeln!(
            self.code,
            "    movq -{}(%rbp), %rdi\n    movq -{}(%rbp), %rsi\n    call .Lsal_fn_{index}",
            local.slot,
            local.slot + 8
        );
        Ok(Ty::Void)
    }

    fn memory_borrow_mut(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 3 {
            return Err(self.error(
                "B108",
                format!("native {name} requires exactly 3 arguments"),
            ));
        }
        let base_expected = if name == "borrow_mut" {
            Ty::Buffer
        } else {
            Ty::MutBytes
        };
        let base_ty = if name == "borrow_mut" {
            self.owner_operand(&args[0], Some(base_expected))?
        } else {
            self.expression(&args[0], Some(base_expected))?
        };
        self.require(base_ty, base_expected, "builtin argument")?;
        let base = Local {
            ty: base_ty,
            slot: self.allocate(base_ty),
            mutable: false,
        };
        self.store(base);
        let start_ty = self.expression(&args[1], Some(Ty::Usize))?;
        self.require(start_ty, Ty::Usize, "builtin argument")?;
        let start = Local {
            ty: Ty::Usize,
            slot: self.allocate(Ty::Usize),
            mutable: false,
        };
        self.store(start);
        let count_ty = self.expression(&args[2], Some(Ty::Usize))?;
        self.require(count_ty, Ty::Usize, "builtin argument")?;
        let count = Local {
            ty: Ty::Usize,
            slot: self.allocate(Ty::Usize),
            mutable: false,
        };
        self.store(count);
        // Subtract only after proving start <= length. Comparing count to the
        // remainder avoids start+count overflow altogether. The derived pair
        // lands in %rax (pointer) / %rdx (count), exactly like `slice`.
        let _ = writeln!(self.code, "    movq -{}(%rbp), %rcx\n    movq -{}(%rbp), %rax\n    cmpq %rax, %rcx\n    ja .Lsal_trap_{}\n    subq %rcx, %rax\n    movq -{}(%rbp), %rdx\n    cmpq %rax, %rdx\n    ja .Lsal_trap_{}\n    movq -{}(%rbp), %rax\n    addq %rcx, %rax\n    jc .Lsal_trap_{}", start.slot, base.slot + 8, self.index, count.slot, self.index, base.slot, self.index);
        Ok(Ty::MutBytes)
    }

    /// Evaluates an owner operand of a non-consuming operation. A `Borrow`
    /// is the address of the original owner slot; dereference it to the
    /// owner's (address, length) pair so the operation addresses the original
    /// metadata. Consuming operations (`buffer_drop`) never use this and keep
    /// rejecting borrows.
    fn owner_operand(&mut self, arg: &Expr, hint: Option<Ty>) -> Result<Ty, Diagnostic> {
        let ty = self.expression(arg, hint)?;
        if ty != Ty::Borrow {
            return Ok(ty);
        }
        self.code
            .push_str("    movq -8(%rax), %rdx\n    movq (%rax), %rax\n");
        Ok(Ty::Buffer)
    }

    fn memory_view(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error("B108", "native view requires exactly 1 argument".to_owned()));
        }
        let ty = self.owner_operand(&args[0], None)?;
        // Buffer/MutBytes/Bytes/Text all carry (ptr, len) words; the readonly
        // projection of an already-readonly span is the identity. The memory
        // pass emits `view(existing)` disjointness guards over any live span
        // local of the same root, including Bytes/Text results.
        if !matches!(ty, Ty::Buffer | Ty::MutBytes | Ty::Bytes | Ty::Text) {
            return Err(self.error(
                "N100",
                format!("native view requires Buffer, MutBytes, Bytes or Text, found {ty:?}"),
            ));
        }
        // Same (ptr, len) words, readonly projection; no runtime work.
        Ok(Ty::Bytes)
    }

    fn memory_borrow(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error(
                "B108",
                "native borrow requires exactly 1 argument".to_owned(),
            ));
        }
        let Expr::Var(name) = &args[0] else {
            return Err(self.error(
                "N100",
                "native borrow requires the original owner slot variable; callsites borrow the bound owner slot",
            ));
        };
        let local = self
            .lookup(name)
            .ok_or_else(|| self.error("B100", format!("undefined native variable `{name}`")))?;
        match local.ty {
            Ty::Buffer | Ty::Record(_) | Ty::Internal(_) => {
                let _ = writeln!(self.code, "    leaq -{}(%rbp), %rax", local.slot);
                Ok(Ty::Borrow)
            }
            Ty::Borrow => {
                // Forwarding an already-borrowed slot keeps the original alias;
                // never re-wrap a Borrow of a Borrow.
                self.load(local);
                Ok(Ty::Borrow)
            }
            _ => Err(self.error(
                "N100",
                "native borrow requires an owned Buffer, collection metadata record, or internal owner slot",
            )),
        }
    }

    fn memory_put(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 3 {
            return Err(self.error("B108", "native put requires exactly 3 arguments".to_owned()));
        }
        let span_ty = self.expression(&args[0], Some(Ty::MutBytes))?;
        self.require(span_ty, Ty::MutBytes, "builtin argument")?;
        let span = Local {
            ty: span_ty,
            slot: self.allocate(span_ty),
            mutable: false,
        };
        self.store(span);
        let index_ty = self.expression(&args[1], Some(Ty::Usize))?;
        self.require(index_ty, Ty::Usize, "builtin argument")?;
        let index = Local {
            ty: Ty::Usize,
            slot: self.allocate(Ty::Usize),
            mutable: false,
        };
        self.store(index);
        let value_ty = self.expression(&args[2], Some(Ty::U8))?;
        self.require(value_ty, Ty::U8, "builtin argument")?;
        let value = Local {
            ty: Ty::U8,
            slot: self.allocate(Ty::U8),
            mutable: false,
        };
        self.store(value);
        let _ = writeln!(
            self.code,
            "    movq -{}(%rbp), %rax\n    cmpq -{}(%rbp), %rax\n    jae .Lsal_trap_{}\n    addq -{}(%rbp), %rax\n    jc .Lsal_trap_{}\n    movq %rax, %rcx\n    movq -{}(%rbp), %rax\n    movb %al, (%rcx)",
            index.slot,
            span.slot + 8,
            self.index,
            span.slot,
            self.index,
            value.slot
        );
        Ok(Ty::Void)
    }

    fn memory_borrow_end(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error(
                "B108",
                "native borrow_end requires exactly 1 argument".to_owned(),
            ));
        }
        // Ending a loan is purely static; the loan is already proven dead by
        // the memory pass. Evaluate once for order, emit no runtime.
        self.expression(&args[0], None)?;
        Ok(Ty::Void)
    }

    fn memory_text(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error("B108", "native text requires exactly 1 argument".to_owned()));
        }
        let ty = self.expression(&args[0], Some(Ty::Bytes))?;
        self.require(ty, Ty::Bytes, "builtin argument")?;
        let local = Local {
            ty,
            slot: self.allocate(ty),
            mutable: false,
        };
        self.store(local);
        let signature = self.signatures.get("TextValidate").ok_or_else(|| {
            self.error(
                "N100",
                "native text requires the SAL runtime `TextValidate(Bytes)->bool`; missing runtime signature",
            )
        })?;
        if signature.params != [Ty::Bytes]
            || signature.result != Ty::Bool
            || signature.foreign.is_some()
        {
            return Err(self.error(
                "N100",
                "native text requires the SAL runtime `TextValidate(Bytes)->bool`; missing runtime signature",
            ));
        }
        let index = signature.index;
        let _ = writeln!(
            self.code,
            "    movq -{}(%rbp), %rdi\n    movq -{}(%rbp), %rsi\n    call .Lsal_fn_{index}\n    testq %rax, %rax\n    je .Lsal_trap_{}",
            local.slot,
            local.slot + 8,
            self.index
        );
        self.load(local);
        Ok(Ty::Text)
    }

    fn memory_contract_assert(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 1 {
            return Err(self.error(
                "B108",
                "native SalContractAssert requires exactly 1 argument".to_owned(),
            ));
        }
        let ty = self.expression(&args[0], Some(Ty::Bool))?;
        self.require(ty, Ty::Bool, "builtin argument")?;
        let _ = writeln!(
            self.code,
            "    testq %rax, %rax\n    je .Lsal_trap_{}",
            self.index
        );
        Ok(Ty::Void)
    }

    fn memory_assert_disjoint(&mut self, args: &[Expr]) -> Result<Ty, Diagnostic> {
        if args.len() != 2 {
            return Err(self.error(
                "B108",
                "native SalMemoryAssertDisjoint requires exactly 2 arguments".to_owned(),
            ));
        }
        let first_ty = self.expression(&args[0], Some(Ty::Bytes))?;
        self.require(first_ty, Ty::Bytes, "builtin argument")?;
        let first = Local {
            ty: first_ty,
            slot: self.allocate(first_ty),
            mutable: false,
        };
        self.store(first);
        let second_ty = self.expression(&args[1], Some(Ty::Bytes))?;
        self.require(second_ty, Ty::Bytes, "builtin argument")?;
        let second = Local {
            ty: second_ty,
            slot: self.allocate(second_ty),
            mutable: false,
        };
        self.store(second);
        // Empty spans are disjoint with everything, even each other. Ends use
        // checked adds so wrap cannot hide an overlap; comparisons are
        // unsigned addresses.
        let done = self.label();
        let _ = writeln!(
            self.code,
            "    movq -{}(%rbp), %rax\n    movq -{}(%rbp), %rcx\n    movq -{}(%rbp), %rdx\n    movq -{}(%rbp), %r8\n    testq %rcx, %rcx\n    je {done}\n    testq %r8, %r8\n    je {done}\n    movq %rax, %r9\n    addq %rcx, %rax\n    jc .Lsal_trap_{}\n    movq %rdx, %rcx\n    addq %r8, %rdx\n    jc .Lsal_trap_{}\n    cmpq %rcx, %rax\n    jbe {done}\n    cmpq %r9, %rdx\n    jbe {done}\n    jmp .Lsal_trap_{}\n{done}:",
            first.slot,
            first.slot + 8,
            second.slot,
            second.slot + 8,
            self.index,
            self.index,
            self.index
        );
        Ok(Ty::Void)
    }

    /// Internal record constructor. Materializes like a `C` record (stable
    /// fixed-frame pointer in `%rax`) but permits span/pair/borrow fields and
    /// never becomes C-facing: callers reject `Internal` at the boundary.
    pub(super) fn construct_internal(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Result<Ty, Diagnostic> {
        let ty = Ty::Internal(
            self.internal
                .keys()
                .position(|record| record == name)
                .expect("known internal record"),
        );
        let (size, fields) = self
            .internal_layout(ty)
            .map(|layout| (layout.size, layout.fields.clone()))
            .expect("validated internal record");
        if args.len() != fields.len() {
            return Err(self.error(
                "B101",
                format!("record `{name}` constructor has wrong arity"),
            ));
        }
        let slot = self.allocate(ty);
        let _ = writeln!(
            self.code,
            "    leaq -{slot}(%rbp), %rdi\n    xorl %eax, %eax\n    movq ${size}, %rcx\n    rep stosb"
        );
        for (field, arg) in fields.iter().zip(args) {
            let expected = self.resolve(&field.ty).ok_or_else(|| {
                self.error("N100", format!("unknown internal field type in `{name}`"))
            })?;
            let actual = self.expression(arg, Some(expected))?;
            self.require(actual, expected, "record field")?;
            let destination = format!("{}(%rbp)", -(slot as i64) + field.offset as i64);
            match expected {
                Ty::Record(_) | Ty::Internal(_) => {
                    let field_size = if let Some(layout) = self.record_layout(expected) {
                        layout.size
                    } else if let Some(layout) = self.internal_layout(expected) {
                        layout.size
                    } else {
                        return Err(self.error("N100", "unknown nested record layout"));
                    };
                    let _ = writeln!(self.code, "    movq %rax, %rsi\n    leaq {destination}, %rdi\n    movq ${field_size}, %rcx\n    rep movsb");
                }
                Ty::Text | Ty::Bytes | Ty::Buffer | Ty::MutBytes => {
                    let _ = writeln!(
                        self.code,
                        "    movq %rax, {destination}\n    movq %rdx, {}(%rbp)",
                        -(slot as i64) + field.offset as i64 + 8
                    );
                }
                _ => {
                    let (instruction, register) = match expected.bits() {
                        8 => ("movb", "%al"),
                        16 => ("movw", "%ax"),
                        32 => ("movl", "%eax"),
                        _ => ("movq", "%rax"),
                    };
                    let _ = writeln!(self.code, "    {instruction} {register}, {destination}");
                }
            }
        }
        let _ = writeln!(self.code, "    leaq -{slot}(%rbp), %rax");
        Ok(ty)
    }
}
