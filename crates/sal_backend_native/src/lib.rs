//! Linux x86-64 GNU assembly, without implicit application-runtime imports.
//!
//! Text and Bytes are immutable byte spans, returned internally in rax/rdx.
//! Scalar arguments use the SysV integer registers; stack arguments hold the
//! remainder in source order. Integer records classify as one/two INTEGER
//! eightbytes or MEMORY per the AMD64 ABI; larger returns use a hidden RDI.
//! Checked integer arithmetic (add/sub/mul/div/rem) traps with `ud2` on
//! overflow, divide-by-zero, or range violation; span comparisons compare
//! content, never pointer identity.
//! C exports and imports are restricted to integer scalars, bool, C records,
//! and Void results: spans are never C ABI safe and Void never appears as a
//! parameter. Only Pure effects may cross the C boundary on exports; imports
//! require both SystemCall and UnsafeMemory. Contracts and unknown effects are
//! rejected everywhere.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use sal_ir::{c_record_layouts, CAbiTarget, CRecordLayout, Ir, OperationDecl, TypeRef};
use sal_syntax::{Diagnostic, Severity, Span};

#[cfg(test)]
mod concurrency_machine_tests;
mod lower;
#[cfg(test)]
mod tests;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeTarget {
    Executable,
    StaticLibrary,
}

#[derive(Debug, Clone)]
pub struct NativeProgram {
    pub assembly: String,
    pub header: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ty {
    Text,
    Bytes,
    I8,
    I16,
    I32,
    I64,
    U16,
    U32,
    U64,
    Usize,
    Isize,
    U8,
    Bool,
    Void,
    Record(usize),
}

impl Ty {
    fn from_ref(ty: &TypeRef) -> Option<Self> {
        match ty {
            TypeRef::Named(name) => match name.as_str() {
                "Text" => Some(Self::Text),
                "Bytes" => Some(Self::Bytes),
                "i8" => Some(Self::I8),
                "i16" => Some(Self::I16),
                "i32" => Some(Self::I32),
                "i64" => Some(Self::I64),
                "u16" => Some(Self::U16),
                "u32" => Some(Self::U32),
                "u64" => Some(Self::U64),
                "usize" => Some(Self::Usize),
                "isize" => Some(Self::Isize),
                "u8" => Some(Self::U8),
                "bool" => Some(Self::Bool),
                "Void" => Some(Self::Void),
                _ => None,
            },
            TypeRef::Generic { .. } => None,
        }
    }

    fn resolve(ty: &TypeRef, layouts: &BTreeMap<String, CRecordLayout>) -> Option<Self> {
        match ty {
            TypeRef::Generic { .. } => None,
            TypeRef::Named(name) => {
                if let Some(primitive) = Self::from_ref(ty) {
                    // A valid record can never collide with a primitive name;
                    // collisions are rejected by layout validation and fail
                    // closed here via the caller's diagnostics.
                    Some(primitive)
                } else {
                    layouts.keys().position(|key| key == name).map(Self::Record)
                }
            }
        }
    }

    fn span(self) -> bool {
        matches!(self, Self::Text | Self::Bytes)
    }

    fn slots(self) -> usize {
        match self {
            Self::Void => 0,
            Self::Text | Self::Bytes => 2,
            // Records use their own C geometry in abi::bytes; this is only a
            // defensive fallback so an accidental call cannot panic.
            Self::Record(_) => 1,
            _ => 1,
        }
    }

    fn integer(self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::Usize
                | Self::Isize
                | Self::U8
        )
    }

    fn signed(self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::Isize
        )
    }

    fn bits(self) -> u32 {
        match self {
            Self::Bool | Self::I8 | Self::U8 => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 | Self::Usize | Self::Isize => 64,
            // Spans, Void, and records never reach narrow lowering; report a
            // full word so an accidental use emits a wide move, not a panic.
            Self::Text | Self::Bytes | Self::Void | Self::Record(_) => 64,
        }
    }

    fn fits_literal(self, value: i64) -> bool {
        match self {
            Self::I8 => i8::try_from(value).is_ok(),
            Self::I16 => i16::try_from(value).is_ok(),
            Self::I32 => i32::try_from(value).is_ok(),
            Self::I64 | Self::Isize => true,
            Self::U8 => u8::try_from(value).is_ok(),
            Self::U16 => u16::try_from(value).is_ok(),
            Self::U32 => u32::try_from(value).is_ok(),
            Self::U64 | Self::Usize => value >= 0,
            _ => false,
        }
    }

    fn c_name(self) -> &'static str {
        match self {
            Self::I8 => "int8_t",
            Self::I16 => "int16_t",
            Self::I32 => "int32_t",
            Self::I64 => "int64_t",
            Self::U16 => "uint16_t",
            Self::U32 => "uint32_t",
            Self::U64 => "uint64_t",
            Self::Usize => "size_t",
            Self::Isize => "intptr_t",
            Self::U8 => "uint8_t",
            Self::Bool => "bool",
            Self::Void => "void",
            Self::Text | Self::Bytes | Self::Record(_) => {
                unreachable!("spans and records cannot pass C export validation")
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Signature {
    index: usize,
    params: Vec<Ty>,
    result: Ty,
    foreign: Option<String>,
}

fn error(code: &'static str, message: impl Into<String>, span: &Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message: message.into(),
        span: span.clone(),
        suggestion: None,
    }
}

fn identifier(name: &str) -> bool {
    let mut bytes = name.bytes();
    matches!(bytes.next(), Some(b'a'..=b'z' | b'A'..=b'Z' | b'_'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

static C_RESERVED: &[&str] = &[
    "INT16_C",
    "INT16_MAX",
    "INT16_MIN",
    "INT32_C",
    "INT32_MAX",
    "INT32_MIN",
    "INT64_C",
    "INT64_MAX",
    "INT64_MIN",
    "INT8_C",
    "INT8_MAX",
    "INT8_MIN",
    "INTMAX_C",
    "INTMAX_MAX",
    "INTMAX_MIN",
    "INTPTR_MAX",
    "INTPTR_MIN",
    "INT_FAST16_MAX",
    "INT_FAST16_MIN",
    "INT_FAST32_MAX",
    "INT_FAST32_MIN",
    "INT_FAST64_MAX",
    "INT_FAST64_MIN",
    "INT_FAST8_MAX",
    "INT_FAST8_MIN",
    "INT_LEAST16_MAX",
    "INT_LEAST16_MIN",
    "INT_LEAST32_MAX",
    "INT_LEAST32_MIN",
    "INT_LEAST64_MAX",
    "INT_LEAST64_MIN",
    "INT_LEAST8_MAX",
    "INT_LEAST8_MIN",
    "NDEBUG",
    "NULL",
    "PTRDIFF_MAX",
    "PTRDIFF_MIN",
    "SIG_ATOMIC_MAX",
    "SIG_ATOMIC_MIN",
    "SIZE_MAX",
    "UINT16_C",
    "UINT16_MAX",
    "UINT32_C",
    "UINT32_MAX",
    "UINT64_C",
    "UINT64_MAX",
    "UINT8_C",
    "UINT8_MAX",
    "UINTMAX_C",
    "UINTMAX_MAX",
    "UINTPTR_MAX",
    "UINT_FAST16_MAX",
    "UINT_FAST32_MAX",
    "UINT_FAST64_MAX",
    "UINT_FAST8_MAX",
    "UINT_LEAST16_MAX",
    "UINT_LEAST32_MAX",
    "UINT_LEAST64_MAX",
    "UINT_LEAST8_MAX",
    "WCHAR_MAX",
    "WCHAR_MIN",
    "WINT_MAX",
    "WINT_MIN",
    "assert",
    "int16_t",
    "int32_t",
    "int64_t",
    "int8_t",
    "int_fast16_t",
    "int_fast32_t",
    "int_fast64_t",
    "int_fast8_t",
    "int_least16_t",
    "int_least32_t",
    "int_least64_t",
    "int_least8_t",
    "intmax_t",
    "intptr_t",
    "max_align_t",
    "offsetof",
    "ptrdiff_t",
    "size_t",
    "static_assert",
    "std",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "uint8_t",
    "uint_fast16_t",
    "uint_fast32_t",
    "uint_fast64_t",
    "uint_fast8_t",
    "uint_least16_t",
    "uint_least32_t",
    "uint_least64_t",
    "uint_least8_t",
    "uintmax_t",
    "uintptr_t",
    "wchar_t",
];
fn is_c_typedef_or_macro(name: &str) -> bool {
    C_RESERVED.binary_search(&name).is_ok()
}

// These names cannot be declared by a portable C11/C++ header after its
// includes. Leading underscores and double underscores are reserved; typedef
// and macro names from the included headers would not compile as function or
// member names.
fn c_identifier(name: &str) -> bool {
    if !identifier(name) {
        return false;
    }
    if name.starts_with('_') || name.contains("__") {
        return false;
    }
    if is_c_typedef_or_macro(name) {
        return false;
    }
    if C_KEYWORDS.binary_search(&name).is_ok() {
        return false;
    }
    true
}
static C_KEYWORDS: &[&str] = &[
    "alignas",
    "alignof",
    "and",
    "and_eq",
    "asm",
    "auto",
    "bitand",
    "bitor",
    "bool",
    "break",
    "case",
    "catch",
    "char",
    "char16_t",
    "char32_t",
    "char8_t",
    "class",
    "co_await",
    "co_return",
    "co_yield",
    "compl",
    "concept",
    "const",
    "const_cast",
    "consteval",
    "constexpr",
    "constinit",
    "continue",
    "decltype",
    "default",
    "delete",
    "do",
    "double",
    "dynamic_cast",
    "else",
    "enum",
    "explicit",
    "export",
    "extern",
    "false",
    "float",
    "for",
    "friend",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "mutable",
    "namespace",
    "new",
    "noexcept",
    "not",
    "not_eq",
    "nullptr",
    "operator",
    "or",
    "or_eq",
    "private",
    "protected",
    "public",
    "register",
    "reinterpret_cast",
    "requires",
    "restrict",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "static_assert",
    "static_cast",
    "struct",
    "switch",
    "template",
    "this",
    "thread_local",
    "throw",
    "true",
    "try",
    "typedef",
    "typeid",
    "typename",
    "union",
    "unsigned",
    "using",
    "virtual",
    "void",
    "volatile",
    "wchar_t",
    "while",
    "xor",
    "xor_eq",
];

fn is_reserved_runtime_symbol(name: &str) -> bool {
    matches!(name, "_start" | "main") || name.starts_with("sal_record_")
}

fn record_c_name(sal_name: &str) -> String {
    format!("sal_record_{sal_name}")
}

fn header_ty(layouts: &BTreeMap<String, CRecordLayout>, ty: Ty) -> String {
    match ty {
        Ty::Record(index) => layouts
            .keys()
            .nth(index)
            .map(|name| record_c_name(name))
            .expect("validated record index"),
        _ => ty.c_name().to_owned(),
    }
}

fn ordered_record_names(layouts: &BTreeMap<String, CRecordLayout>) -> Vec<String> {
    let mut order = Vec::with_capacity(layouts.len());
    let mut done: BTreeSet<&str> = BTreeSet::new();
    // Shared layout validation has already ruled out cycles. An explicit DFS
    // emits dependencies first without recursive host-stack use or repeated
    // full-map sweeps for long chains.
    let mut pending = Vec::new();
    for name in layouts.keys() {
        pending.push((name.as_str(), false));
        while let Some((name, expanded)) = pending.pop() {
            if done.contains(name) {
                continue;
            }
            if expanded {
                done.insert(name);
                order.push(name.to_owned());
                continue;
            }
            pending.push((name, true));
            for field in layouts[name].fields.iter().rev() {
                let TypeRef::Named(dependency) = &field.ty else {
                    continue;
                };
                if layouts.contains_key(dependency) && !done.contains(dependency.as_str()) {
                    pending.push((dependency.as_str(), false));
                }
            }
        }
    }
    order
}

/// Validate the IR and emit deterministic, position-independent function code.
/// This deliberately does not use the legacy HTTP/Rust `check_exec` gate.
/// GNU as/ld/ar are build tools; the emitted program has no runtime imports.
pub fn emit_native(ir: &Ir, target: NativeTarget) -> Result<NativeProgram, Vec<Diagnostic>> {
    if let Err(diagnostic) = lower::preflight(ir) {
        return Err(vec![diagnostic]);
    }
    let (_, mut diagnostics) = sal_ir::build(&ir.file);
    diagnostics.extend(sal_ir::check_types(ir));
    diagnostics.extend(sal_ir::check_bodies(ir));
    diagnostics.extend(sal_ir::check_effects(ir));
    // Consume the shared layout map once. Invalid records are already reported
    // by check_types; use an empty map here so record uses fail closed via
    // Ty::resolve without duplicating every E2010 diagnostic.
    let layouts: BTreeMap<String, CRecordLayout> =
        c_record_layouts(ir, CAbiTarget::LinuxX86_64).unwrap_or_default();
    let fallback = Span::single(1, 1);
    let mut unsupported_servers: Vec<_> = ir
        .servers
        .values()
        .map(|s| (&s.name, &s.span))
        .chain(ir.routes.values().map(|r| (&r.name, &r.span)))
        .collect();
    unsupported_servers.sort_by(|a, b| a.0.cmp(b.0));
    for (name, span) in unsupported_servers {
        diagnostics.push(error("N107", format!("native server/route `{name}` is not implemented; select the explicit Rust HTTP backend"), span));
    }
    // Validate C-facing record names in deterministic order, including invalid
    // records absent from the layout map. Unmarked specification entities do
    // not acquire native ABI restrictions.
    let mut declared_records: Vec<_> = ir
        .entities
        .iter()
        .filter(|(_, entity)| entity.c_layout)
        .collect();
    declared_records.sort_by(|a, b| a.0.cmp(b.0));
    for (name, entity) in declared_records {
        if name != &entity.name || !c_identifier(name) {
            diagnostics.push(error(
                "N102",
                format!("C record `{name}` is not a matching available C identifier"),
                &entity.span,
            ));
        }
        for field in &entity.fields {
            if !c_identifier(&field.name) {
                diagnostics.push(error(
                    "N102",
                    format!(
                        "field `{}` in C record `{name}` is not an available C identifier",
                        field.name
                    ),
                    &field.span,
                ));
            }
        }
    }
    let operations: BTreeMap<_, _> = ir
        .operations
        .iter()
        .map(|(name, op)| (name.as_str(), op))
        .collect();
    let mut signatures = BTreeMap::new();
    let mut used_symbols = BTreeSet::new();
    for (index, (name, operation)) in operations.iter().enumerate() {
        let span = &operation.span;
        if !identifier(name) || !identifier(&operation.name) || *name != operation.name {
            diagnostics.push(error(
                "N100",
                "native operation names must be matching ASCII identifiers",
                span,
            ));
        }
        let params: Option<Vec<_>> = operation
            .accepts
            .iter()
            .map(|p| Ty::resolve(&p.ty, &layouts))
            .collect();
        // An omitted result means Void: a procedure with no return value.
        let result = operation
            .returns
            .as_ref()
            .map(|ty| Ty::resolve(ty, &layouts))
            .unwrap_or(Some(Ty::Void));
        if params.is_none() || result.is_none() {
            diagnostics.push(error("N100", format!("operation `{name}` requires supported native parameters and result: Text, Bytes, i8, i16, i32, i64, u16, u32, u64, usize, isize, u8, bool, Void, or a valid C record; Character, Word, floats and aggregates are unsupported"), span));
        }
        let void_param = params.as_ref().is_some_and(|p| p.contains(&Ty::Void));
        if void_param {
            diagnostics.push(error(
                "N100",
                format!("operation `{name}` cannot accept a Void parameter"),
                span,
            ));
        }
        let has_code = !operation.body.is_empty() || operation.responds_literal.is_some();
        let is_import = operation.c_import.is_some();
        let is_export = operation.c_export.is_some();
        if is_import && is_export {
            diagnostics.push(error(
                "N102",
                format!("operation `{name}` cannot both import and export C"),
                span,
            ));
        }
        if is_import {
            if has_code {
                diagnostics.push(error(
                    "N103",
                    format!("C import `{name}` must not have a SAL body"),
                    span,
                ));
            }
            if operation.name == "Main" {
                diagnostics.push(error(
                    "N105",
                    "C imports cannot serve as the native Main entrypoint",
                    span,
                ));
            }
        } else if !has_code {
            diagnostics.push(error(
                "N103",
                format!("operation `{name}` has no executable body"),
                span,
            ));
        }
        // Pure is always allowed on ordinary code. Exports must stay pure;
        // imports must own both machine capabilities and never pretend pure.
        // Contracts and unknown effects never cross the native boundary.
        if is_export && operation.effects.iter().any(|effect| effect != "Pure") {
            diagnostics.push(error("N104", format!("operation `{name}` has contracts or effects that native execution cannot enforce"), span));
        }
        if is_export && (!operation.requires.is_empty() || !operation.ensures.is_empty()) {
            diagnostics.push(error("N104", format!("operation `{name}` has contracts or effects that native execution cannot enforce"), span));
        }
        if is_import {
            let has_syscall = operation
                .effects
                .iter()
                .any(|effect| effect == "SystemCall");
            let has_unsafe = operation
                .effects
                .iter()
                .any(|effect| effect == "UnsafeMemory");
            if !has_syscall || !has_unsafe {
                diagnostics.push(error(
                    "N104",
                    format!("C import `{name}` must declare both SystemCall and UnsafeMemory"),
                    span,
                ));
            }
            if operation
                .effects
                .iter()
                .any(|effect| !matches!(effect.as_str(), "SystemCall" | "UnsafeMemory"))
                || !operation.requires.is_empty()
                || !operation.ensures.is_empty()
            {
                diagnostics.push(error("N104", format!("operation `{name}` has contracts or effects that native execution cannot enforce"), span));
            }
        }
        if !is_export
            && !is_import
            && (operation
                .effects
                .iter()
                .any(|effect| !matches!(effect.as_str(), "Pure" | "SystemCall" | "UnsafeMemory"))
                || !operation.requires.is_empty()
                || !operation.ensures.is_empty())
        {
            diagnostics.push(error("N104", format!("operation `{name}` has contracts or effects that native execution cannot enforce"), span));
        }
        for (kind, symbol) in [
            ("export", operation.c_export.as_ref()),
            ("import", operation.c_import.as_ref()),
        ] {
            let Some(symbol) = symbol else { continue };
            // The generated record namespace is reserved as a whole, so no
            // exported/imported function can collide with a record typedef.
            if !c_identifier(symbol) || is_reserved_runtime_symbol(symbol) {
                diagnostics.push(error(
                    "N102",
                    format!("C {kind} `{symbol}` is not an available C/ELF identifier"),
                    span,
                ));
            }
            if !used_symbols.insert(symbol.as_str()) {
                diagnostics.push(error(
                    "N102",
                    format!("duplicate C symbol `{symbol}`"),
                    span,
                ));
            }
            let spans = params
                .as_ref()
                .is_some_and(|params| params.iter().any(|ty| ty.span()));
            if spans || result.is_some_and(|ty| ty.span()) {
                diagnostics.push(error("N100", format!("C {kind} `{symbol}` permits only integer scalars, bool, C records, and Void results; Text and Bytes are not C ABI safe"), span));
            }
        }
        if let (Some(params), Some(result)) = (params, result) {
            signatures.insert(
                (*name).to_owned(),
                Signature {
                    index,
                    params,
                    result,
                    foreign: operation.c_import.clone(),
                },
            );
        }
    }
    let entry = if target == NativeTarget::Executable {
        let text_candidates: Vec<_> = operations
            .values()
            .copied()
            .filter(|op| {
                op.c_import.is_none()
                    && op.accepts.is_empty()
                    && (!op.body.is_empty() || op.responds_literal.is_some())
                    && op.returns.as_ref().and_then(|ty| Ty::resolve(ty, &layouts))
                        == Some(Ty::Text)
            })
            .collect();
        let int_entry = operations.get("Main").copied().filter(|op| {
            op.c_import.is_none()
                && op.accepts.is_empty()
                && !op.body.is_empty()
                && op.returns.as_ref().and_then(|ty| Ty::resolve(ty, &layouts)) == Some(Ty::I64)
        });
        let text_entry = text_candidates
            .iter()
            .find(|op| op.name == "Main")
            .copied()
            .or_else(|| {
                if text_candidates.len() == 1 {
                    text_candidates.first().copied()
                } else {
                    None
                }
            });
        // Prefer an explicit Main; a sole zero-argument Text operation remains
        // the fallback only when no valid Main of either supported kind exists.
        // Imports never serve as entrypoints.
        let entry = int_entry.or(text_entry);
        if entry.is_none() {
            diagnostics.push(error("N105", "native executable requires Main() -> Text, Main() -> i64, or a sole zero-argument Text-returning operation", &fallback));
        }
        entry
            .and_then(|op| signatures.get(&op.name))
            .map(|sig| (sig.index, sig.result))
    } else {
        if !operations.values().any(|op| op.c_export.is_some()) {
            diagnostics.push(error(
                "N106",
                "native static library requires at least one explicit C export",
                &fallback,
            ));
        }
        None
    };
    let mut assembly =
        String::from("# SAL native: Linux x86-64 SysV; overflow traps with ud2.\n.text\n");
    let mut literals = Vec::new();
    for operation in operations.values() {
        if operation.c_import.is_some() {
            continue;
        }
        if signatures
            .get(&operation.name)
            .is_some_and(|signature| !signature.params.contains(&Ty::Void))
        {
            match lower::function(operation, &signatures, &layouts, &mut literals) {
                Ok(code) => assembly.push_str(&code),
                Err(diagnostic) => diagnostics.push(diagnostic),
            }
        }
    }
    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return Err(diagnostics);
    }
    if let Some((index, kind)) = entry {
        emit_start(&mut assembly, index, kind);
    }
    if !literals.is_empty() || entry.is_some() {
        assembly.push_str(".section .rodata\n");
        for (index, literal) in literals.iter().enumerate() {
            let _ = writeln!(assembly, ".Lsal_text_{index}:");
            // Decimal byte directives avoid assembler escaping/encoding ambiguities.
            if literal.is_empty() {
                assembly.push_str("    .byte 0\n");
            } else {
                for chunk in literal.as_bytes().chunks(32) {
                    assembly.push_str("    .byte ");
                    for (i, byte) in chunk.iter().enumerate() {
                        if i != 0 {
                            assembly.push(',');
                        }
                        let _ = write!(assembly, "{byte}");
                    }
                    assembly.push('\n');
                }
            }
        }
        if matches!(entry, Some((_, Ty::Text))) {
            assembly.push_str(".Lsal_newline:\n    .byte 10\n");
        }
    }
    if assembly.contains(".Lsal_concurrency_state(%rip)") {
        assembly.push_str(".bss\n.balign 16\n.Lsal_concurrency_state:\n    .zero 16\n");
    }
    assembly.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    let header = if target == NativeTarget::StaticLibrary {
        Some(emit_header(
            operations.values().copied(),
            &signatures,
            &layouts,
        ))
    } else {
        None
    };
    Ok(NativeProgram { assembly, header })
}

fn emit_header<'a>(
    operations: impl Iterator<Item = &'a OperationDecl>,
    signatures: &BTreeMap<String, Signature>,
    layouts: &BTreeMap<String, CRecordLayout>,
) -> String {
    let mut header = String::from("#include <stdint.h>\n#include <stddef.h>\n#include <stdbool.h>\n#include <assert.h>\n\n/* Linux x86-64 SysV ABI. SAL Text and Character are not C ABI safe; Bytes spans are not C ABI safe either.\n * Checked integer arithmetic traps; no SAL runtime is linked. Records are by-value C structs.\n */\n#ifdef __cplusplus\nextern \"C\" {\n#endif\n\n");
    for name in ordered_record_names(layouts) {
        let layout = &layouts[&name];
        let c_name = record_c_name(&name);
        let _ = writeln!(header, "typedef struct {{");
        for field in &layout.fields {
            let ty = Ty::resolve(&field.ty, layouts).expect("validated record field");
            let _ = writeln!(header, "    {} {};", header_ty(layouts, ty), field.name);
        }
        let _ = writeln!(header, "}} {c_name};");
        let _ = writeln!(
            header,
            "static_assert(sizeof({c_name}) == {}u, \"{c_name} size\");",
            layout.size
        );
        let _ = writeln!(
            header,
            "#ifdef __cplusplus\nstatic_assert(alignof({c_name}) == {}u, \"{c_name} align\");\n#else\nstatic_assert(_Alignof({c_name}) == {}u, \"{c_name} align\");\n#endif",
            layout.align, layout.align
        );
        for field in &layout.fields {
            let _ = writeln!(
                header,
                "static_assert(offsetof({c_name}, {}) == {}u, \"{c_name}.{} offset\");",
                field.name, field.offset, field.name
            );
        }
        header.push('\n');
    }
    for operation in operations {
        let symbol = operation.c_export.as_ref().or(operation.c_import.as_ref());
        if let Some(symbol) = symbol {
            let Some(signature) = signatures.get(&operation.name) else {
                continue;
            };
            let _ = write!(header, "{} {symbol}(", header_ty(layouts, signature.result));
            if signature.params.is_empty() {
                header.push_str("void");
            }
            for (index, ty) in signature.params.iter().enumerate() {
                if index != 0 {
                    header.push_str(", ");
                }
                let _ = write!(header, "{} arg{index}", header_ty(layouts, *ty));
            }
            header.push_str(");\n");
        }
    }
    header.push_str("\n#ifdef __cplusplus\n}\n#endif\n");
    // Fixed FNV-1a, not a process-randomized host hasher. Different export
    // declarations must not suppress each other's headers when composed.
    let hash = header.bytes().fold(0xcbf29ce484222325_u64, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3)
    });
    let guard = format!("SAL_NATIVE_EXPORTS_{hash:016X}_H");
    format!("#ifndef {guard}\n#define {guard}\n{header}#endif /* {guard} */\n")
}

fn emit_start(assembly: &mut String, index: usize, kind: Ty) {
    match kind {
        Ty::I64 => {
            // Main() -> i64: the result is the Linux exit status. No output.
            let _ = writeln!(
                assembly,
                ".globl _start\n.type _start,@function\n_start:\n    andq $-16, %rsp\n    call .Lsal_fn_{index}\n    movq %rax, %rdi\n    movl $60, %eax\n    syscall\n    ud2\n.size _start, .-_start"
            );
        }
        Ty::Text => {
            let _ = writeln!(assembly, ".globl _start\n.type _start,@function\n_start:\n    andq $-16, %rsp\n    call .Lsal_fn_{index}\n    movq %rax, %rsi");
            assembly.push_str(
                r#"    call .Lsal_write_all
    leaq .Lsal_newline(%rip), %rsi
    movq $1, %rdx
    call .Lsal_write_all
    xorl %edi, %edi
    movl $60, %eax
    syscall
    ud2
.size _start, .-_start
# write(1, ptr, len): retry EINTR, advance partial writes, fail closed.
.Lsal_write_all:
    testq %rdx, %rdx
    je .Lsal_write_done
.Lsal_write_retry:
    movl $1, %eax
    movl $1, %edi
    syscall
    cmpq $-4, %rax
    je .Lsal_write_retry
    testq %rax, %rax
    jle .Lsal_output_error
    addq %rax, %rsi
    subq %rax, %rdx
    jne .Lsal_write_retry
.Lsal_write_done:
    ret
.Lsal_output_error:
    movl $1, %edi
    movl $231, %eax
    syscall
    ud2
"#,
            );
        }
        _ => unreachable!("native entry validation admits only i64 and Text"),
    }
}
