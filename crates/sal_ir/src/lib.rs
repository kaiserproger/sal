//! SAL typed IR: registry + semantic checkers.
//!
//! CONTRACT (do not change public signatures; implement bodies only):
//! - `build` indexes top-level items by name. Duplicate top-level name (any kind)
//!   -> E1001 error diagnostic, first definition wins. Unresolved uses -> E1002;
//!   reserved intrinsic declarations -> E1003; neither is registered.
//! - `check_types` (E2xx): every FieldDecl/ParamDecl/returns type must resolve.
//!   Primitives: bool String UUID u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 f32 f64
//!   usize isize Text Word Character Bytes. Generic builtins: Option<T> Vec<T> (arity 1), Result<T,E>
//!   (arity 2), Money<CUR> (arity 1, CUR matches ^[A-Z]{3}$). Other Named must be
//!   a known entity/enum; other Generic names -> E2002. Recurse into args.
//!   E2001 unknown type, E2003 bad Money currency, E2004 arity mismatch.
//! - `check_architecture` (ARCH1xx, all errors): ARCH101 service/module `belongs
//!   to` unknown layer; ARCH102 layer `owns` name that is not a known
//!   entity/service/module/operation; ARCH103 may/must-not target unknown layer;
//!   ARCH104 same layer pair both may- and must-not-depend; ARCH105 circular
//!   may-depend-on cycle (message lists cycle); ARCH106 two modules own the same
//!   resource; ARCH107 module both may-modify/owns and cannot-modify a resource.
//!   `owns`/`implements` targets that are plain resources/interfaces are NOT
//!   validated except for ARCH106/ARCH107.
//! - `check_effects`: EFF202
//!   operation effects contain `Pure` plus others (error); EFF203 missing a
//!   direct intrinsic or declared callee effect, including all nested calls.
//! - `check_bodies` (B1xx errors): lexical names (B100), call/arity (B101),
//!   return types (B102), bool conditions (B103), duplicate bindings (B104),
//!   operators (B105), return coverage (B106), argument types (B107), builtin
//!   use (B108), fields/indexes (B109), readonly assignment (B110). Assignment
//!   type mismatch is B107; parameters are readonly. Locals are lexical and
//!   mutable only with `let mut`; nested blocks may shadow. Literal construction checks
//!   integer ranges and Word/Character constraints. Bodyless specifications
//!   remain valid. Diagnostics use operation spans in name/source order.
//! - `verify_rust_imports` (ARCH0xx/ARCH2xx/ARCH3xx): for each file resolve its
//!   layer via `layer_of`; unknown module -> ARCH201 error. Import path first
//!   segment (lowercased) matching a known layer name (lowercased) is a layer
//!   dep: if target != own layer and no may-depend edge own->target -> ARCH001
//!   error. Non-layer first segments are external crates (allowed), except the
//!   capability map below. ARCH202 warning when layer cannot be determined.
//!   Capability map (case-insensitive substring match on ANY path segment):
//!   DatabaseAccess -> [sqlx postgres diesel rusqlite sea_orm mongodb redis];
//!   HTTPAccess -> [reqwest hyper axum actix_web tower_http]. Match against the
//!   file module's `forbids` list (case-insensitive) -> ARCH301 error.
//! - `layer_of`: service -> belongs_to; module -> belongs_to; entity -> layer
//!   whose `owns` contains it; operation -> None.
//!
//! Checkers inspect the first registered definition and report in name/rule order.
//! Type traversal and dependency-cycle detection use explicit stacks.

use sal_syntax::{Diagnostic, LayerRule, SalFile};
use std::collections::{HashMap, HashSet};

pub use sal_syntax::{
    EntityDecl, EnumDecl, Expr, FieldDecl, Item, LayerDecl, ModuleDecl, OperationDecl, ParamDecl,
    RespondsKind, RouteDecl, RouteMethod, ServerDecl, ServiceDecl, Severity, Span, Stmt, TypeRef,
};

mod c_layout;
pub mod collections;
mod concurrency;
pub mod declarations;
pub mod memory;
pub use c_layout::{c_record_layouts, CAbiTarget, CFieldLayout, CRecordLayout};

#[derive(Debug, Clone, Default)]
pub struct Ir {
    pub file: SalFile,
    pub entities: HashMap<String, EntityDecl>,
    pub enums: HashMap<String, EnumDecl>,
    pub layers: HashMap<String, LayerDecl>,
    pub services: HashMap<String, ServiceDecl>,
    pub operations: HashMap<String, OperationDecl>,
    pub modules: HashMap<String, ModuleDecl>,
    pub servers: HashMap<String, ServerDecl>,
    pub routes: HashMap<String, RouteDecl>,
}

#[derive(Debug, Clone)]
pub struct RustFile {
    pub module: String,
    pub imports: Vec<String>,
}

pub fn build(file: &SalFile) -> (Ir, Vec<Diagnostic>) {
    let (file, mut diagnostics) = lower_pipeline(file);
    let mut ir = Ir::default();
    for item in registered_items(&file, &mut diagnostics) {
        let (name, _) = item_identity(item);
        match item {
            Item::Application { .. } | Item::Use { .. } => {}
            Item::Entity(value) => {
                ir.entities.insert(name.to_owned(), value.clone());
            }
            Item::Enum(value) => {
                ir.enums.insert(name.to_owned(), value.clone());
            }
            Item::Layer(value) => {
                ir.layers.insert(name.to_owned(), value.clone());
            }
            Item::Service(value) => {
                ir.services.insert(name.to_owned(), value.clone());
            }
            Item::Operation(value) => {
                ir.operations.insert(name.to_owned(), value.clone());
            }
            Item::Module(value) => {
                ir.modules.insert(name.to_owned(), value.clone());
            }
            Item::Server(value) => {
                ir.servers.insert(name.to_owned(), value.clone());
            }
            Item::Route(value) => {
                ir.routes.insert(name.to_owned(), value.clone());
            }
        }
    }
    ir.file = file;
    (ir, diagnostics)
}

/// Shared lowering pipeline `declarations -> concurrency -> memory ->
/// collections`. A failing stage stops the pipeline but the file lowered by
/// the previous stages is kept, so later checkers see the derived
/// declarations (e.g. generated JSON codecs) and report the stage's real
/// diagnostics instead of cascading `unknown operation` noise.
///
/// Re-building an already collections-lowered file (backends re-run `build`
/// on `Ir::file`) skips the memory pass: memory validated the pre-lowering
/// source, and collections output is identified by the parser-false
/// `generated` flag, which source code cannot forge.
fn lower_pipeline(file: &SalFile) -> (SalFile, Vec<Diagnostic>) {
    let mut current = match declarations::lower(file) {
        Ok(next) => next,
        Err(diagnostics) => return (file.clone(), diagnostics),
    };
    current = match concurrency::lower(&current) {
        Ok(next) => next,
        Err(diagnostics) => return (current, diagnostics),
    };
    if !collections::is_lowered(&current) {
        current = match memory::lower(&current) {
            Ok(next) => next,
            Err(diagnostics) => return (current, diagnostics),
        };
    }
    match collections::lower(&current) {
        Ok(next) => (next, Vec::new()),
        Err(diagnostics) => (current, diagnostics),
    }
}

/// Validate the original namespace before a frontend consumes declarations.
pub fn check_declarations(file: &SalFile) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    registered_items(file, &mut diagnostics).for_each(drop);
    diagnostics
}

fn registered_items<'a>(
    file: &'a SalFile,
    diagnostics: &'a mut Vec<Diagnostic>,
) -> impl Iterator<Item = &'a Item> {
    let mut names = HashSet::new();
    file.items.iter().filter(move |item| {
        if let Item::Use { path, span } = item {
            diagnostics.push(error(
                "E1002",
                format!("unresolved use `{path}`; load source dependencies before building IR"),
                span,
            ));
            return false;
        }
        let (name, span) = item_identity(item);
        let generated = match item {
            Item::Operation(operation) => operation.generated,
            Item::Entity(entity) => entity.generated,
            _ => false,
        };
        let reserved_generation = name.starts_with("SalDecl")
            || name.starts_with("SalColl")
            || name.starts_with("SalConc");
        if builtin_signature(name).is_some()
            || is_numeric_intrinsic(name)
            || reflection_arity(name).is_some()
            || matches!(
                name,
                "Buffer" | "MutBytes" | "Borrow" | "Vector" | "Map" | "ValueResult"
            )
            || (reserved_generation && !generated)
        {
            diagnostics.push(error(
                "E1003",
                format!("top-level name `{name}` is reserved for the compiler"),
                span,
            ));
            return false;
        }
        if !names.insert(name) {
            diagnostics.push(error(
                "E1001",
                format!("duplicate top-level name `{name}`; first definition wins"),
                span,
            ));
            return false;
        }
        true
    })
}

pub fn check_types(ir: &Ir) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    if let Err(errors) = c_record_layouts(ir, CAbiTarget::LinuxX86_64) {
        diagnostics.extend(errors);
    }
    for (_, entity) in sorted_entries(&ir.entities) {
        for field in &entity.fields {
            check_type(ir, &field.ty, &field.span, &mut diagnostics);
        }
    }
    for (_, operation) in sorted_entries(&ir.operations) {
        if operation.c_import.is_some()
            && (operation.c_export.is_some()
                || !operation.body.is_empty()
                || operation.responds_literal.is_some())
        {
            diagnostics.push(error(
                "E2011",
                format!(
                    "C import `{}` cannot have a SAL body or export clause",
                    operation.name
                ),
                &operation.span,
            ));
        }
        for parameter in &operation.accepts {
            check_type(ir, &parameter.ty, &operation.span, &mut diagnostics);
        }
        if let Some(ty) = &operation.returns {
            check_type(ir, ty, &operation.span, &mut diagnostics);
        }
    }
    diagnostics
}

/// Checks lexical value types and return coverage without executing bodies.
/// Bodyless specifications are legal; executable backends must reject their use.
pub fn check_bodies(ir: &Ir) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (_, operation) in sorted_entries(&ir.operations) {
        if operation.body.is_empty() {
            continue;
        }
        let mut checker = BodyChecker {
            ir,
            operation,
            scopes: vec![HashMap::new()],
            loop_depth: 0,
            diagnostics: &mut diagnostics,
        };
        for parameter in &operation.accepts {
            checker.bind(&parameter.name, BodyType::declared(&parameter.ty), false);
        }
        if !checker.block(&operation.body) && operation.returns.is_some() {
            checker.report(
                "B106",
                format!(
                    "operation `{}` may finish without returning a value",
                    operation.name
                ),
            );
        }
    }
    diagnostics
}

/// Borrow declaration types and literal names instead of cloning type trees.
/// `pub(crate)`: shared with the compiler owner's memory/ownership passes
/// (concurrency checks, native lowering); this file owns the definitions.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum BodyType<'a> {
    Named(&'a str),
    Generic(&'a TypeRef),
    Void,
    Unknown,
}

impl<'a> BodyType<'a> {
    fn declared(ty: &'a TypeRef) -> Self {
        match ty {
            TypeRef::Named(name) => Self::Named(name),
            TypeRef::Generic { .. } => Self::Generic(ty),
        }
    }

    fn integer(self) -> bool {
        matches!(
            self,
            Self::Named(
                "i8" | "i16"
                    | "i32"
                    | "i64"
                    | "i128"
                    | "isize"
                    | "u8"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "u128"
                    | "usize"
            )
        )
    }

    fn numeric(self) -> bool {
        self.integer() || matches!(self, Self::Named("f32" | "f64"))
    }

    fn element(self) -> Option<Self> {
        match self {
            Self::Generic(TypeRef::Generic { name, args }) if name == "Vec" && args.len() == 1 => {
                Some(Self::declared(&args[0]))
            }
            _ => None,
        }
    }

    fn description(self) -> String {
        match self {
            Self::Named(name) => name.to_owned(),
            Self::Generic(ty) => format!("{ty:?}"),
            Self::Void => "no value".into(),
            Self::Unknown => "unknown".into(),
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Binding<'a> {
    ty: BodyType<'a>,
    mutable: bool,
}

#[derive(Clone, Copy)]
pub(crate) enum BuiltinArg {
    Exact(&'static str),
    Span,
    Length,
    Integer,
    MachineWord,
}
pub(crate) fn builtin_signature(name: &str) -> Option<(&'static [BuiltinArg], BodyType<'static>)> {
    use BuiltinArg::{Exact, Integer, Length, MachineWord, Span};
    let (args, result): (&[BuiltinArg], BodyType<'_>) = match name {
        "len" => (&[Length], BodyType::Named("usize")),
        "bytes" => (&[Exact("Text")], BodyType::Named("Bytes")),
        "text" => (&[Exact("Bytes")], BodyType::Named("Text")),
        "SalContractAssert" => (&[Exact("bool")], BodyType::Void),
        "SalMemoryAssertDisjoint" => (&[Exact("Bytes"), Exact("Bytes")], BodyType::Void),
        "byte" => (&[Exact("Bytes"), Exact("usize")], BodyType::Named("u8")),
        "slice" => (
            &[Exact("Bytes"), Exact("usize"), Exact("usize")],
            BodyType::Named("Bytes"),
        ),
        // Owner-dependent types are refined by the memory/collection passes;
        // concrete spans stay typed here. Allocation remains SystemCall.
        "buffer" => (&[Exact("usize")], BodyType::Named("Buffer")),
        "buffer_drop" | "borrow_end" => (&[Integer], BodyType::Void),
        "borrow_mut" | "slice_mut" => (
            &[Integer, Exact("usize"), Exact("usize")],
            BodyType::Named("MutBytes"),
        ),
        "view" => (&[Integer], BodyType::Named("Bytes")),
        "borrow" => (&[Integer], BodyType::Unknown),
        "put" => (&[Integer, Integer, Integer], BodyType::Void),
        "vector" => (&[Integer, Integer], BodyType::Unknown),
        "vector_len" | "vector_capacity" | "map_len" | "map_capacity" => {
            (&[Integer], BodyType::Named("usize"))
        }
        "vector_reserve" | "vector_push" | "map_reserve" => {
            (&[Integer, Integer], BodyType::Named("i64"))
        }
        "vector_get" | "map_get" | "map_remove" => (&[Integer, Integer], BodyType::Unknown),
        "vector_pop" => (&[Integer], BodyType::Unknown),
        "map_contains" => (&[Integer, Integer], BodyType::Named("bool")),
        "vector_set" | "map_insert" => (&[Integer, Integer, Integer], BodyType::Named("i64")),
        "vector_drop" | "map_drop" => (&[Integer], BodyType::Void),
        "map" => (&[Integer, Integer, Integer], BodyType::Unknown),
        // Pure machine-integer boundaries: arity here, same-width typing in
        // `BodyChecker::call` before the generic argument loop.
        "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "bit_and" | "bit_or" | "bit_xor" => {
            (&[Integer, Integer], BodyType::Unknown)
        }
        "bit_not" => (&[Integer], BodyType::Unknown),
        "shift_left" | "shift_right" => (&[Integer, Integer], BodyType::Unknown),
        "bits_as" => (&[Integer, Integer], BodyType::Unknown),
        "usize" => (&[Integer], BodyType::Named("usize")),
        "i64" => (&[Integer], BodyType::Named("i64")),
        "u8" => (&[Integer], BodyType::Named("u8")),
        "i8" => (&[Integer], BodyType::Named("i8")),
        "i16" => (&[Integer], BodyType::Named("i16")),
        "i32" => (&[Integer], BodyType::Named("i32")),
        "isize" => (&[Integer], BodyType::Named("isize")),
        "u16" => (&[Integer], BodyType::Named("u16")),
        "u32" => (&[Integer], BodyType::Named("u32")),
        "u64" => (&[Integer], BodyType::Named("u64")),
        "syscall" => (&[MachineWord; 7], BodyType::Named("i64")),
        "address" => (&[Span], BodyType::Named("usize")),
        "bytes_at" => (&[Exact("usize"), Exact("usize")], BodyType::Named("Bytes")),
        "load8" => (&[Exact("usize")], BodyType::Named("u8")),
        "store8" => (&[Exact("usize"), Exact("u8")], BodyType::Void),
        "atomic_load" => (&[Exact("usize")], BodyType::Named("u32")),
        "atomic_store" => (&[Exact("usize"), Exact("u32")], BodyType::Void),
        "atomic_cas" => (
            &[Exact("usize"), Exact("u32"), Exact("u32")],
            BodyType::Named("u32"),
        ),
        "load64" => (&[Exact("usize")], BodyType::Named("usize")),
        "store64" => (&[Exact("usize"), Exact("usize")], BodyType::Void),
        "concurrency_state" => (&[], BodyType::Named("usize")),
        // The compile-time operation operand is checked separately below.
        "operation_address" => (&[Exact("usize")], BodyType::Named("usize")),
        "thread_launch" => (&[Exact("usize"); 4], BodyType::Named("i64")),
        _ => return None,
    };
    Some((args, result))
}

pub(crate) fn intrinsic_effects(name: &str) -> &'static [&'static str] {
    match name {
        "buffer" | "buffer_drop" | "vector" | "vector_drop" | "vector_reserve" | "vector_push"
        | "map" | "map_drop" | "map_reserve" | "map_insert" => &["SystemCall"],
        "syscall" | "thread_launch" => &["SystemCall", "UnsafeMemory"],
        "address" | "bytes_at" | "load8" | "store8" | "atomic_load" | "atomic_store"
        | "atomic_cas" | "load64" | "store64" | "concurrency_state" | "operation_address" => {
            &["UnsafeMemory"]
        }
        _ => &[],
    }
}

pub(crate) fn reflection_arity(name: &str) -> Option<usize> {
    match name {
        "size_of" | "align_of" => Some(1),
        "offset_of" => Some(2),
        _ => None,
    }
}

struct BodyChecker<'a, 'd> {
    ir: &'a Ir,
    operation: &'a OperationDecl,
    scopes: Vec<HashMap<&'a str, Binding<'a>>>,
    loop_depth: usize,
    diagnostics: &'d mut Vec<Diagnostic>,
}

impl<'a> BodyChecker<'a, '_> {
    fn report(&mut self, code: &'static str, message: String) {
        self.diagnostics
            .push(error(code, message, &self.operation.span));
    }

    fn bind(&mut self, name: &'a str, ty: BodyType<'a>, mutable: bool) {
        let scope = self.scopes.last_mut().expect("operation has a root scope");
        if let std::collections::hash_map::Entry::Vacant(entry) = scope.entry(name) {
            entry.insert(Binding { ty, mutable });
        } else {
            self.report(
                "B104",
                format!("duplicate binding `{name}` in the same scope"),
            );
        }
    }

    fn lookup(&self, name: &str) -> Option<Binding<'a>> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn require(&mut self, actual: BodyType<'a>, expected: BodyType<'a>, code: &'static str) {
        if actual != BodyType::Unknown && expected != BodyType::Unknown && actual != expected {
            self.report(
                code,
                format!(
                    "expected {}, got {}",
                    expected.description(),
                    actual.description()
                ),
            );
        }
    }

    fn nested_block(&mut self, body: &'a [Stmt], binding: Option<(&'a str, BodyType<'a>)>) -> bool {
        self.scopes.push(HashMap::new());
        if let Some((name, ty)) = binding {
            self.bind(name, ty, false);
        }
        let returns = self.block(body);
        self.scopes.pop();
        returns
    }

    fn block(&mut self, body: &'a [Stmt]) -> bool {
        let mut returns = false;
        for statement in body {
            match statement {
                Stmt::Let {
                    name,
                    expr,
                    mutable,
                } => {
                    let mut ty = self.expr(expr, None);
                    if ty == BodyType::Void {
                        self.report("B108", "cannot bind an expression with no value".into());
                        ty = BodyType::Unknown;
                    }
                    self.bind(name, ty, *mutable);
                }
                Stmt::Assign { name, expr } => {
                    let binding = self.lookup(name);
                    let actual = self.expr(expr, binding.map(|binding| binding.ty));
                    match binding {
                        None => self
                            .report("B100", format!("assignment to undefined variable `{name}`")),
                        Some(binding) => {
                            if !binding.mutable {
                                self.report(
                                    "B110",
                                    format!("cannot assign to readonly binding `{name}`"),
                                );
                            }
                            if actual != BodyType::Unknown
                                && binding.ty != BodyType::Unknown
                                && actual != binding.ty
                            {
                                self.report(
                                    "B107",
                                    format!(
                                        "assignment to `{name}` expected {}, got {}",
                                        binding.ty.description(),
                                        actual.description()
                                    ),
                                );
                            }
                        }
                    }
                }
                Stmt::Return(expr) => {
                    let expected = self
                        .operation
                        .returns
                        .as_ref()
                        .map(BodyType::declared)
                        .unwrap_or(BodyType::Void);
                    let actual = self.expr(expr, Some(expected));
                    self.require(actual, expected, "B102");
                    returns = true;
                }
                Stmt::If { cond, then, else_ } => {
                    self.condition(cond);
                    let then_returns = self.nested_block(then, None);
                    let else_returns = self.nested_block(else_, None);
                    returns |= then_returns && else_returns;
                }
                Stmt::While { cond, body } => {
                    self.condition(cond);
                    self.loop_depth += 1;
                    self.nested_block(body, None);
                    self.loop_depth -= 1;
                    returns |= *cond == Expr::Bool(true) && !breaks_out(body);
                }
                Stmt::For { var, iter, body } => {
                    let ty = self.expr(iter, None);
                    let element = ty.element().unwrap_or_else(|| {
                        if ty != BodyType::Unknown {
                            self.report("B109", "for requires a Vec iterable".into());
                        }
                        BodyType::Unknown
                    });
                    self.loop_depth += 1;
                    self.nested_block(body, Some((var, element)));
                    self.loop_depth -= 1;
                }
                Stmt::Break | Stmt::Continue => {
                    if self.loop_depth == 0 {
                        self.report("B111", "loop control requires an enclosing loop".into());
                    }
                }
                // Explicit `unsafe:` scope: type/borrow checks still apply to
                // every nested statement; only UnsafeMemory is discharged,
                // and that happens in `check_operation_effects`, not here.
                Stmt::Unsafe { body } => {
                    returns |= self.nested_block(body, None);
                }
                Stmt::ExprStmt(expr) => {
                    self.expr(expr, None);
                }
            }
        }
        returns
    }

    fn condition(&mut self, expr: &'a Expr) {
        let actual = self.expr(expr, Some(BodyType::Named("bool")));
        self.require(actual, BodyType::Named("bool"), "B103");
    }

    /// Only nonliteral evidence supplies a peer's context. This does not
    /// diagnose or execute expressions, and never guesses a variable's type.
    /// Numeric intrinsics recurse into their value operands (never the
    /// `bits_as` target name) so nested calls preserve width:
    /// `wrapping_add(1, wrapping_mul(u8(10), u8(2)))` infers `u8`.
    fn hint(&self, expr: &'a Expr) -> Option<BodyType<'a>> {
        match expr {
            Expr::Var(name) => self.lookup(name).map(|binding| binding.ty),
            Expr::Call { name, args } if name == "bits_as" => match args.first() {
                Some(Expr::Var(target)) if int_bit_width(target).is_some() => {
                    Some(BodyType::Named(match target.as_str() {
                        "i8" => "i8",
                        "i16" => "i16",
                        "i32" => "i32",
                        "i64" => "i64",
                        "isize" => "isize",
                        "u8" => "u8",
                        "u16" => "u16",
                        "u32" => "u32",
                        "u64" => "u64",
                        _ => "usize",
                    }))
                }
                _ => None,
            },
            Expr::Call { name, args }
                if name == "bit_not" || name == "shift_left" || name == "shift_right" =>
            {
                args.first().and_then(|operand| self.hint(operand))
            }
            Expr::Call { name, args }
                if matches!(
                    name.as_str(),
                    "wrapping_add"
                        | "wrapping_sub"
                        | "wrapping_mul"
                        | "bit_and"
                        | "bit_or"
                        | "bit_xor"
                ) =>
            {
                match args.as_slice() {
                    [first, second] => self
                        .hint(first)
                        .filter(|ty| ty.integer())
                        .or_else(|| self.hint(second).filter(|ty| ty.integer())),
                    _ => None,
                }
            }
            Expr::Call { name, .. } => builtin_signature(name)
                .map(|(_, result)| result)
                .or_else(|| reflection_arity(name).map(|_| BodyType::Named("usize")))
                .or_else(|| {
                    self.ir
                        .entities
                        .get(name)
                        .map(|entity| BodyType::Named(&entity.name))
                })
                .or_else(|| {
                    self.ir.operations.get(name).map(|op| {
                        op.returns
                            .as_ref()
                            .map(BodyType::declared)
                            .unwrap_or(BodyType::Void)
                    })
                }),
            Expr::Field { base, field } => self.hint(base).and_then(|ty| self.field(ty, field)),
            Expr::Index { base, .. } => self.hint(base).and_then(BodyType::element),
            Expr::BinOp {
                op:
                    sal_syntax::BinOp::Add
                    | sal_syntax::BinOp::Sub
                    | sal_syntax::BinOp::Mul
                    | sal_syntax::BinOp::Div
                    | sal_syntax::BinOp::Rem,
                left,
                right,
            } => self.hint(left).or_else(|| self.hint(right)),
            Expr::BinOp { .. } | Expr::Bool(_) | Expr::Not(_) => Some(BodyType::Named("bool")),
            Expr::Float(_) => Some(BodyType::Named("f64")),
            Expr::Lit(_) | Expr::Int(_) => None,
        }
    }

    fn field(&self, base: BodyType<'a>, name: &str) -> Option<BodyType<'a>> {
        // `ValueResult<T>` is a plain value record shared by collection
        // accessors: `found: bool` distinguishes missing/out-of-range, and
        // `value: T` carries the payload. It never nests owners.
        if let BodyType::Generic(TypeRef::Generic { name: owner, args }) = base {
            if owner == "ValueResult" && args.len() == 1 {
                return match name {
                    "found" => Some(BodyType::Named("bool")),
                    "value" => Some(BodyType::declared(&args[0])),
                    _ => None,
                };
            }
        }
        let BodyType::Named(entity) = base else {
            return None;
        };
        self.ir
            .entities
            .get(entity)?
            .fields
            .iter()
            .find(|field| field.name == name)
            .map(|field| BodyType::declared(&field.ty))
    }

    fn expr(&mut self, expr: &'a Expr, expected: Option<BodyType<'a>>) -> BodyType<'a> {
        match expr {
            Expr::Lit(value) => match expected {
                Some(BodyType::Named("Word"))
                    if !value.is_empty() && !value.chars().any(char::is_whitespace) =>
                {
                    BodyType::Named("Word")
                }
                Some(BodyType::Named("Character")) if value.chars().count() == 1 => {
                    BodyType::Named("Character")
                }
                _ => BodyType::Named("Text"),
            },
            Expr::Int(value) => expected
                .filter(|ty| integer_literal_fits(*value, *ty))
                .unwrap_or(BodyType::Named("i64")),
            Expr::Float(_) => BodyType::Named("f64"),
            Expr::Bool(_) => BodyType::Named("bool"),
            Expr::Not(value) => {
                let actual = self.expr(value, Some(BodyType::Named("bool")));
                self.require(actual, BodyType::Named("bool"), "B105");
                BodyType::Named("bool")
            }
            Expr::Var(name) => self
                .lookup(name)
                .map(|binding| binding.ty)
                .unwrap_or_else(|| {
                    self.report("B100", format!("undefined variable `{name}`"));
                    BodyType::Unknown
                }),
            Expr::Call { name, args } => self.call(name, args, expected),
            Expr::Field { base, field } => {
                let base = self.expr(base, None);
                self.field(base, field).unwrap_or_else(|| {
                    if base != BodyType::Unknown {
                        self.report(
                            "B109",
                            format!("{} has no field `{field}`", base.description()),
                        );
                    }
                    BodyType::Unknown
                })
            }
            Expr::Index { base, index } => {
                let base = self.expr(base, None);
                let index = self.expr(index, Some(BodyType::Named("usize")));
                self.require(index, BodyType::Named("usize"), "B109");
                base.element().unwrap_or_else(|| {
                    if base != BodyType::Unknown {
                        self.report(
                            "B109",
                            "indexing requires a Vec; Text is not byte-indexable".into(),
                        );
                    }
                    BodyType::Unknown
                })
            }
            Expr::BinOp { op, left, right } => {
                use sal_syntax::BinOp;
                if matches!(op, BinOp::And | BinOp::Or) {
                    let boolean = BodyType::Named("bool");
                    let left = self.expr(left, Some(boolean));
                    let right = self.expr(right, Some(boolean));
                    self.require(left, boolean, "B105");
                    self.require(right, boolean, "B105");
                    return boolean;
                }
                let integer_arithmetic = matches!(op, BinOp::Mul | BinOp::Div | BinOp::Rem);
                let arithmetic = integer_arithmetic || matches!(op, BinOp::Add | BinOp::Sub);
                let ordering = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
                let context = if arithmetic {
                    expected.filter(|ty| ty.numeric())
                } else {
                    None
                }
                .or_else(|| self.hint(left))
                .or_else(|| self.hint(right));
                let left = self.expr(left, context);
                let right = self.expr(right, context.or(Some(left)));
                if left == BodyType::Unknown || right == BodyType::Unknown {
                    return BodyType::Unknown;
                }
                let supported = if integer_arithmetic {
                    left.integer()
                } else if arithmetic || ordering {
                    left.numeric()
                } else {
                    left.numeric()
                        || matches!(
                            left,
                            BodyType::Named("bool" | "Text" | "Bytes" | "Word" | "Character")
                        )
                };
                if left != right || !supported {
                    self.report(
                        "B105",
                        format!(
                            "operator {op:?} does not support {} and {}",
                            left.description(),
                            right.description(),
                        ),
                    );
                    BodyType::Unknown
                } else if arithmetic {
                    left
                } else {
                    BodyType::Named("bool")
                }
            }
        }
    }

    fn call(
        &mut self,
        name: &str,
        args: &'a [Expr],
        expected: Option<BodyType<'a>>,
    ) -> BodyType<'a> {
        if name == "operation_address" {
            let [Expr::Var(name)] = args else {
                self.report(
                    "B108",
                    "operation_address requires one operation name".into(),
                );
                return BodyType::Unknown;
            };
            let valid = self.ir.operations.get(name).is_some_and(|operation| {
                operation.c_import.is_none()
                    && operation.accepts.len() == 1
                    && operation.accepts[0].ty == TypeRef::Named("usize".into())
                    && operation.returns == Some(TypeRef::Named("i64".into()))
            });
            if !valid {
                self.report(
                    "B108",
                    "operation_address requires SAL (usize) -> i64".into(),
                );
            }
            return BodyType::Named("usize");
        }
        if let Some(arity) = reflection_arity(name) {
            return self.reflection(name, args, arity);
        }
        if is_numeric_intrinsic(name) {
            return self.numeric_intrinsic(name, args, expected);
        }
        // Opaque owners are never forged by calls: `Buffer(...)`,
        // `MutBytes(...)`, `Vector(...)`, `Map(...)`, `Borrow(...)`, and
        // `ValueResult(...)` have dedicated constructors/accessors only.
        // Fail closed with B108 (not the generic B101 unknown-call path).
        if matches!(
            name,
            "Buffer" | "MutBytes" | "Vector" | "Map" | "Borrow" | "ValueResult"
        ) {
            for arg in args {
                self.expr(arg, None);
            }
            self.report(
                "B108",
                format!("call `{name}` cannot forge an opaque owner or result record"),
            );
            return BodyType::Unknown;
        }
        // Opaque owners/spans never convert: `usize(owner)`, `u8(span)`,
        // and the other checked casts reject owned handles (B108).
        if matches!(
            name,
            "usize" | "i64" | "u8" | "i8" | "i16" | "i32" | "isize" | "u16" | "u32" | "u64"
        ) && args.len() == 1
        {
            let actual = self.expr(args.first().expect("checked arity"), None);
            if !actual.integer()
                && actual != BodyType::Unknown
                && !matches!(actual, BodyType::Named("f32" | "f64"))
                && matches!(
                    actual,
                    BodyType::Named("Buffer" | "MutBytes" | "Bytes" | "Text")
                        | BodyType::Generic(_)
                )
            {
                self.report(
                    "B108",
                    format!(
                        "call `{name}` requires an integer source, got {}",
                        actual.description()
                    ),
                );
                return BodyType::Named(match name {
                    "usize" => "usize",
                    "i64" => "i64",
                    "u8" => "u8",
                    "i8" => "i8",
                    "i16" => "i16",
                    "i32" => "i32",
                    "isize" => "isize",
                    "u16" => "u16",
                    "u32" => "u32",
                    _ => "u64",
                });
            }
            // Fall through to the generic checked-cast path below, which
            // types integer/float sources and reports B108 otherwise.
        }
        // `byte` reads both immutable views and exclusive writable spans.
        if name == "byte" && args.len() == 2 {
            let base = self.expr(&args[0], None);
            if !matches!(
                base,
                BodyType::Named("Bytes" | "MutBytes") | BodyType::Unknown
            ) && base != BodyType::Unknown
            {
                self.report(
                    "B107",
                    format!("expected Bytes, got {}", base.description()),
                );
            }
            let index = self.expr(&args[1], Some(BodyType::Named("usize")));
            self.require(index, BodyType::Named("usize"), "B107");
            return BodyType::Named("u8");
        }
        // `len` covers caller loans and typed owners as well as the legacy
        // Text/Word/Bytes/Vec surface.
        if name == "len" && args.len() == 1 {
            let actual = self.expr(&args[0], None);
            let valid = matches!(
                actual,
                BodyType::Named("Text" | "Word" | "Bytes" | "Buffer" | "MutBytes")
            ) || actual.element().is_some()
                || matches!(
                    actual,
                    BodyType::Generic(TypeRef::Generic { name, args })
                        if (name == "Vector" || name == "Map" || name == "Borrow") && !args.is_empty()
                )
                || actual == BodyType::Unknown;
            if !valid {
                self.report(
                    "B108",
                    format!(
                        "call `len` argument 1 requires Text, Word, Bytes, Buffer, MutBytes, Vec, or a typed owner, got {}",
                        actual.description()
                    ),
                );
            }
            return BodyType::Named("usize");
        }
        let record = self.ir.entities.get(name);
        let signature = builtin_signature(name);
        let operation = if signature.is_some() || name == "push" {
            None
        } else {
            self.ir.operations.get(name)
        };
        let arity = signature
            .map(|(parameters, _)| parameters.len())
            .or_else(|| (name == "push").then_some(2))
            .or_else(|| operation.map(|op| op.accepts.len()))
            .or_else(|| record.map(|entity| entity.fields.len()));
        match arity {
            None => self.report("B101", format!("unknown operation or builtin `{name}`")),
            Some(expected) if expected != args.len() => self.report(
                "B101",
                format!(
                    "call `{name}` expects {expected} argument(s), got {}",
                    args.len()
                ),
            ),
            Some(_) => {}
        }
        for (index, arg) in args.iter().enumerate() {
            let rule = signature.and_then(|(parameters, _)| parameters.get(index));
            let expected = match rule {
                Some(BuiltinArg::Exact(ty)) => Some(BodyType::Named(ty)),
                _ => operation
                    .and_then(|op| op.accepts.get(index))
                    .map(|param| BodyType::declared(&param.ty))
                    .or_else(|| {
                        record
                            .and_then(|entity| entity.fields.get(index))
                            .map(|field| BodyType::declared(&field.ty))
                    }),
            };
            let actual = self.expr(arg, expected);
            if let Some(expected) = expected {
                self.require(actual, expected, "B107");
            } else if let Some(rule) = rule {
                let (valid, description) = match rule {
                    BuiltinArg::Span => (
                        matches!(actual, BodyType::Named("Text" | "Bytes" | "MutBytes"))
                            || matches!(actual, BodyType::Named(ty)
                                if self.ir.entities.get(ty).is_some_and(|entity| entity.c_layout)),
                        "Text, Bytes, MutBytes, or a C record",
                    ),
                    BuiltinArg::Length => (
                        matches!(actual, BodyType::Named("Text" | "Word" | "Bytes"))
                            || actual.element().is_some(),
                        "Text, Word, Bytes, or Vec",
                    ),
                    BuiltinArg::Integer => (actual.integer(), "an integer"),
                    BuiltinArg::MachineWord => (
                        matches!(
                            actual,
                            BodyType::Named("i64" | "u64" | "usize" | "isize" | "u8")
                        ),
                        "a machineword integer (i64, u64, usize, isize, or u8)",
                    ),
                    BuiltinArg::Exact(_) => unreachable!("exact arguments have an expected type"),
                };
                // Checked owner/span loans (Buffer/MutBytes/typed owners) flow
                // to the compiler owner's memory pass for precise B107/CON203
                // + provenance; this file only enforces arity here, never a
                // blanket B108 on owner-typed arguments. Internal records that
                // hold views are loan holders there too, so `borrow_end` of
                // such a record is the memory pass's to validate.
                let deferred = is_memory_builtin(name)
                    && (matches!(
                        actual,
                        BodyType::Named("Buffer" | "MutBytes" | "Bytes" | "Text")
                            | BodyType::Generic(_)
                    ) || (name == "borrow"
                        && matches!(actual, BodyType::Named(record) if self.ir.entities.contains_key(record)))
                        || (name == "borrow_end"
                            && matches!(actual, BodyType::Named(record)
                                if memory::record_carries_views(&self.ir.entities, record))));
                if !valid && actual != BodyType::Unknown && !deferred {
                    self.report(
                        "B108",
                        format!(
                            "call `{name}` argument {} requires {description}, got {}",
                            index + 1,
                            actual.description()
                        ),
                    );
                }
            }
        }
        if name == "push" {
            self.report(
                "B108",
                "push requires mutable collections, which are not supported".into(),
            );
            return BodyType::Unknown;
        }
        signature
            .filter(|(parameters, _)| parameters.len() == args.len())
            .map(|(_, result)| result)
            .or_else(|| {
                operation.map(|op| {
                    op.returns
                        .as_ref()
                        .map(BodyType::declared)
                        .unwrap_or(BodyType::Void)
                })
            })
            .or_else(|| record.map(|entity| BodyType::Named(&entity.name)))
            .unwrap_or(BodyType::Unknown)
    }

    fn reflection(&mut self, name: &str, args: &'a [Expr], arity: usize) -> BodyType<'a> {
        if args.len() != arity {
            self.report(
                "B108",
                format!("`{name}` expects {arity} compile-time operand(s)"),
            );
            return BodyType::Unknown;
        }
        let Some(Expr::Var(ty)) = args.first() else {
            self.report("B108", format!("`{name}` requires a C record type name"));
            return BodyType::Unknown;
        };
        let Some(record) = self.ir.entities.get(ty).filter(|entity| entity.c_layout) else {
            self.report(
                "B108",
                format!("`{name}` requires a C record type, got `{ty}`"),
            );
            return BodyType::Unknown;
        };
        if name == "offset_of" {
            let Expr::Lit(field) = &args[1] else {
                self.report("B108", "`offset_of` requires a literal field name".into());
                return BodyType::Unknown;
            };
            if !record
                .fields
                .iter()
                .any(|candidate| candidate.name == *field)
            {
                self.report("B108", format!("C record `{ty}` has no field `{field}`"));
                return BodyType::Unknown;
            }
        }
        BodyType::Named("usize")
    }

    /// Integer type context for one value operand: the operand's own hint
    /// first, then the peer's hint, then the call-site expectation. Mirrors
    /// the checked `+`/`-` propagation without ever silently converting a
    /// variable's type: `expected` only types otherwise-untyped literals.
    fn integer_context(
        &self,
        operand: &'a Expr,
        peer: Option<&'a Expr>,
        expected: Option<BodyType<'a>>,
    ) -> Option<BodyType<'a>> {
        self.hint(operand)
            .filter(|ty| ty.integer())
            .or_else(|| {
                peer.and_then(|peer| self.hint(peer))
                    .filter(|ty| ty.integer())
            })
            .or_else(|| expected.filter(|ty| ty.integer()))
    }

    fn integer_operand(
        &mut self,
        name: &str,
        operand: &'a Expr,
        context: Option<BodyType<'a>>,
    ) -> BodyType<'a> {
        let actual = self.expr(operand, context);
        if actual != BodyType::Unknown && !actual.integer() {
            self.report(
                "B107",
                format!(
                    "call `{name}` requires integer types, got {}",
                    actual.description()
                ),
            );
            return BodyType::Unknown;
        }
        actual
    }

    /// Pure machine-integer boundaries: exact-typed operands, no implicit
    /// conversion, unsuffixed-literal contextual inference (operand hint,
    /// then peer hint, then the call-site expectation). Nested intrinsic
    /// result hints preserve width, so `returns u8` on
    /// `wrapping_add(250, 10)` yields 4 and
    /// `wrapping_add(1, wrapping_mul(u8(10), u8(2)))` yields 21 at runtime.
    /// Shifts take a `usize` count; the width guard stays a native runtime
    /// trap owned by the numeric lowerer. Pure: no effect entries.
    fn numeric_intrinsic(
        &mut self,
        name: &str,
        args: &'a [Expr],
        expected: Option<BodyType<'a>>,
    ) -> BodyType<'a> {
        if name == "bits_as" {
            if args.len() != 2 {
                self.report(
                    "B101",
                    format!("call `{name}` expects 2 argument(s), got {}", args.len()),
                );
                return BodyType::Unknown;
            }
            let target = match &args[0] {
                Expr::Var(target) if int_bit_width(target).is_some() => target.as_str(),
                Expr::Var(target) => {
                    self.report(
                        "B108",
                        format!("`bits_as` target requires an integer type name, got `{target}`"),
                    );
                    return BodyType::Unknown;
                }
                _ => {
                    self.report(
                        "B108",
                        "`bits_as` target must be a compile-time integer type name".into(),
                    );
                    return BodyType::Unknown;
                }
            };
            let width = int_bit_width(target).expect("checked target");
            let result = BodyType::Named(match target {
                "i8" => "i8",
                "i16" => "i16",
                "i32" => "i32",
                "i64" => "i64",
                "isize" => "isize",
                "u8" => "u8",
                "u16" => "u16",
                "u32" => "u32",
                "u64" => "u64",
                _ => "usize",
            });
            let value = self.expr(&args[1], Some(result));
            let same = match value {
                BodyType::Named(found) => int_bit_width(found) == Some(width),
                BodyType::Unknown => true,
                _ => false,
            };
            if !same {
                self.report(
                    "B107",
                    format!(
                        "`bits_as` requires the same bit width as `{target}`, got {}",
                        value.description()
                    ),
                );
                return BodyType::Unknown;
            }
            if value == BodyType::Unknown {
                return BodyType::Unknown;
            }
            return result;
        }
        if name == "bit_not" {
            if args.len() != 1 {
                self.report(
                    "B101",
                    format!("call `{name}` expects 1 argument(s), got {}", args.len()),
                );
                return BodyType::Unknown;
            }
            // Unary result hint: the operand's own type first, then the
            // call-site expectation (literals only; typed vars never convert).
            let context = self.integer_context(&args[0], None, expected);
            return self.integer_operand(name, &args[0], context);
        }
        if name == "shift_left" || name == "shift_right" {
            if args.len() != 2 {
                self.report(
                    "B101",
                    format!("call `{name}` expects 2 argument(s), got {}", args.len()),
                );
                return BodyType::Unknown;
            }
            let context = self.integer_context(&args[0], None, expected);
            let value = self.integer_operand(name, &args[0], context);
            if value == BodyType::Unknown {
                self.expr(&args[1], Some(BodyType::Named("usize")));
                return BodyType::Unknown;
            }
            let count = self.expr(&args[1], Some(BodyType::Named("usize")));
            if count != BodyType::Unknown && count != BodyType::Named("usize") {
                self.report(
                    "B107",
                    format!(
                        "call `{name}` shift count requires usize, got {}",
                        count.description()
                    ),
                );
                return BodyType::Unknown;
            }
            return value;
        }
        // Binary wrapping/bitwise: same-width T for both operands. Literals
        // take the peer's type first; the call-site expectation is only the
        // last resort for otherwise-untyped literals. Explicitly typed
        // operands never silently convert.
        if args.len() != 2 {
            self.report(
                "B101",
                format!("call `{name}` expects 2 argument(s), got {}", args.len()),
            );
            return BodyType::Unknown;
        }
        let context = self.integer_context(&args[0], Some(&args[1]), expected);
        let left = self.integer_operand(name, &args[0], context);
        if left == BodyType::Unknown {
            self.expr(&args[1], None);
            return BodyType::Unknown;
        }
        let right = self.integer_operand(name, &args[1], Some(left));
        if right == BodyType::Unknown {
            return BodyType::Unknown;
        }
        if left != right {
            self.report(
                "B107",
                format!(
                    "call `{name}` requires equal integer types, got {} and {}",
                    left.description(),
                    right.description()
                ),
            );
            return BodyType::Unknown;
        }
        left
    }
}
pub(crate) fn integer_literal_fits(value: i64, ty: BodyType<'_>) -> bool {
    match ty {
        BodyType::Named("i8") => i8::try_from(value).is_ok(),
        BodyType::Named("i16") => i16::try_from(value).is_ok(),
        BodyType::Named("i32") => i32::try_from(value).is_ok(),
        BodyType::Named("i64" | "i128" | "isize") => true,
        BodyType::Named("u8") => u8::try_from(value).is_ok(),
        BodyType::Named("u16") => u16::try_from(value).is_ok(),
        BodyType::Named("u32") => u32::try_from(value).is_ok(),
        BodyType::Named("u64" | "u128" | "usize") => value >= 0,
        _ => false,
    }
}
/// Bit width of a machine integer type name, shared with the compiler
/// owner's same-width checks (`bits_as`, wrapping/bit/shift operands).
/// Returns `None` for non-integers, floats, owners, spans, and handles.
pub(crate) fn int_bit_width(name: &str) -> Option<u32> {
    Some(match name {
        "i8" | "u8" => 8,
        "i16" | "u16" => 16,
        "i32" | "u32" => 32,
        "i64" | "u64" | "isize" | "usize" => 64,
        _ => return None,
    })
}

/// The ten exact pure machine-integer boundary spellings (nine contract
/// intrinsics plus `bits_as`), owned by the native numeric module's header
/// guide; this file only reserves and types them.
pub(crate) fn is_numeric_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "wrapping_add"
            | "wrapping_sub"
            | "wrapping_mul"
            | "bit_and"
            | "bit_or"
            | "bit_xor"
            | "bit_not"
            | "shift_left"
            | "shift_right"
            | "bits_as"
    )
}

/// Checked safe-memory/collection builtins whose owner/span arguments the
/// compiler owner's memory pass types precisely (B107/CON203 + provenance).
/// This file enforces arity (B101) and scalar rules only, and never emits a
/// blanket B108 for owner-typed arguments to these names.
pub(crate) fn is_memory_builtin(name: &str) -> bool {
    matches!(
        name,
        "buffer"
            | "buffer_drop"
            | "borrow_mut"
            | "slice_mut"
            | "view"
            | "put"
            | "borrow_end"
            | "borrow"
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

pub fn check_architecture(ir: &Ir) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (_, service) in sorted_entries(&ir.services) {
        check_membership(
            ir,
            &service.name,
            service.belongs_to.as_deref(),
            &service.span,
            &mut diagnostics,
        );
    }
    let mut owners: HashMap<&str, &str> = HashMap::new();
    for (_, module) in sorted_entries(&ir.modules) {
        check_membership(
            ir,
            &module.name,
            module.belongs_to.as_deref(),
            &module.span,
            &mut diagnostics,
        );
        for resource in &module.owns {
            if let Some(owner) = owners.get(resource.as_str()) {
                if *owner != module.name {
                    diagnostics.push(error(
                        "ARCH106",
                        format!(
                            "resource `{resource}` is owned by both `{owner}` and `{}`",
                            module.name
                        ),
                        &module.span,
                    ));
                }
            } else {
                owners.insert(resource, &module.name);
            }
        }
        let mut conflicts = HashSet::new();
        for resource in &module.cannot_modify {
            if (module.owns.contains(resource) || module.may_modify.contains(resource))
                && conflicts.insert(resource)
            {
                diagnostics.push(error(
                    "ARCH107",
                    format!(
                        "module `{}` both owns/may modify and cannot modify `{resource}`",
                        module.name
                    ),
                    &module.span,
                ));
            }
        }
    }
    for (_, layer) in sorted_entries(&ir.layers) {
        let allowed: HashSet<&str> = layer
            .rules
            .iter()
            .filter_map(|rule| match rule {
                LayerRule::MayDependOn { target, .. } => Some(target.as_str()),
                _ => None,
            })
            .collect();
        let mut conflicts = HashSet::new();
        for rule in &layer.rules {
            match rule {
                LayerRule::Owns { name, span } => {
                    if !ir.entities.contains_key(name)
                        && !ir.services.contains_key(name)
                        && !ir.modules.contains_key(name)
                        && !ir.operations.contains_key(name)
                    {
                        diagnostics.push(error(
                            "ARCH102",
                            format!("layer `{}` owns unknown declaration `{name}`", layer.name),
                            span,
                        ));
                    }
                }
                LayerRule::MayDependOn { target, span }
                | LayerRule::MustNotDependOn { target, span, .. } => {
                    if !ir.layers.contains_key(target) {
                        diagnostics.push(error(
                            "ARCH103",
                            format!("layer `{}` refers to unknown layer `{target}`", layer.name),
                            span,
                        ));
                    }
                    if matches!(rule, LayerRule::MustNotDependOn { .. })
                        && allowed.contains(target.as_str())
                        && conflicts.insert(target)
                    {
                        diagnostics.push(error(
                            "ARCH104",
                            format!(
                                "layer `{}` both may and must not depend on `{target}`",
                                layer.name
                            ),
                            span,
                        ));
                    }
                }
            }
        }
    }
    check_layer_cycles(ir, &mut diagnostics);
    diagnostics
}

pub fn check_effects(ir: &Ir) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for (_, operation) in sorted_entries(&ir.operations) {
        if operation.c_import.is_some() {
            for effect in ["SystemCall", "UnsafeMemory"] {
                if !operation.effects.iter().any(|own| own == effect) {
                    diagnostics.push(error(
                        "EFF203",
                        format!(
                            "C import `{}` must declare effect `{effect}`",
                            operation.name
                        ),
                        &operation.span,
                    ));
                }
            }
        }
        if operation.effects.iter().any(|effect| effect == "Pure")
            && operation.effects.iter().any(|effect| effect != "Pure")
        {
            diagnostics.push(error(
                "EFF202",
                format!(
                    "operation `{}` combines `Pure` with other effects",
                    operation.name
                ),
                &operation.span,
            ));
        }
        check_operation_effects(ir, operation, &mut diagnostics);
    }
    diagnostics
}

fn check_operation_effects(ir: &Ir, operation: &OperationDecl, diagnostics: &mut Vec<Diagnostic>) {
    enum Node<'a> {
        Statement(&'a Stmt),
        EnterUnsafe,
        ExitUnsafe,
        Expression(&'a Expr),
    }
    let mut pending: Vec<_> = operation.body.iter().rev().map(Node::Statement).collect();
    // Lexical `unsafe:` scope: discharges ONLY `UnsafeMemory` for nested
    // raw operations/calls. `SystemCall` and every other effect still
    // propagate normally; type/borrow checks are untouched (see
    // `BodyChecker::block`). No module/name whitelists.
    let mut unsafe_depth: usize = 0;
    while let Some(node) = pending.pop() {
        match node {
            Node::EnterUnsafe => {
                unsafe_depth += 1;
            }
            Node::ExitUnsafe => {
                unsafe_depth = unsafe_depth.saturating_sub(1);
            }
            Node::Statement(statement) => match statement {
                Stmt::Let { expr, .. }
                | Stmt::Assign { expr, .. }
                | Stmt::Return(expr)
                | Stmt::ExprStmt(expr) => pending.push(Node::Expression(expr)),
                Stmt::If { cond, then, else_ } => {
                    pending.extend(else_.iter().rev().map(Node::Statement));
                    pending.extend(then.iter().rev().map(Node::Statement));
                    pending.push(Node::Expression(cond));
                }
                Stmt::While { cond, body } => {
                    pending.extend(body.iter().rev().map(Node::Statement));
                    pending.push(Node::Expression(cond));
                }
                Stmt::For { iter, body, .. } => {
                    pending.extend(body.iter().rev().map(Node::Statement));
                    pending.push(Node::Expression(iter));
                }
                Stmt::Unsafe { body } => {
                    pending.push(Node::ExitUnsafe);
                    pending.extend(body.iter().rev().map(Node::Statement));
                    pending.push(Node::EnterUnsafe);
                }
                Stmt::Break | Stmt::Continue => {}
            },
            Node::Expression(expr) => match expr {
                Expr::Call { name, args } => {
                    let in_unsafe = unsafe_depth > 0;
                    let mut require = |effect: &str| {
                        if effect != "Pure"
                            && !(in_unsafe && effect == "UnsafeMemory")
                            && !operation.effects.iter().any(|own| own == effect)
                        {
                            diagnostics.push(error(
                                "EFF203",
                                format!(
                                    "operation `{}` must declare effect `{effect}` required by call `{name}`",
                                    operation.name
                                ),
                                &operation.span,
                            ));
                        }
                    };
                    for effect in intrinsic_effects(name) {
                        require(effect);
                    }
                    if builtin_signature(name).is_none() && !is_numeric_intrinsic(name) {
                        if let Some(callee) = ir.operations.get(name) {
                            if callee.c_import.is_some() {
                                for effect in ["SystemCall", "UnsafeMemory"] {
                                    require(effect);
                                }
                            }
                            for (index, effect) in callee.effects.iter().enumerate() {
                                if !callee.effects[..index].contains(effect)
                                    && !(callee.c_import.is_some()
                                        && matches!(effect.as_str(), "SystemCall" | "UnsafeMemory"))
                                {
                                    require(effect);
                                }
                            }
                        }
                    }
                    pending.extend(args.iter().rev().map(Node::Expression));
                }
                Expr::Field { base, .. } | Expr::Not(base) => pending.push(Node::Expression(base)),
                Expr::Index { base, index } => {
                    pending.push(Node::Expression(index));
                    pending.push(Node::Expression(base));
                }
                Expr::BinOp { left, right, .. } => {
                    pending.push(Node::Expression(right));
                    pending.push(Node::Expression(left));
                }
                Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
            },
        }
    }
}

/// Executable subset checker (X1xx errors, W1xx warnings). TWO program kinds:
///
/// Server program (any `server` or `route` present): exactly one `server`
/// (X100 missing/duplicate/port/version: port 1..=65535 present,
/// `speaks HTTP/1` required, other versions X101); one or more `route`s
/// (X102 non-GET or missing method, X103 bad path, X104 missing/bad responds:
/// Word-or-Text use (Character rejected here as X105 when the response
/// parameter matches a Character operation parameter); unknown `param NAME`
/// with no matching `:p` segment -> X106. No routes -> X102.
///
/// Console program (no servers AND no routes): exactly one hello-world
/// `operation` (`returns Text` + `responds with "literal"`). Zero hello
/// operations -> X107; more than one operation total -> X108; hello operation
/// returning non-Text or without a literal -> X104 (bad response).
/// Hello-world `operation` inside a SERVER program stays silent (accepted).
/// Only operations with neither a body nor a response literal produce W100.
/// Deterministic order: servers, routes, then operations, each sorted by name.
/// Never panics.
pub fn check_exec(ir: &Ir) -> Vec<Diagnostic> {
    if ir.servers.is_empty() && ir.routes.is_empty() {
        let mut diagnostics = Vec::new();
        check_console(ir, &Span::single(1, 1), &mut diagnostics);
        return diagnostics;
    }
    let mut diagnostics = check_servers(ir);
    for (name, operation) in sorted_entries(&ir.operations) {
        if operation.body.is_empty() && operation.responds_literal.is_none() {
            diagnostics.push(Diagnostic {
                code: "W100",
                severity: Severity::Warning,
                message: format!("operation `{name}` is ignored by the executable backend"),
                span: operation.span.clone(),
                suggestion: None,
            });
        }
    }
    diagnostics
}

/// Validate server declarations without legacy executable warnings or body copies.
pub fn check_server_declarations(file: &SalFile) -> Vec<Diagnostic> {
    check_server_parts(
        file.items
            .iter()
            .filter_map(|item| match item {
                Item::Server(server) => Some((&server.name, server)),
                _ => None,
            })
            .collect(),
        file.items
            .iter()
            .filter_map(|item| match item {
                Item::Route(route) => Some((&route.name, route)),
                _ => None,
            })
            .collect(),
        file.items.iter().filter_map(|item| match item {
            Item::Operation(operation) => Some(operation),
            _ => None,
        }),
    )
}

pub fn check_servers(ir: &Ir) -> Vec<Diagnostic> {
    check_server_parts(
        ir.servers.iter().collect(),
        ir.routes.iter().collect(),
        ir.operations.values(),
    )
}

fn check_server_parts<'a>(
    mut servers: Vec<(&String, &ServerDecl)>,
    mut routes: Vec<(&String, &RouteDecl)>,
    operations: impl Iterator<Item = &'a OperationDecl> + Clone,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let fallback_span = Span::single(1, 1);
    servers.sort_unstable_by(|left, right| left.0.cmp(right.0));
    routes.sort_unstable_by(|left, right| left.0.cmp(right.0));
    if servers.is_empty() {
        diagnostics.push(error(
            "X100",
            "executable requires exactly one server".into(),
            &fallback_span,
        ));
    }
    for (index, (name, server)) in servers.iter().enumerate() {
        if index > 0 {
            diagnostics.push(error(
                "X100",
                format!("additional server `{name}`; executable requires exactly one server"),
                &server.span,
            ));
        }
        if server.port.is_none_or(|port| port == 0) {
            diagnostics.push(error(
                "X100",
                format!("server `{name}` requires a port in 1..=65535"),
                &server.span,
            ));
        }
        match server.http_version.as_deref() {
            None => diagnostics.push(error(
                "X100",
                format!("server `{name}` requires `speaks HTTP/1`"),
                &server.span,
            )),
            Some("HTTP/1") => {}
            Some(version) => diagnostics.push(error(
                "X101",
                format!("server `{name}` has unsupported HTTP version `{version}`"),
                &server.span,
            )),
        }
    }
    if routes.is_empty() {
        let span = servers
            .first()
            .map_or(&fallback_span, |(_, server)| &server.span);
        diagnostics.push(error(
            "X102",
            "executable requires at least one route".into(),
            span,
        ));
    }
    for (name, route) in routes {
        if !matches!(route.method, Some(RouteMethod::Get)) {
            diagnostics.push(error(
                "X102",
                format!("route `{name}` requires a GET method"),
                &route.span,
            ));
        }
        if route.path.as_deref().is_none_or(|path| {
            !path.starts_with('/') || path.split('/').any(|segment| segment == ":")
        }) {
            diagnostics.push(error(
                "X103",
                format!(
                    "route `{name}` requires a path starting with `/` and nonempty parameter names"
                ),
                &route.span,
            ));
        }
        let valid_response = match &route.responds {
            Some(RespondsKind::Text | RespondsKind::Literal(_)) => true,
            Some(RespondsKind::Param(param)) => {
                let mut bytes = param.bytes();
                matches!(bytes.next(), Some(b'a'..=b'z' | b'A'..=b'Z' | b'_'))
                    && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            }
            None => false,
        };
        if !valid_response {
            diagnostics.push(error(
                "X104",
                format!("route `{name}` requires a Text, literal, or named parameter response"),
                &route.span,
            ));
        }
        if let Some(RespondsKind::Param(param)) = &route.responds {
            if operations.clone().any(|operation| {
                operation.accepts.iter().any(|accepted| {
                    accepted.name == *param
                        && matches!(&accepted.ty, TypeRef::Named(ty) if ty == "Character")
                })
            }) {
                diagnostics.push(error(
                    "X105",
                    format!("route `{name}` cannot respond with Character parameter `{param}`"),
                    &route.span,
                ));
            }
            if !route.path.as_deref().is_some_and(|path| {
                path.split('/').any(|segment| {
                    segment
                        .strip_prefix(':')
                        .is_some_and(|capture| !capture.is_empty() && capture == param)
                })
            }) {
                diagnostics.push(error(
                    "X106",
                    format!("route `{name}` responds with unknown path parameter `{param}`"),
                    &route.span,
                ));
            }
        }
    }
    diagnostics
}

/// Console-program gate: no servers/routes, exactly one hello-world operation.
fn check_console(ir: &Ir, fallback: &Span, diagnostics: &mut Vec<Diagnostic>) {
    let operations = sorted_entries(&ir.operations);
    let hello: Vec<(&String, &OperationDecl)> = operations
        .iter()
        .filter(|(_, operation)| {
            matches!(&operation.returns, Some(TypeRef::Named(ty)) if ty == "Text")
                && (operation.responds_literal.is_some() || has_text_return(operation))
        })
        .map(|(name, operation)| (*name, *operation))
        .collect();
    if hello.is_empty() {
        diagnostics.push(error(
            "X107",
            "console program requires exactly one hello-world operation".into(),
            fallback,
        ));
        return;
    }
    if operations.len() > 1 {
        diagnostics.push(error(
            "X108",
            "console program allows exactly one operation".into(),
            &operations[1].1.span,
        ));
    }
    for (name, operation) in &operations {
        if operation.body.is_empty() && operation.responds_literal.is_none() {
            diagnostics.push(Diagnostic {
                code: "W100",
                severity: Severity::Warning,
                message: format!("operation `{name}` is ignored by the executable backend"),
                span: operation.span.clone(),
                suggestion: None,
            });
        }
    }
}

/// Whether a `break` in `body` exits the loop that directly owns `body`.
/// Breaks inside nested loops target those loops instead.
fn breaks_out(body: &[Stmt]) -> bool {
    body.iter().any(|statement| match statement {
        Stmt::Break => true,
        Stmt::If { then, else_, .. } => breaks_out(then) || breaks_out(else_),
        Stmt::Unsafe { body } => breaks_out(body),
        _ => false,
    })
}

/// Body-form hello: any `return` of a Text literal or Text-typed value.
/// Conservative: literal always counts; variable counts (type proven by B-check).
fn has_text_return(operation: &OperationDecl) -> bool {
    fn block_returns(body: &[sal_syntax::Stmt]) -> bool {
        body.iter().any(|stmt| match stmt {
            sal_syntax::Stmt::Return(sal_syntax::Expr::Lit(_))
            | sal_syntax::Stmt::Return(sal_syntax::Expr::Var(_)) => true,
            sal_syntax::Stmt::If { then, else_, .. } => block_returns(then) || block_returns(else_),
            sal_syntax::Stmt::Unsafe { body } => block_returns(body),
            _ => false,
        })
    }
    block_returns(&operation.body)
}

pub fn verify_rust_imports(ir: &Ir, files: &[RustFile]) -> Vec<Diagnostic> {
    const CAPABILITIES: &[(&str, &[&str])] = &[
        (
            "DatabaseAccess",
            &[
                "sqlx", "postgres", "diesel", "rusqlite", "sea_orm", "mongodb", "redis",
            ],
        ),
        (
            "HTTPAccess",
            &["reqwest", "hyper", "axum", "actix_web", "tower_http"],
        ),
    ];
    let mut diagnostics = Vec::new();
    let layers = sorted_entries(&ir.layers);
    for file in files {
        let Some(span) = declaration_span(ir, &file.module) else {
            diagnostics.push(error(
                "ARCH201",
                format!("Rust file refers to unknown module `{}`", file.module),
                &Span::single(1, 1),
            ));
            continue;
        };
        let own_layer = layer_of(ir, &file.module);
        if own_layer.is_none() {
            diagnostics.push(Diagnostic {
                code: "ARCH202",
                severity: Severity::Warning,
                message: format!("cannot determine layer for module `{}`", file.module),
                span: span.clone(),
                suggestion: None,
            });
        }
        let module = ir.modules.get(&file.module);
        for import in &file.imports {
            let path = import.to_ascii_lowercase();
            let first = path.split("::").find(|segment| !segment.is_empty());
            if let (Some(own), Some(first)) = (own_layer.as_deref(), first) {
                if let Some((target, _)) = layers
                    .iter()
                    .find(|(name, _)| name.eq_ignore_ascii_case(first))
                {
                    let permitted = own.eq_ignore_ascii_case(target)
                        || ir.layers.get(own).is_some_and(|layer| {
                            layer.rules.iter().any(|rule| {
                                matches!(
                                    rule,
                                    LayerRule::MayDependOn { target: allowed, .. }
                                        if allowed == *target
                                )
                            })
                        });
                    if !permitted {
                        diagnostics.push(error(
                            "ARCH001",
                            format!(
                                "module `{}` in layer `{own}` imports `{import}` without a may-depend edge to `{target}`",
                                file.module
                            ),
                            span,
                        ));
                    }
                }
            }
            if let Some(module) = module {
                for (capability, crates) in CAPABILITIES {
                    if module
                        .forbids
                        .iter()
                        .any(|forbidden| forbidden.eq_ignore_ascii_case(capability))
                        && path
                            .split("::")
                            .any(|segment| crates.iter().any(|name| segment.contains(*name)))
                    {
                        diagnostics.push(error(
                            "ARCH301",
                            format!(
                                "module `{}` forbids `{capability}` but imports `{import}`",
                                file.module
                            ),
                            span,
                        ));
                    }
                }
            }
        }
    }
    diagnostics
}

pub fn layer_of(ir: &Ir, module: &str) -> Option<String> {
    if let Some(service) = ir.services.get(module) {
        return service.belongs_to.clone();
    }
    if let Some(module) = ir.modules.get(module) {
        return module.belongs_to.clone();
    }
    if ir.entities.contains_key(module) {
        return ir
            .layers
            .values()
            .filter(|layer| {
                layer
                    .rules
                    .iter()
                    .any(|rule| matches!(rule, LayerRule::Owns { name, .. } if name == module))
            })
            .min_by(|left, right| left.name.cmp(&right.name))
            .map(|layer| layer.name.clone());
    }
    None
}

fn item_identity(item: &Item) -> (&str, &Span) {
    match item {
        Item::Application { name, span } => (name, span),
        Item::Use { path, span } => (path, span),
        Item::Entity(value) => (&value.name, &value.span),
        Item::Enum(value) => (&value.name, &value.span),
        Item::Layer(value) => (&value.name, &value.span),
        Item::Service(value) => (&value.name, &value.span),
        Item::Operation(value) => (&value.name, &value.span),
        Item::Module(value) => (&value.name, &value.span),
        Item::Server(value) => (&value.name, &value.span),
        Item::Route(value) => (&value.name, &value.span),
    }
}

fn sorted_entries<T>(map: &HashMap<String, T>) -> Vec<(&String, &T)> {
    let mut entries: Vec<_> = map.iter().collect();
    entries.sort_unstable_by(|left, right| left.0.cmp(right.0));
    entries
}

fn error(code: &'static str, message: String, span: &Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span: span.clone(),
        suggestion: None,
    }
}

fn is_primitive(name: &str) -> bool {
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
    )
}

fn check_type(ir: &Ir, ty: &TypeRef, span: &Span, diagnostics: &mut Vec<Diagnostic>) {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        match ty {
            TypeRef::Named(name) => {
                let primitive = is_primitive(name);
                if !primitive && !ir.entities.contains_key(name) && !ir.enums.contains_key(name) {
                    diagnostics.push(error("E2001", format!("unknown type `{name}`"), span));
                }
            }
            TypeRef::Generic { name, args } => {
                let arity = match name.as_str() {
                    "Option" | "Vec" | "Money" | "Borrow" | "Vector" | "ValueResult" => Some(1),
                    "Result" | "Map" => Some(2),
                    _ => None,
                };
                if let Some(arity) = arity {
                    if args.len() != arity {
                        diagnostics.push(error(
                            "E2004",
                            format!(
                                "type `{name}` expects {arity} argument(s), found {}",
                                args.len()
                            ),
                            span,
                        ));
                    }
                } else {
                    diagnostics.push(error(
                        "E2002",
                        format!("unknown generic type `{name}`"),
                        span,
                    ));
                }
                if name == "Money" {
                    if let Some(currency) = args.first() {
                        let valid = matches!(
                            currency,
                            TypeRef::Named(code)
                                if code.len() == 3 && code.bytes().all(|byte| byte.is_ascii_uppercase())
                        );
                        if !valid {
                            diagnostics.push(error(
                                "E2003",
                                "Money currency must be exactly three uppercase ASCII letters"
                                    .into(),
                                span,
                            ));
                        }
                    }
                    // A currency name is a literal, not an entity/enum reference.
                    for (index, arg) in args.iter().enumerate().rev() {
                        if index != 0 || matches!(arg, TypeRef::Generic { .. }) {
                            pending.push(arg);
                        }
                    }
                } else {
                    pending.extend(args.iter().rev());
                }
            }
        }
    }
}

fn check_membership(
    ir: &Ir,
    name: &str,
    layer: Option<&str>,
    span: &Span,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let Some(layer) = layer {
        if !ir.layers.contains_key(layer) {
            diagnostics.push(error(
                "ARCH101",
                format!("`{name}` belongs to unknown layer `{layer}`"),
                span,
            ));
        }
    }
}

fn check_layer_cycles(ir: &Ir, diagnostics: &mut Vec<Diagnostic>) {
    let mut finished: HashSet<&str> = HashSet::new();
    let mut active: HashMap<&str, usize> = HashMap::new();
    for (name, layer) in sorted_entries(&ir.layers) {
        if finished.contains(name.as_str()) {
            continue;
        }
        let mut stack = vec![(name.as_str(), layer.rules.iter())];
        active.insert(name, 0);
        while let Some((name, rules)) = stack.last_mut() {
            let Some(rule) = rules.next() else {
                finished.insert(*name);
                active.remove(*name);
                stack.pop();
                continue;
            };
            let LayerRule::MayDependOn { target, span } = rule else {
                continue;
            };
            let Some(next_layer) = ir.layers.get(target) else {
                continue;
            };
            if let Some(start) = active.get(target.as_str()) {
                let mut cycle: Vec<_> = stack.iter().skip(*start).map(|(name, _)| *name).collect();
                cycle.push(target);
                diagnostics.push(error(
                    "ARCH105",
                    format!("circular layer dependency: {}", cycle.join(" -> ")),
                    span,
                ));
            } else if !finished.contains(target.as_str()) {
                active.insert(target, stack.len());
                stack.push((target, next_layer.rules.iter()));
            }
        }
    }
}

fn declaration_span<'a>(ir: &'a Ir, name: &str) -> Option<&'a Span> {
    ir.modules
        .get(name)
        .map(|value| &value.span)
        .or_else(|| ir.services.get(name).map(|value| &value.span))
        .or_else(|| ir.entities.get(name).map(|value| &value.span))
        .or_else(|| ir.operations.get(name).map(|value| &value.span))
        .or_else(|| ir.enums.get(name).map(|value| &value.span))
        .or_else(|| ir.layers.get(name).map(|value| &value.span))
        .or_else(|| {
            ir.file.items.iter().find_map(|item| match item {
                Item::Application {
                    name: application,
                    span,
                } if application == name => Some(span),
                _ => None,
            })
        })
}

#[cfg(test)]
mod c_abi_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn parsed(source: &str) -> SalFile {
        let (file, diagnostics) = sal_syntax::parse(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        file
    }

    fn checked_ir(source: &str) -> Ir {
        let (ir, diagnostics) = build(&parsed(source));
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        ir
    }

    /// Body checks for sources the ownership pass rejects too; those
    /// diagnostics are asserted where ownership is the subject.
    fn unchecked_ir(source: &str) -> Ir {
        build(&parsed(source)).0
    }

    fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect()
    }

    #[test]
    fn numeric_intrinsics_type_same_width_integers_with_literal_inference() {
        // Positive: contextual literal inference, including the nested-call
        // width preservation (`wrapping_add(1, wrapping_mul(u8(10), u8(2)))`).
        let ir = checked_ir(
            "operation Good:\n  returns u8.\n  body:\n    let a = wrapping_add(250, 10).\n    let b = wrapping_add(1, wrapping_mul(u8(10), u8(2))).\n    let c = bit_and(u8(6), u8(3)).\n    let d = bit_not(u8(6)).\n    let e = shift_left(u8(1), usize(2)).\n    let f = shift_right(u8(4), usize(1)).\n    let g = bits_as(u8, wrapping_add(250, 10)).\n    return g.\n",
        );
        assert!(check_bodies(&ir).is_empty(), "{:?}", check_bodies(&ir));
        assert!(check_effects(&ir).is_empty());
        // Negative: mismatched widths, bad shift count, bad bits_as
        // target/width, and wrong arities.
        for (call, code) in [
            ("wrapping_add(u8(1), usize(2))", "B107"),
            ("wrapping_add(u8(1), 1.5)", "B107"),
            ("wrapping_add(1, true)", "B107"),
            ("bit_not(u8(1), u8(2))", "B101"),
            ("wrapping_add(u8(1))", "B101"),
            ("shift_left(u8(1), u8(2))", "B107"),
            ("shift_left(u8(1))", "B101"),
            ("bits_as(u8, u16(1))", "B107"),
            ("bits_as(u16, u8(1))", "B107"),
            ("bits_as(unknown, u8(1))", "B108"),
            ("bits_as(1, u8(1))", "B108"),
            ("bits_as(u8)", "B101"),
        ] {
            let ir = checked_ir(&format!("operation Bad:\n  body:\n    {call}.\n"));
            assert_eq!(codes(&check_bodies(&ir)), [code], "{call}");
        }
    }

    #[test]
    fn numeric_intrinsics_are_pure_and_reserved() {
        // Pure operations may call numeric intrinsics with no effects.
        let ir = checked_ir(
            "operation Pure:\n  effects: Pure.\n  returns u8.\n  body:\n    return wrapping_add(250, 10).\n",
        );
        assert!(check_bodies(&ir).is_empty(), "{:?}", check_bodies(&ir));
        assert!(check_effects(&ir).is_empty());
        for name in [
            "wrapping_add",
            "wrapping_sub",
            "wrapping_mul",
            "bit_and",
            "bit_or",
            "bit_xor",
            "bit_not",
            "shift_left",
            "shift_right",
            "bits_as",
        ] {
            let (ir, diagnostics) = build(&parsed(&format!("operation {name}:\n  returns i64.\n")));
            assert_eq!(codes(&diagnostics), ["E1003"], "{name}");
            assert!(!ir.operations.contains_key(name));
        }
        for name in [
            "buffer",
            "buffer_drop",
            "borrow_mut",
            "slice_mut",
            "view",
            "put",
            "borrow_end",
            "borrow",
            "Buffer",
            "MutBytes",
            "Borrow",
            "Vector",
            "Map",
            "ValueResult",
        ] {
            let (ir, diagnostics) = build(&parsed(&format!("operation {name}:\n  returns i64.\n")));
            assert_eq!(codes(&diagnostics), ["E1003"], "{name}");
            assert!(!ir.operations.contains_key(name));
        }
    }

    #[test]
    fn safe_memory_surface_types_loans_and_rejects_owner_casts() {
        // Positive: the checked safe-memory SDK surface types cleanly.
        let ir = checked_ir(
            "operation Good:\n  returns i64.\n  effects: SystemCall.\n  body:\n    let arena = buffer(usize(64)).\n    let span = borrow_mut(arena, usize(0), usize(64)).\n    put(span, usize(0), u8(9)).\n    let probe = view(span).\n    let first = byte(probe, usize(0)).\n    let wide = byte(span, usize(0)).\n    let size = len(arena) + len(span) + len(probe).\n    borrow_end(probe).\n    borrow_end(span).\n    buffer_drop(arena).\n    return i64(first) + i64(wide) + i64(size).\n",
        );
        assert!(check_bodies(&ir).is_empty(), "{:?}", check_bodies(&ir));
        // Negative: opaque owners/spans never forge into integers, and
        // `byte` still rejects non-span bases.
        for (call, code) in [
            ("usize(arena)", "B108"),
            ("u8(span)", "B108"),
            ("byte(arena, usize(0))", "B107"),
            ("byte(\"x\", usize(0))", "B107"),
            ("len(1)", "B108"),
        ] {
            let ir = unchecked_ir(&format!(
                "operation Bad:\n  accepts arena of type Buffer.\n  accepts span of type MutBytes.\n  body:\n    {call}.\n"
            ));
            assert_eq!(codes(&check_bodies(&ir)), [code], "{call}");
        }
    }

    #[test]
    fn owner_collection_types_validate_without_e2002() {
        let ir = checked_ir(
            "operation Good:\n  accepts owned of type Buffer.\n  accepts span of type MutBytes.\n  accepts held of type Borrow<Buffer>.\n  accepts items of type Vector<i64>.\n  accepts table of type Map<i64, i64>.\n  accepts found of type ValueResult<i64>.\n  returns i64.\n  effects: SystemCall.\n  body:\n    buffer_drop(owned).\n    vector_drop(items).\n    map_drop(table).\n    return 0.\n",
        );
        assert!(check_types(&ir).is_empty(), "{:?}", check_types(&ir));
        for ty in [
            "Borrow<Buffer, Buffer>",
            "Map<i64>",
            "ValueResult<i64, i64>",
        ] {
            let ir = unchecked_ir(&format!(
                "operation Bad:\n  accepts value of type {ty}.\n  body:\n    return 0.\n"
            ));
            assert_eq!(codes(&check_types(&ir)), ["E2004"], "{ty}");
        }
    }

    #[test]
    fn collection_calls_type_expected_shapes_and_reject_forgeries() {
        // Positive: canonical arities type cleanly; get/pop project
        // `found`/`value` through the ValueResult helper.
        let source = format!(
            "{}\noperation Good:\n  accepts items of type Vector<i64>.\n  accepts table of type Map<i64, i64>.\n  returns i64.\n  effects: SystemCall.\n  body:\n    let slot = vector_get(items, usize(0)).\n    let hit = slot.found.\n    let count = vector_len(items) + map_len(table).\n    let present = map_contains(table, 1).\n    vector_drop(items).\n    map_drop(table).\n    if hit && present:\n      return i64(count) + slot.value.\n    return 0.\n",
            include_str!("../../../stdlib/collections.sal")
        );
        let ir = checked_ir(&source);
        assert!(check_bodies(&ir).is_empty(), "{:?}", check_bodies(&ir));
        // Negative: forged owner/result construction and owner->integer
        // casts fail closed; arities still B101.
        for (call, code) in [
            ("Vector(1)", "B108"),
            ("Map(1, 2, 3)", "B108"),
            ("Borrow(items)", "B108"),
            ("ValueResult(true, 1)", "B108"),
            ("Buffer(1)", "B108"),
            ("usize(items)", "B108"),
            ("vector_get(items)", "B101"),
            ("vector_set(items, usize(0))", "B101"),
            ("map_insert(table, 1)", "B101"),
        ] {
            let ir = unchecked_ir(&format!(
                "operation Bad:\n  accepts items of type Vector<i64>.\n  accepts table of type Map<i64, i64>.\n  body:\n    {call}.\n"
            ));
            assert_eq!(codes(&check_bodies(&ir)), [code], "{call}");
        }
        // Generated `SalColl*` names are reserved like intrinsics.
        let (ir, diagnostics) = build(&parsed("operation SalCollHelper:\n  returns i64.\n"));
        assert_eq!(codes(&diagnostics), ["E1003"]);
        assert!(!ir.operations.contains_key("SalCollHelper"));
    }

    #[test]
    fn logical_operands_are_bool_and_unreachable_rhs_is_still_checked() {
        for (expression, expected) in [
            ("1 && true", vec!["B105"]),
            ("false || 1", vec!["B105"]),
            ("!1", vec!["B105"]),
            ("\"a\" && \"b\"", vec!["B105", "B105"]),
            ("false && missing", vec!["B100"]),
            ("true || missing", vec!["B100"]),
            ("!missing", vec!["B100"]),
        ] {
            let ir = checked_ir(&format!("operation Bad:\n  body:\n    {expression}.\n"));
            assert_eq!(codes(&check_bodies(&ir)), expected, "{expression}");
        }
    }

    #[test]
    fn logical_rhs_and_negation_preserve_required_effects() {
        for expression in ["false && Touch()", "true || Touch()", "!Touch()"] {
            let ir = checked_ir(&format!(
                "operation Touch:\n  effects: UnsafeMemory.\n  returns bool.\n  body:\n    return load8(usize(0)) == u8(0).\noperation Caller:\n  returns bool.\n  body:\n    return {expression}.\n"
            ));
            assert!(check_bodies(&ir).is_empty(), "{expression}");
            assert_eq!(codes(&check_effects(&ir)), ["EFF203"], "{expression}");
        }
    }

    #[test]
    fn loop_control_is_lexical_and_does_not_prove_function_return() {
        let ir = checked_ir(
            "operation Control:\n  accepts rows of type Vec<bool>.\n  body:\n    while true:\n      if false:\n        continue.\n      break.\n    for row in rows:\n      if !row:\n        break.\n      continue.\n    break.\n    continue.\noperation MissingReturn:\n  returns i64.\n  body:\n    while true:\n      break.\n",
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B111", "B111", "B106"]);
    }

    fn named(name: &str) -> TypeRef {
        TypeRef::Named(name.into())
    }

    fn executable_ir() -> Ir {
        checked_ir(
            "server TupoiServer:\n  listens on port 8081.\n  speaks HTTP/1.\n\
             route Say:\n  handles GET /say/:what.\n  responds with param what.\n",
        )
    }

    #[test]
    fn unresolved_uses_and_reserved_intrinsics_are_not_registered() {
        let (ir, diagnostics) = build(&parsed(
            "use \"dep.sal\".\nuse \"dep.sal\".\noperation Valid:\n  returns Bytes.\n",
        ));
        assert_eq!(codes(&diagnostics), ["E1002", "E1002"]);
        assert_eq!(ir.operations.len(), 1);
        assert!(check_types(&ir).is_empty());
        for name in [
            "len", "bytes", "byte", "slice", "usize", "i64", "u8", "syscall", "address",
            "bytes_at", "load8", "store8",
        ] {
            let (ir, diagnostics) = build(&parsed(&format!("operation {name}:\n  returns i64.\n")));
            assert_eq!(codes(&diagnostics), ["E1003"], "{name}");
            assert!(!ir.operations.contains_key(name));
        }
    }

    #[test]
    fn assignment_checks_nearest_binding_mutability_and_exact_type() {
        let ir = checked_ir(
            r#"operation Update:
  accepts input of type u8.
  returns u8.
  body:
    let mut value = input.
    set value = 255.
    while value > 0:
      set value = value - 1.
      if true:
        let value = 0.
        set value = 1.
      set value = 2.
    set input = 1.
    set absent = 0.
    set value = 256.
    set value = usize(1).
    return value.
"#,
        );
        let diagnostics = check_bodies(&ir);
        assert_eq!(
            codes(&diagnostics),
            ["B110", "B110", "B100", "B107", "B107"]
        );
        for (diagnostic, name) in diagnostics
            .iter()
            .zip(["value", "input", "absent", "value", "value"])
        {
            assert!(diagnostic.message.contains(&format!("`{name}`")));
        }
        assert!(diagnostics[3].message.contains("expected u8, got i64"));
        assert!(diagnostics[4].message.contains("expected u8, got usize"));
    }

    #[test]
    fn mutable_shadow_does_not_change_outer_binding_mutability_or_type() {
        let ir = checked_ir(
            r#"operation Shadow:
  returns i64.
  body:
    let value = 1.
    if true:
      let mut value = u8(2).
      set value = 255.
    set value = 3.
    return value.
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B110"]);
    }

    #[test]
    fn byte_intrinsics_numeric_context_and_procedure_statements_are_typed() {
        let ir = checked_ir(
            r#"operation Write:
  accepts ptr of type usize.
  accepts value of type u8.
  effects: UnsafeMemory.
  body:
    store8(ptr, value).
operation Main:
  accepts data of type Bytes.
  accepts ptr of type usize.
  returns bool.
  effects: SystemCall, UnsafeMemory.
  body:
    let mut n = byte(data, 0).
    set n = n * 2 / 1 % 255.
    let view = slice(bytes("hello"), 0, len(data)).
    let raw = bytes_at(address(view), usize(i64(len(data)))).
    Write(ptr, u8(i64(load8(ptr)))).
    syscall(1, 1, address(raw), len(raw), 0, 0, 0).
    if n < 255:
      if n <= 1:
        return view == raw.
    while n >= 1:
      set n = n - 1.
    return view != data.
"#,
        );
        for diagnostics in [check_types(&ir), check_bodies(&ir), check_effects(&ir)] {
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
    }

    #[test]
    fn intrinsics_reject_wrong_arity_and_argument_types() {
        for (call, code) in [
            ("len()", "B101"),
            ("bytes()", "B101"),
            ("byte(bytes(\"x\"))", "B101"),
            ("slice(bytes(\"x\"), 0)", "B101"),
            ("usize()", "B101"),
            ("i64(1, 2)", "B101"),
            ("u8()", "B101"),
            ("syscall(1, 0, 0, 0, 0, 0)", "B101"),
            ("syscall(1, 0, 0, 0, 0, 0, 0, 0)", "B101"),
            ("address()", "B101"),
            ("bytes_at(0)", "B101"),
            ("load8()", "B101"),
            ("store8(0)", "B101"),
            ("bytes(bytes(\"x\"))", "B107"),
            ("byte(\"x\", 0)", "B107"),
            ("byte(bytes(\"x\"), i64(0))", "B107"),
            ("slice(bytes(\"x\"), 0, -1)", "B107"),
            ("address(true)", "B108"),
            ("bytes_at(i64(0), 0)", "B107"),
            ("bytes_at(0, i64(0))", "B107"),
            ("load8(i64(0))", "B107"),
            ("store8(0, 256)", "B107"),
            ("store8(0, i64(1))", "B107"),
            ("usize(true)", "B108"),
            ("i64(\"x\")", "B108"),
            ("u8(1.5)", "B108"),
            ("syscall(1, 0, 0, 0, 0, 0, false)", "B108"),
        ] {
            let ir = checked_ir(&format!("operation Bad:\n  body:\n    {call}.\n"));
            assert_eq!(codes(&check_bodies(&ir)), [code], "{call}");
        }
        let ir = checked_ir(
            "operation Bad:\n  accepts wide of type u128.\n  body:\n    syscall(wide, 0, 0, 0, 0, 0, 0).\n",
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B108"]);
    }

    #[test]
    fn void_calls_cannot_be_bound_or_used_as_values() {
        let ir = checked_ir(
            "operation Procedure:\n  body:\n    1.\n\
             operation Bad:\n  returns u8.\n  body:\n    let value = Procedure().\n    let stored = store8(0, 1).\n    return Procedure().\n",
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B108", "B108", "B102"]);
    }

    #[test]
    fn checked_casts_accept_integer_sources_but_not_implicit_variable_conversion() {
        let ir = checked_ir(
            "operation Cast:\n  accepts wide of type u128.\n  returns u8.\n  body:\n    usize(-1).\n    u8(256).\n    i64(wide).\n    return u8(wide).\n",
        );
        // Explicit conversion range failures are runtime traps, not implicit coercions.
        assert!(check_bodies(&ir).is_empty());
        for expression in [
            "u8(1) * usize(2)",
            "1.5 * 2.0",
            "true < false",
            "bytes(\"x\") >= bytes(\"y\")",
        ] {
            let ir = checked_ir(&format!("operation Bad:\n  body:\n    {expression}.\n"));
            assert_eq!(codes(&check_bodies(&ir)), ["B105"], "{expression}");
        }
    }

    #[test]
    fn raw_syscall_requires_both_capabilities_even_with_integer_addresses() {
        for (effects, missing) in [
            ("Pure", vec!["SystemCall", "UnsafeMemory"]),
            ("SystemCall", vec!["UnsafeMemory"]),
            ("UnsafeMemory", vec!["SystemCall"]),
            ("SystemCall, UnsafeMemory", vec![]),
        ] {
            let ir = checked_ir(&format!(
                "operation Raw:\n  effects: {effects}.\n  body:\n    syscall(1, 1, 4096, 1, 0, 0, 0).\n"
            ));
            let diagnostics = check_effects(&ir);
            assert_eq!(codes(&diagnostics), vec!["EFF203"; missing.len()]);
            for (diagnostic, effect) in diagnostics.iter().zip(missing) {
                assert!(diagnostic.message.contains(&format!("`{effect}`")));
            }
        }
    }

    #[test]
    fn effects_are_checked_inside_every_expression_and_statement_position() {
        for statement in [
            "let value = Source().",
            "let mut value = usize(0).\n    set value = Source().",
            "return Source().",
            "if Source() == 0:\n      return 1.",
            "while Source() > 0:\n      return 1.",
            "if true:\n      Source().\n    else:\n      Source().",
            "while true:\n      Source().",
            "for item in items:\n      Source().",
            "for item in Items():\n      1.",
            "usize(Source()).",
            "items[Source()].field.",
            "RecordSource().field.",
            "Source() + 1.",
        ] {
            let ir = checked_ir(&format!(
                "entity Record:\n  has field of type usize.\n\
                 operation Source:\n  effects: DatabaseAccess.\n  returns usize.\n\
                 operation Items:\n  effects: DatabaseAccess.\n  returns Vec<Record>.\n\
                 operation RecordSource:\n  effects: DatabaseAccess.\n  returns Record.\n\
                 operation Caller:\n  accepts items of type Vec<Record>.\n  returns usize.\n  body:\n    {statement}\n    return 0.\n"
            ));
            let diagnostics = check_effects(&ir);
            let count = if statement.contains("else:") { 2 } else { 1 };
            assert_eq!(codes(&diagnostics), vec!["EFF203"; count], "{statement}");
            assert!(diagnostics
                .iter()
                .all(|d| d.message.contains("`DatabaseAccess`")));
        }
        for call in [
            "address(\"x\")",
            "bytes_at(0, 0)",
            "load8(0)",
            "store8(0, 0)",
        ] {
            let ir = checked_ir(&format!(
                "operation Pure:\n  effects: Pure.\n  body:\n    {call}.\n"
            ));
            assert_eq!(codes(&check_effects(&ir)), ["EFF203"], "{call}");
        }
    }

    #[test]
    fn declared_effects_propagate_through_wrappers_and_recursion() {
        let ir = checked_ir(
            "operation Caller:\n  effects: Pure.\n  body:\n    Wrapper().\n\
             operation Wrapper:\n  effects: SystemCall, UnsafeMemory.\n  body:\n    Leaf().\n\
             operation Leaf:\n  effects: SystemCall, UnsafeMemory.\n  body:\n    Wrapper().\n    syscall(1, 0, 0, 0, 0, 0, 0).\n",
        );
        let diagnostics = check_effects(&ir);
        assert_eq!(codes(&diagnostics), ["EFF203", "EFF203"]);
        assert!(diagnostics
            .iter()
            .all(|d| d.message.contains("`Caller`") && d.message.contains("`Wrapper`")));
    }

    #[test]
    fn bodies_preserve_lexical_scopes_and_reject_undefined_values() {
        let ir = checked_ir(
            r#"operation Scope:
  accepts input of type Text.
  accepts items of type Vec<Text>.
  returns Text.
  body:
    let value = value.
    let value = input.
    let input = "duplicate parameter".
    if true:
      let value = "shadow".
      let branch = value.
    else:
      return branch.
    for item in items:
      let inside = item.
    return item.
    return inside.
"#,
        );
        let diagnostics = check_bodies(&ir);
        assert_eq!(
            codes(&diagnostics),
            ["B100", "B104", "B104", "B100", "B100", "B100"]
        );
        for (diagnostic, name) in diagnostics
            .iter()
            .zip(["value", "value", "input", "branch", "item", "inside"])
        {
            assert!(diagnostic.message.contains(&format!("`{name}`")));
            assert_eq!(diagnostic.span.line, 1);
            assert_eq!(diagnostic.severity, Severity::Error);
        }
    }

    #[test]
    fn bodies_reject_wrong_calls_and_unsupported_mutation() {
        let ir = checked_ir(
            r#"operation Calls:
  accepts input of type Text.
  body:
    len(input).
    push(input, "value").
    Target(input).
    len().
    Target().
    Missing(unknown).
    Target(true).
    len(false).
operation Target:
  accepts value of type Text.
"#,
        );
        assert_eq!(
            codes(&check_bodies(&ir)),
            ["B108", "B101", "B101", "B101", "B100", "B107", "B108"]
        );
    }

    #[test]
    fn bodies_visit_undefined_expression_operands_in_source_order() {
        let ir = checked_ir(
            "operation Expressions:\n  body:\n    len(record.field[index] + left - right == first != last).\n",
        );
        let diagnostics = check_bodies(&ir);
        assert_eq!(codes(&diagnostics), ["B100"; 6]);
        for (diagnostic, name) in diagnostics
            .iter()
            .zip(["record", "index", "left", "right", "first", "last"])
        {
            assert_eq!(diagnostic.message, format!("undefined variable `{name}`"));
        }
    }

    #[test]
    fn bodies_reject_return_mismatches_through_bindings_and_calls() {
        let ir = checked_ir(
            r#"operation Flag:
  returns bool.
  body:
    return true.
operation Wrong:
  accepts flag of type bool.
  returns Text.
  body:
    let local = flag.
    return local.
    return Flag().
    return 3.5.
    return -4.
operation WrongScalar:
  accepts value of type u64.
  returns i64.
  body:
    return value.
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B102"; 5]);
    }

    #[test]
    fn bodies_require_boolean_conditions_including_variables_and_calls() {
        let ir = checked_ir(
            r#"operation Conditions:
  returns Text.
  body:
    let flag = "not bool".
    if flag:
      return "bad".
    while Value():
      return "bad".
    if 1 == 2:
      return "ok".
    return "done".
operation Value:
  returns i64.
  body:
    return 1.
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B103", "B103"]);
    }

    #[test]
    fn bodies_accept_nested_calls_shadowing_branches_and_precedence() {
        let ir = checked_ir(
            r#"operation Add:
  accepts value of type u64.
  returns u64.
  body:
    return 1 + value - 1.
operation Choose:
  accepts flag of type bool.
  accepts value of type u64.
  returns u64.
  body:
    let answer = Add(Add(value)).
    if flag:
      let answer = Add(7).
      if answer + 1 == 8:
        return answer.
      else:
        return 0.
    else:
      return answer.
operation Main:
  returns Text.
  body:
    let value = Choose(true, 7).
    if value == 3 + 4:
      return "yes".
    else:
      return "no".
"#,
        );
        assert!(check_types(&ir).is_empty());
        let diagnostics = check_bodies(&ir);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn bodies_require_returns_on_every_path_but_allow_specifications() {
        let ir = checked_ir(
            r#"operation Branch:
  accepts flag of type bool.
  returns Text.
  body:
    if flag:
      return "yes".
    else:
      let value = "fallthrough".
operation Loop:
  returns i64.
  body:
    while true:
      if true:
        break.
operation Forever:
  returns i64.
  body:
    while true:
      let value = 1.
operation Spec:
  accepts value of type Text.
  returns Text.
operation Straight:
  returns Text.
  body:
    let value = "fallthrough".
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B106"; 3]);
    }

    #[test]
    fn bodies_validate_word_character_and_integer_literal_construction() {
        for (ty, literal) in [
            ("Word", r#""""#),
            ("Word", r#""two words""#),
            ("Word", "\"a\u{2003}b\""),
            ("Character", r#""""#),
            ("Character", r#""ab""#),
            ("Character", "\"e\u{301}\""),
            ("u8", "256"),
            ("u64", "-1"),
            ("i8", "-129"),
        ] {
            let source =
                format!("operation Bad:\n  returns {ty}.\n  body:\n    return {literal}.\n");
            assert_eq!(
                codes(&check_bodies(&checked_ir(&source))),
                ["B102"],
                "{source}"
            );
        }
        for (ty, literal) in [
            ("Word", r#""世界""#),
            ("Character", r#""界""#),
            ("Character", r#"" ""#),
            ("u8", "255"),
            ("i8", "-128"),
            ("usize", "0"),
        ] {
            let source =
                format!("operation Good:\n  returns {ty}.\n  body:\n    return {literal}.\n");
            let diagnostics = check_bodies(&checked_ir(&source));
            assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
        }
        let ir = checked_ir(
            r#"operation Bad:
  returns Word.
  body:
    let text = "word".
    NeedsCharacter("ab").
    return text.
operation NeedsCharacter:
  accepts value of type Character.
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B107", "B102"]);
    }

    #[test]
    fn bodies_reject_bad_operators_without_implicit_variable_casts() {
        let ir = checked_ir(
            r#"operation Bad:
  accepts unsigned of type u64.
  returns bool.
  body:
    let signed = 1.
    let bad = signed + unsigned.
    let text = "a" + "b".
    let flag = true - false.
    return "text" == 1.
"#,
        );
        assert_eq!(codes(&check_bodies(&ir)), ["B105"; 4]);
    }

    #[test]
    fn bodies_check_field_index_and_builtin_result_types() {
        let ir = checked_ir(
            r#"entity Record:
  has text of type Text.
operation Access:
  accepts record of type Record.
  accepts words of type Vec<Word>.
  returns usize.
  body:
    let text = record.text.
    let word = words[0].
    len(word).
    len(words).
    return len(text).
operation Bad:
  accepts record of type Record.
  accepts words of type Vec<Word>.
  returns Text.
  body:
    record.missing.
    words[true].
    "abc"[0].
    push(words, "next").
    return words[0].
"#,
        );
        assert_eq!(
            codes(&check_bodies(&ir)),
            ["B109", "B109", "B109", "B108", "B102"]
        );
    }

    #[test]
    fn bodies_do_not_treat_void_calls_as_values() {
        let ir = checked_ir(
            r#"operation Bad:
  returns Text.
  body:
    let value = Void().
    return Void().
operation Void:
  body:
    len("ok").
"#,
        );
        assert_eq!(
            codes(&check_bodies(&ir)),
            ["B108", "B102"],
            "{:?}",
            check_bodies(&ir)
        );
    }

    #[test]
    fn body_diagnostics_follow_sorted_operation_names() {
        let ir = checked_ir(
            "operation Zed:\n  body:\n    return missing_z.\n\
             operation Alpha:\n  returns Text.\n  body:\n    return 1.\n",
        );
        let diagnostics = check_bodies(&ir);
        assert_eq!(codes(&diagnostics), ["B102", "B100"]);
        assert_eq!(diagnostics[0].span.line, 4);
        assert_eq!(diagnostics[1].span.line, 1);
        assert!(check_bodies(&Ir::default()).is_empty());
    }

    #[test]
    fn executable_warns_only_for_spec_only_operations() {
        let mut ir = checked_ir(
            "operation Body:\n  returns Text.\n  body:\n    return \"body\".\n\
             operation Legacy:\n  returns String.\n  responds with \"literal\".\n\
             operation Spec:\n  returns Text.\n",
        );
        let server_ir = executable_ir();
        ir.servers = server_ir.servers;
        ir.routes = server_ir.routes;
        let diagnostics = check_exec(&ir);
        assert_eq!(codes(&diagnostics), ["W100"]);
        assert!(diagnostics[0].message.contains("`Spec`"));
        let legacy = ir.operations.get_mut("Legacy").unwrap();
        legacy.body.clear();
        assert!(legacy.responds_literal.is_some());
        assert_eq!(codes(&check_exec(&ir)), ["W100"]);
    }

    #[test]
    fn executable_tupoi_and_supported_responses_pass() {
        let mut ir = executable_ir();
        assert!(check_exec(&ir).is_empty());
        for response in [
            RespondsKind::Text,
            RespondsKind::Literal(String::new()),
            RespondsKind::Literal("hello\n世界".into()),
        ] {
            ir.routes.get_mut("Say").unwrap().responds = Some(response);
            assert!(check_exec(&ir).is_empty());
        }
    }

    #[test]
    fn executable_requires_server_and_routes() {
        assert_eq!(codes(&check_exec(&Ir::default())), ["X107"]);
        let mut ir = executable_ir();
        ir.routes.clear();
        assert_eq!(codes(&check_exec(&ir)), ["X102"]);
        ir = executable_ir();
        ir.servers.clear();
        assert_eq!(codes(&check_exec(&ir)), ["X100"]);
    }

    #[test]
    fn executable_server_cardinality_port_and_version_errors() {
        let mut ir = executable_ir();
        for port in [None, Some(0)] {
            ir.servers.get_mut("TupoiServer").unwrap().port = port;
            assert_eq!(codes(&check_exec(&ir)), ["X100"]);
        }
        for port in [1, 65535] {
            ir.servers.get_mut("TupoiServer").unwrap().port = Some(port);
            assert!(check_exec(&ir).is_empty());
        }
        ir.servers.get_mut("TupoiServer").unwrap().http_version = None;
        assert_eq!(codes(&check_exec(&ir)), ["X100"]);
        for version in ["", "HTTP/1.1", "HTTP/2"] {
            ir.servers.get_mut("TupoiServer").unwrap().http_version = Some(version.into());
            assert_eq!(codes(&check_exec(&ir)), ["X101"]);
        }
        ir = executable_ir();
        let mut duplicate = ir.servers["TupoiServer"].clone();
        duplicate.name = "ZServer".into();
        ir.servers.insert(duplicate.name.clone(), duplicate);
        assert_eq!(codes(&check_exec(&ir)), ["X100"]);
    }

    #[test]
    fn executable_route_method_path_and_response_errors() {
        let mut ir = executable_ir();
        ir.routes.get_mut("Say").unwrap().method = None;
        assert_eq!(codes(&check_exec(&ir)), ["X102"]);
        ir.routes.get_mut("Say").unwrap().method = Some(RouteMethod::Get);
        ir.routes.get_mut("Say").unwrap().responds = Some(RespondsKind::Text);
        for path in [None, Some(""), Some("say/:what"), Some("/say/:")] {
            ir.routes.get_mut("Say").unwrap().path = path.map(str::to_owned);
            assert_eq!(codes(&check_exec(&ir)), ["X103"]);
        }
        for path in ["/", "/say/:what", "/世界/:what"] {
            ir.routes.get_mut("Say").unwrap().path = Some(path.into());
            assert!(check_exec(&ir).is_empty());
        }
        ir.routes.get_mut("Say").unwrap().responds = None;
        assert_eq!(codes(&check_exec(&ir)), ["X104"]);
        for param in ["", "bad name", "9bad"] {
            ir.routes.get_mut("Say").unwrap().responds = Some(RespondsKind::Param(param.into()));
            assert_eq!(codes(&check_exec(&ir)), ["X104", "X106"]);
        }
        ir.routes.get_mut("Say").unwrap().responds = Some(RespondsKind::Param("missing".into()));
        assert_eq!(codes(&check_exec(&ir)), ["X106"]);
    }

    #[test]
    fn executable_character_response_checks_only_matching_operation_parameters() {
        let mut ir = executable_ir();
        let operation = OperationDecl {
            name: "Echo".into(),
            span: Span::single(10, 1),
            accepts: vec![ParamDecl {
                name: "what".into(),
                ty: named("Character"),
            }],
            returns: Some(named("Text")),
            effects: Vec::new(),
            requires: Vec::new(),
            ensures: Vec::new(),
            ownership: Default::default(),
            generated: false,
            responds_literal: Some("hello".into()),
            c_export: None,
            c_import: None,
            body: Vec::new(),
        };
        ir.operations.insert(operation.name.clone(), operation);
        assert_eq!(codes(&check_exec(&ir)), ["X105"]);
        ir.operations.get_mut("Echo").unwrap().accepts[0].name = "other".into();
        assert!(check_exec(&ir).is_empty());
        ir.operations.get_mut("Echo").unwrap().accepts[0].name = "what".into();
        for ty in ["Word", "Text"] {
            ir.operations.get_mut("Echo").unwrap().accepts[0].ty = named(ty);
            assert!(check_exec(&ir).is_empty());
        }
        ir.operations.get_mut("Echo").unwrap().responds_literal = None;
        let diagnostics = check_exec(&ir);
        assert_eq!(codes(&diagnostics), ["W100"]);
        assert_eq!(diagnostics[0].severity, Severity::Warning);
        ir.operations.get_mut("Echo").unwrap().responds_literal = Some("hello".into());
        ir.operations.get_mut("Echo").unwrap().returns = Some(named("String"));
        assert!(check_exec(&ir).is_empty());
    }

    #[test]
    fn executable_diagnostics_follow_name_and_rule_order() {
        let mut ir = executable_ir();
        ir.servers.get_mut("TupoiServer").unwrap().port = None;
        ir.servers.get_mut("TupoiServer").unwrap().http_version = Some("HTTP/2".into());
        ir.routes.clear();
        for (name, line) in [("ZRoute", 20), ("ARoute", 30)] {
            ir.routes.insert(
                name.into(),
                RouteDecl {
                    name: name.into(),
                    span: Span::single(line, 1),
                    method: None,
                    path: None,
                    responds: None,
                },
            );
        }
        let diagnostics = check_exec(&ir);
        assert_eq!(
            codes(&diagnostics),
            ["X100", "X101", "X102", "X103", "X104", "X102", "X103", "X104"]
        );
        assert_eq!(
            diagnostics.iter().map(|d| d.span.line).collect::<Vec<_>>(),
            [1, 1, 30, 30, 30, 20, 20, 20]
        );
        assert!(diagnostics.iter().all(|d| d.severity == Severity::Error));
    }

    fn generic(name: &str, args: Vec<TypeRef>) -> TypeRef {
        TypeRef::Generic {
            name: name.into(),
            args,
        }
    }

    fn types_ir(types: Vec<TypeRef>) -> Ir {
        let entity = EntityDecl {
            name: "Record".into(),
            span: Span::single(1, 1),
            fields: types
                .into_iter()
                .enumerate()
                .map(|(index, ty)| FieldDecl {
                    name: format!("field_{index}"),
                    ty,
                    span: Span::single(index + 2, 3),
                })
                .collect(),
            invariants: Vec::new(),
            c_layout: false,
            json: Default::default(),
            iteration: None,
            generated: false,
        };
        build(&SalFile {
            items: vec![Item::Entity(entity)],
        })
        .0
    }

    #[test]
    fn duplicate_names_cross_kinds_and_application_keep_first() {
        let file = parsed(
            "application App.\n\
             entity App:\n  has id of type UUID.\n\
             entity Shared:\n  has first of type String.\n\
             enum Shared:\n  Replaced.\n\
             entity Shared:\n  has second of type bool.\n",
        );
        let (ir, diagnostics) = build(&file);
        assert_eq!(codes(&diagnostics), ["E1001", "E1001", "E1001"]);
        assert!(diagnostics
            .iter()
            .all(|value| value.severity == Severity::Error));
        assert!(!ir.entities.contains_key("App"));
        assert!(!ir.enums.contains_key("Shared"));
        assert_eq!(ir.entities["Shared"].fields[0].name, "first");
        assert_eq!(ir.file.items.len(), file.items.len());
    }

    #[test]
    fn primitives_named_types_and_nested_generics_are_valid() {
        let mut types: Vec<_> = [
            "bool",
            "String",
            "UUID",
            "Character",
            "Word",
            "Text",
            "u8",
            "u16",
            "u32",
            "u64",
            "u128",
            "i8",
            "i16",
            "i32",
            "i64",
            "i128",
            "f32",
            "f64",
            "usize",
            "isize",
            "Record",
        ]
        .into_iter()
        .map(named)
        .collect();
        types.push(generic(
            "Result",
            vec![
                generic("Option", vec![generic("Vec", vec![named("Record")])]),
                generic("Money", vec![named("USD")]),
            ],
        ));
        let ir = types_ir(types);
        assert!(check_types(&ir).is_empty());
        let ir = checked_ir(
            "enum Status:\n  Ready.\n\
             operation Get:\n  accepts input of type Option<Status>.\n  returns Result<Status, String>.\n",
        );
        assert!(check_types(&ir).is_empty());
    }

    #[test]
    fn type_errors_recurse_and_currency_is_not_a_named_type() {
        let ir = types_ir(vec![
            named("Missing"),
            generic("Unknown", vec![named("NestedMissing")]),
            generic("Money", vec![named("usd")]),
            generic("Option", Vec::new()),
            generic("Vec", vec![named("bool"), named("String")]),
            generic("Result", vec![named("bool")]),
            generic("Money", Vec::new()),
            generic("Money", vec![generic("Vec", vec![named("Absent")])]),
        ]);
        let diagnostics = check_types(&ir);
        assert_eq!(
            codes(&diagnostics),
            [
                "E2001", "E2002", "E2001", "E2003", "E2004", "E2004", "E2004", "E2004", "E2003",
                "E2001",
            ]
        );
        assert_eq!(diagnostics[0].span.line, 2);
        for currency in ["US", "USDD", "U1D", "UsD", "ÜSD", ""] {
            let ir = types_ir(vec![generic("Money", vec![named(currency)])]);
            assert_eq!(codes(&check_types(&ir)), ["E2003"], "{currency}");
        }
    }

    #[test]
    fn parameter_and_return_types_are_checked() {
        let ir = checked_ir(
            "operation Get:\n  accepts input of type Vec<Missing>.\n  returns Unknown<String>.\n",
        );
        assert_eq!(codes(&check_types(&ir)), ["E2001", "E2002"]);
    }

    #[test]
    fn architecture_reports_membership_ownership_and_dependency_errors() {
        let ir = checked_ir(
            "service Service:\n  belongs to Missing.\n\
             module First:\n  belongs to Absent.\n  owns Resource.\n  cannot modify Resource.\n\
             module Second:\n  owns Resource.\n  may modify Other.\n  cannot modify Other.\n\
             enum Status:\n  Ready.\n\
             layer Domain:\n  owns Status.\n  may depend on Ghost.\n  must not depend on Ghost directly.\n",
        );
        let diagnostics = check_architecture(&ir);
        assert_eq!(
            codes(&diagnostics),
            [
                "ARCH101", "ARCH101", "ARCH107", "ARCH106", "ARCH107", "ARCH102", "ARCH103",
                "ARCH103", "ARCH104",
            ]
        );
        assert!(diagnostics
            .iter()
            .all(|value| value.severity == Severity::Error));
    }

    #[test]
    fn cycles_list_the_path_and_include_self_cycles() {
        let ir = checked_ir(
            "layer A:\n  may depend on B.\n\
             layer B:\n  may depend on C.\n\
             layer C:\n  may depend on A.\n\
             layer SelfCycle:\n  may depend on SelfCycle.\n",
        );
        let diagnostics = check_architecture(&ir);
        assert_eq!(codes(&diagnostics), ["ARCH105", "ARCH105"]);
        assert!(diagnostics[0].message.contains("A -> B -> C -> A"));
        assert!(diagnostics[1].message.contains("SelfCycle -> SelfCycle"));
    }

    #[test]
    fn valid_architecture_accepts_plain_resources_and_interfaces() {
        let ir = checked_ir(
            "entity Model:\n  has id of type UUID.\n\
             operation Fetch:\n  returns Model.\n\
             service Service:\n  belongs to Domain.\n  implements UnmodeledInterface.\n\
             module Storage:\n  belongs to Infra.\n  owns PlainResource.\n  owns PlainResource.\n  may read Other.\n  implements OtherInterface.\n\
             layer Domain:\n  owns Model.\n  owns Service.\n  owns Fetch.\n  must not depend on Infra.\n\
             layer Infra:\n  owns Storage.\n  may depend on Domain.\n",
        );
        assert!(check_architecture(&ir).is_empty());
        assert_eq!(layer_of(&ir, "Model").as_deref(), Some("Domain"));
        assert_eq!(layer_of(&ir, "Service").as_deref(), Some("Domain"));
        assert_eq!(layer_of(&ir, "Storage").as_deref(), Some("Infra"));
        assert_eq!(layer_of(&ir, "Fetch"), None);
        assert_eq!(layer_of(&ir, "Unknown"), None);
    }

    #[test]
    fn converging_dependency_paths_do_not_create_cycles() {
        let ir = checked_ir(
            "layer A:\n  may depend on B.\n  may depend on C.\n\
             layer B:\n  may depend on D.\n\
             layer C:\n  may depend on D.\n\
             layer D:\n  owns Model.\n\
             entity Model:\n  has value of type bool.\n",
        );
        assert!(check_architecture(&ir).is_empty());
    }

    #[test]
    fn effects_reject_pure_with_other_effects() {
        let ir = checked_ir(
            "operation Impure:\n  effects: Pure, HTTPAccess.\n\
             operation PureOnly:\n  effects: Pure, Pure.\n\
             operation Unrestricted:\n  effects: HTTPAccess, DatabaseAccess.\n",
        );
        assert_eq!(codes(&check_effects(&ir)), ["EFF202"]);
        let (_, diagnostics) = build(&parsed(
            "service Promise:\n  allowed effects:\n    DatabaseAccess.\n  forbidden effects:\n    HTTPAccess.\n",
        ));
        assert_eq!(codes(&diagnostics), ["DEC102"]);
    }

    fn imports(module: &str, paths: &[&str]) -> RustFile {
        RustFile {
            module: module.into(),
            imports: paths.iter().map(|path| (*path).into()).collect(),
        }
    }

    #[test]
    fn imports_require_direct_edges_and_allow_self_and_external_crates() {
        let ir = checked_ir(
            "layer Domain:\n  owns Model.\n\
             layer Infra:\n  may depend on Domain.\n\
             layer UI:\n  may depend on Infra.\n\
             entity Model:\n  has id of type UUID.\n\
             module Storage:\n  belongs to Infra.\n\
             module View:\n  belongs to UI.\n",
        );
        assert!(verify_rust_imports(
            &ir,
            &[
                imports("Storage", &["DOMAIN::Model", "infra::local", "std::fmt"]),
                imports("Model", &["domain::Model"]),
                imports("View", &["infra::Storage"]),
            ],
        )
        .is_empty());
        let diagnostics = verify_rust_imports(
            &ir,
            &[
                imports("Model", &["infra::Storage"]),
                imports("View", &["domain::Model"]),
            ],
        );
        assert_eq!(codes(&diagnostics), ["ARCH001", "ARCH001"]);
    }

    #[test]
    fn import_unknown_modules_and_undetermined_layers_are_distinct() {
        let ir = checked_ir(
            "module Loose:\n  forbids DatabaseAccess.\n\
             operation Execute:\n  returns String.\n",
        );
        let diagnostics = verify_rust_imports(
            &ir,
            &[
                imports("Absent", &["std::fmt"]),
                imports("Loose", &["std::fmt", "crate::SQLX_adapter"]),
                imports("Execute", &[]),
            ],
        );
        assert_eq!(
            codes(&diagnostics),
            ["ARCH201", "ARCH202", "ARCH301", "ARCH202"]
        );
        assert_eq!(diagnostics[0].severity, Severity::Error);
        assert_eq!(diagnostics[1].severity, Severity::Warning);
        assert_eq!(diagnostics[2].severity, Severity::Error);
        assert_eq!(diagnostics[3].severity, Severity::Warning);
    }

    #[test]
    fn capabilities_match_all_crates_case_insensitively_in_any_segment() {
        let ir = checked_ir(
            "layer Domain:\n  owns Restricted.\n  owns Free.\n\
             module Restricted:\n  belongs to Domain.\n  forbids databaseaccess.\n  forbids HTTPACCESS.\n\
             module Free:\n  belongs to Domain.\n",
        );
        for name in [
            "sqlx",
            "postgres",
            "diesel",
            "rusqlite",
            "sea_orm",
            "mongodb",
            "redis",
            "reqwest",
            "hyper",
            "axum",
            "actix_web",
            "tower_http",
        ] {
            let path = format!(
                "wrapper::prefix_{}_suffix::Client",
                name.to_ascii_uppercase()
            );
            let diagnostics = verify_rust_imports(&ir, &[imports("Restricted", &[&path])]);
            assert_eq!(codes(&diagnostics), ["ARCH301"], "{name}");
            assert!(verify_rust_imports(&ir, &[imports("Free", &[&path])]).is_empty());
        }
        assert!(verify_rust_imports(&ir, &[imports("Restricted", &["std::fmt"])]).is_empty());
    }
}
