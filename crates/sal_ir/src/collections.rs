//! Typed POD collections lowering: `Vector<T>` / `Map<K,V>` erasure plus
//! generated typed marshalling wrappers.
//!
//! CONTRACT (canonical surface, Main-fixed arities):
//! - `vector(T, capacity)` binds an owned `Vector<T>`; `vector_drop(v)`
//!   consumes; `vector_len` / `vector_capacity` borrow and return `usize`;
//!   `vector_reserve(v, capacity)` borrows and returns `i64` (0 success,
//!   -12 allocation failure); `vector_push(v, x)` borrows and returns `i64`
//!   (0 / -12); `vector_get(v, i)` borrows and returns `ValueResult<T>`;
//!   `vector_set(v, i, x)` borrows and returns `i64` (0 / -22);
//!   `vector_pop(v)` borrows and returns `ValueResult<T>`.
//! - `map(K, V, capacity)` binds an owned `Map<K,V>`; `map_drop(m)` consumes;
//!   `map_len` / `map_capacity` borrow and return `usize`;
//!   `map_reserve(m, capacity)` borrows and returns `i64` (0 / -12);
//!   `map_insert(m, k, v)` borrows and returns `i64` (0 new, 1 replaced,
//!   -12); `map_get(m, k)` borrows and returns `ValueResult<V>`;
//!   `map_remove(m, k)` borrows and returns `ValueResult<V>`;
//!   `map_contains(m, k)` borrows and returns `bool`.
//! - POD is integers, `bool`, or recursive plain C-layout records thereof.
//!   Borrowed access goes through the ORIGINAL owner slot (`borrow(slot)` +
//!   field offsets, so mutations never lose a wrapper copy); zero capacity
//!   allocates nothing (metadata lives on the caller stack); reads, pops,
//!   removals and contains never allocate and never rehash; reserve/push/
//!   insert are failure-atomic. Constructors exit nonzero on allocation
//!   failure. Key hashing/equality works on generated field-wise packed key
//!   bytes, so C padding never affects lookup; no raw record memcmp.
//! - All storage/growth/hash/probe/delete algorithms are SAL source in
//!   `stdlib/collections.sal` (`Collection*` helpers). This pass only validates the original types
//!   (ownership itself was validated by the memory pass first) and generates
//!   thin typed marshalling wrappers. Generated names all start with
//!   `SalColl`; generated records/wrappers carry `generated = true`.
//!   Source `SalColl*` collisions are rejected with COL208 BEFORE emission;
//!   genuine generated items are accepted by the registry.
//! - Effects: constructors/drop/reserve/push/insert wrappers declare
//!   `SystemCall`; every wrapper body wraps its raw slot/helper calls in an
//!   explicit `unsafe:` block (discharging `UnsafeMemory` only) and declares
//!   just the public `SystemCall` (get/len/capacity/set/pop/remove/contains
//!   plus the Zero and KeyPack helpers declare `Pure`).
//! - Diagnostics are `COL201` (unknown/non-POD element type), `COL202`
//!   (canonical call shape/arity), `COL203` (collection owner/result across
//!   a C ABI boundary), `COL204` (drop of a `Borrow`), `COL208`
//!   (namespace collision / excessive nesting).
//! - The pass is idempotent and preserves non-collection programs exactly:
//!   without canonical calls or collection generics the input file is
//!   returned cloned.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use sal_syntax::{Diagnostic, Expr, Item, OperationDecl, Severity, Span, Stmt, TypeRef};

/// Reserved prefix for every generated top-level name and nothing else.
const GEN_PREFIX: &str = "SalColl";
/// Linux `exit_group` syscall number used for constructor OOM exit.
const EXIT_GROUP: i64 = 231;
/// Maximum tracked AST nesting depth for analysis and rewrite.
const MAX_DEPTH: usize = 128;

fn err(code: &'static str, message: String, span: &Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span: span.clone(),
        suggestion: None,
    }
}

fn is_canonical_call(name: &str) -> bool {
    matches!(
        name,
        "vector"
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

fn scalar_width(name: &str) -> Option<usize> {
    match name {
        "bool" | "u8" | "i8" => Some(1),
        "u16" | "i16" => Some(2),
        "u32" | "i32" => Some(4),
        "u64" | "i64" | "usize" | "isize" => Some(8),
        _ => None,
    }
}

fn is_integer_name(name: &str) -> bool {
    matches!(
        name,
        "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "usize" | "isize"
    )
}

fn generic_parts(ty: &TypeRef) -> Option<(&str, &[TypeRef])> {
    match ty {
        TypeRef::Generic { name, args } => Some((name.as_str(), args.as_slice())),
        TypeRef::Named(_) => None,
    }
}

/// One affine-safe POD shape: scalars plus C-layout records thereof.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Pod {
    Scalar(String),
    Record(String),
}

fn pod_of(ty: &TypeRef) -> Option<Pod> {
    match ty {
        TypeRef::Named(name) => {
            if is_integer_name(name) || name == "bool" {
                Some(Pod::Scalar(name.clone()))
            } else {
                Some(Pod::Record(name.clone()))
            }
        }
        TypeRef::Generic { .. } => None,
    }
}

/// Structural POD validation with entity lookup: scalars always fine,
/// records must exist, be C-layout, and contain only POD fields
/// (transitively, acyclically). Spans, handles and nested generics fail.
fn checked_pod(
    ty: &TypeRef,
    entities: &EntityTable,
    visiting: &mut BTreeSet<String>,
) -> Option<Pod> {
    match pod_of(ty)? {
        Pod::Scalar(_) => pod_of(ty),
        Pod::Record(name) => {
            if !visiting.insert(name.clone()) {
                return None;
            }
            let valid = entities
                .get(&name)
                .filter(|(c_layout, _)| *c_layout)
                .is_some_and(|(_, fields)| {
                    fields
                        .iter()
                        .all(|(_, field)| checked_pod(field, entities, visiting).is_some())
                });
            visiting.remove(&name);
            if valid {
                Some(Pod::Record(name))
            } else {
                None
            }
        }
    }
}

fn checked_pod_top(
    ty: &TypeRef,
    entities: &EntityTable,
) -> Option<Pod> {
    checked_pod(ty, entities, &mut BTreeSet::new())
}

/// True when a type mentions any collections-owned generic.
fn mentions_collections(ty: &TypeRef) -> bool {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if let TypeRef::Generic { name, args } = ty {
            if matches!(name.as_str(), "Vector" | "Map" | "ValueResult" | "Borrow") {
                return true;
            }
            pending.extend(args.iter());
        }
    }
    false
}

fn fnv1a(text: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn sanitize(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.is_empty() || out.as_bytes()[0].is_ascii_digit() {
        out.insert(0, '_');
    }
    out
}

/// Deterministic collision-free tag for one POD type. Scalars use a fixed
/// `P_` vocabulary; records use length- plus hash-qualified `R_` names so a
/// record literally named `I64` can never collide with primitive `i64`.
fn pod_tag(pod: &Pod) -> String {
    match pod {
        Pod::Scalar(name) => {
            let upper = match name.as_str() {
                "i8" => "I8",
                "i16" => "I16",
                "i32" => "I32",
                "i64" => "I64",
                "u8" => "U8",
                "u16" => "U16",
                "u32" => "U32",
                "u64" => "U64",
                "usize" => "USIZE",
                "isize" => "ISIZE",
                "bool" => "BOOL",
                _ => "UNKNOWN",
            };
            format!("P_{upper}")
        }
        Pod::Record(name) => {
            format!("R_{}_{}_{:016X}", sanitize(name), name.len(), fnv1a(name))
        }
    }
}

fn vec_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Vec_{tag}")
}

fn map_name(ktag: &str, vtag: &str) -> String {
    format!("{GEN_PREFIX}Map_{ktag}_{vtag}")
}

fn res_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Result_{tag}")
}

fn box_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Box_{tag}")
}

fn keybuf_name(ktag: &str) -> String {
    format!("{GEN_PREFIX}KeyBuf_{ktag}")
}

fn zero_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Zero_{tag}")
}

fn pack_name(ktag: &str) -> String {
    format!("{GEN_PREFIX}KeyPack_{ktag}")
}

/// Fast iterative probe: does this file need collections lowering at all?
/// Generated `SalColl` items alone never trigger a second pass. Only
/// canonical call names or collection generics on non-generated items do.
fn needs_lower(file: &sal_syntax::SalFile) -> bool {
    for item in &file.items {
        match item {
            Item::Entity(entity) => {
                if entity.generated {
                    continue;
                }
                if entity
                    .fields
                    .iter()
                    .any(|field| mentions_collections(&field.ty))
                {
                    return true;
                }
            }
            Item::Operation(operation) => {
                if operation.generated {
                    continue;
                }
                for param in &operation.accepts {
                    if mentions_collections(&param.ty) {
                        return true;
                    }
                }
                if operation.returns.as_ref().is_some_and(mentions_collections) {
                    return true;
                }
                if body_mentions_canonical(&operation.body) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn body_mentions_canonical(body: &[Stmt]) -> bool {
    let mut stmts: Vec<&Stmt> = body.iter().collect();
    let mut exprs: Vec<&Expr> = Vec::new();
    while let Some(stmt) = stmts.pop() {
        match stmt {
            Stmt::Let { expr, .. } | Stmt::Assign { expr, .. } | Stmt::Return(expr) => {
                exprs.push(expr);
            }
            Stmt::ExprStmt(expr) => exprs.push(expr),
            Stmt::If { cond, then, else_ } => {
                exprs.push(cond);
                stmts.extend(then.iter());
                stmts.extend(else_.iter());
            }
            Stmt::While { cond, body } => {
                exprs.push(cond);
                stmts.extend(body.iter());
            }
            Stmt::For { iter, body, .. } => {
                exprs.push(iter);
                stmts.extend(body.iter());
            }
            Stmt::Unsafe { body } => {
                stmts.extend(body.iter());
            }
            Stmt::Break | Stmt::Continue => {}
        }
        while let Some(expr) = exprs.pop() {
            match expr {
                Expr::Call { name, args } => {
                    if is_canonical_call(name) {
                        return true;
                    }
                    exprs.extend(args.iter());
                }
                Expr::Field { base, .. } | Expr::Not(base) => exprs.push(base),
                Expr::Index { base, index } => {
                    exprs.push(base);
                    exprs.push(index);
                }
                Expr::BinOp { left, right, .. } => {
                    exprs.push(left);
                    exprs.push(right);
                }
                Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
            }
        }
    }
    false
}

/// True once this pass already produced its output in `file`: the compiler
/// emitted generated `SalColl*` records. The wrappers address owner slots
/// through `borrow(slot) + offset`, which is intentionally not an ownership
/// form, so a file in this state has already passed the memory pass (it runs
/// before this one) and must not be fed through it a second time. Provenance
/// is the parser-false `generated` flag, never the name alone.
pub fn is_lowered(file: &sal_syntax::SalFile) -> bool {
    file.items.iter().any(|item| {
        matches!(item, Item::Entity(entity) if entity.generated && entity.name.starts_with(GEN_PREFIX))
    })
}

/// Source-loader hook: the combined source needs `std/collections.sal`
/// when user code mentions the typed collection surface.
pub fn requires_collections_runtime(file: &sal_syntax::SalFile) -> bool {
    needs_lower(file)
}

/// Lower typed collections into ordinary SAL AST plus generated wrappers.
///
/// Non-collection files are returned cloned (byte-equivalent). Invalid
/// collection programs fail with `COL*` diagnostics. The pass runs after
/// memory validation and performs no ownership checking of its own.
pub fn lower(file: &sal_syntax::SalFile) -> Result<sal_syntax::SalFile, Vec<Diagnostic>> {
    if !needs_lower(file) {
        return Ok(file.clone());
    }
    Pass::run(file)
}

/// Entity name -> (C layout, fields).
type EntityTable = HashMap<String, (bool, Vec<(String, TypeRef)>)>;

struct Registry {
    entities: EntityTable,
}

#[derive(Debug, Clone)]
struct Slot {
    ty: Option<TypeRef>,
    borrowed: bool,
}

#[derive(Debug, Clone, Default)]
struct Scope {
    slots: HashMap<String, Slot>,
}

struct Pass<'a> {
    registry: &'a Registry,
    op_returns: HashMap<String, Option<TypeRef>>,
    op_params: HashMap<String, Vec<TypeRef>>,
    vec_terms: BTreeMap<String, TypeRef>,
    map_terms: BTreeMap<(String, String), (TypeRef, TypeRef)>,
    emitted_records: BTreeSet<String>,
    emitted_ops: BTreeSet<String>,
    diagnostics: Vec<Diagnostic>,
    operation: String,
    op_span: Span,
}

impl<'a> Pass<'a> {
    fn run(file: &sal_syntax::SalFile) -> Result<sal_syntax::SalFile, Vec<Diagnostic>> {
        let mut entities: EntityTable = HashMap::new();
        let mut op_returns: HashMap<String, Option<TypeRef>> = HashMap::new();
        let mut op_params: HashMap<String, Vec<TypeRef>> = HashMap::new();
        for item in &file.items {
            match item {
                Item::Entity(entity) => {
                    entities.entry(entity.name.clone()).or_insert_with(|| {
                        (
                            entity.c_layout,
                            entity
                                .fields
                                .iter()
                                .map(|field| (field.name.clone(), field.ty.clone()))
                                .collect(),
                        )
                    });
                }
                Item::Operation(operation) => {
                    op_returns
                        .entry(operation.name.clone())
                        .or_insert_with(|| operation.returns.clone());
                    op_params.entry(operation.name.clone()).or_insert_with(|| {
                        operation
                            .accepts
                            .iter()
                            .map(|param| param.ty.clone())
                            .collect()
                    });
                }
                _ => {}
            }
        }
        let registry = Registry { entities };
        let span = file
            .items
            .first()
            .map(|item| match item {
                Item::Application { span, .. } | Item::Use { span, .. } => span.clone(),
                Item::Entity(value) => value.span.clone(),
                Item::Enum(value) => value.span.clone(),
                Item::Operation(value) => value.span.clone(),
                Item::Module(value) => value.span.clone(),
                Item::Service(value) => value.span.clone(),
                Item::Server(value) => value.span.clone(),
                Item::Layer(value) => value.span.clone(),
                Item::Route(value) => value.span.clone(),
            })
            .unwrap_or(Span::single(1, 1));
        let mut pass = Pass {
            registry: &registry,
            op_returns,
            op_params,
            vec_terms: BTreeMap::new(),
            map_terms: BTreeMap::new(),
            emitted_records: BTreeSet::new(),
            emitted_ops: BTreeSet::new(),
            diagnostics: Vec::new(),
            operation: String::new(),
            op_span: span.clone(),
        };
        // C ABI guard: collection owners/results never cross `extern "C"`.
        for item in &file.items {
            if let Item::Operation(operation) = item {
                if operation.c_import.is_none() && operation.c_export.is_none() {
                    continue;
                }
                let mut bad: Option<String> = None;
                for param in &operation.accepts {
                    if mentions_collections(&param.ty) {
                        bad = Some(format!("parameter `{}`", param.name));
                        break;
                    }
                }
                if bad.is_none() {
                    if let Some(returns) = &operation.returns {
                        if mentions_collections(returns) {
                            bad = Some("return type".into());
                        }
                    }
                }
                if let Some(where_) = bad {
                    pass.diagnostics.push(err(
                        "COL203",
                        format!(
                            "operation `{}` cannot expose a collection owner/result across C ABI ({where_}); keep ownership inside SAL and pass only scalars or C records",
                            operation.name
                        ),
                        &operation.span,
                    ));
                }
            }
        }
        // Source namespace check: user `SalColl*` top-level names collide
        // with compiler generation. Checked BEFORE emission; genuine
        // generated items (generated = true) are accepted.
        for item in &file.items {
            let (name, generated, item_span) = match item {
                Item::Entity(entity) => (entity.name.as_str(), entity.generated, &entity.span),
                Item::Operation(operation) => (
                    operation.name.as_str(),
                    operation.generated,
                    &operation.span,
                ),
                _ => continue,
            };
            if name.starts_with(GEN_PREFIX) && !generated {
                pass.diagnostics.push(err(
                    "COL208",
                    format!("`{name}` collides with the compiler collections namespace"),
                    item_span,
                ));
            }
        }
        // Validate + rewrite every operation, collecting instance types.
        let mut rewritten: Vec<(Item, Vec<Stmt>)> = Vec::new();
        let mut passthrough: Vec<Item> = Vec::new();
        for item in &file.items {
            match item {
                Item::Operation(operation) => {
                    if operation.generated {
                        passthrough.push(item.clone());
                        continue;
                    }
                    pass.operation = operation.name.clone();
                    pass.op_span = operation.span.clone();
                    pass.check_signature(operation);
                    let mut scope = Scope::default();
                    for param in &operation.accepts {
                        let borrowed = matches!(generic_parts(&param.ty), Some(("Borrow", _)));
                        scope.slots.insert(
                            param.name.clone(),
                            Slot {
                                ty: Some(param.ty.clone()),
                                borrowed,
                            },
                        );
                    }
                    let body = pass.rewrite_block(&operation.body, &mut scope, 0);
                    let mut erased = operation.clone();
                    for param in &mut erased.accepts {
                        param.ty = pass.erase_ty(&param.ty);
                    }
                    erased.returns = erased.returns.as_ref().map(|ty| pass.erase_ty(ty));
                    rewritten.push((Item::Operation(erased), body));
                }
                Item::Entity(entity) => {
                    if entity.generated {
                        passthrough.push(item.clone());
                        continue;
                    }
                    let mut erased = entity.clone();
                    for field in &mut erased.fields {
                        field.ty = pass.erase_ty(&field.ty);
                    }
                    passthrough.push(Item::Entity(erased));
                }
                _ => passthrough.push(item.clone()),
            }
        }
        if !pass.diagnostics.is_empty() {
            return Err(pass.diagnostics);
        }
        let mut out: Vec<Item> = Vec::new();
        pass.emit_instances(&mut out, &span);
        for item in passthrough {
            out.push(item);
        }
        for (item, body) in rewritten {
            match item {
                Item::Operation(mut operation) => {
                    operation.body = body;
                    out.push(Item::Operation(operation));
                }
                _ => out.push(item),
            }
        }
        Ok(sal_syntax::SalFile { items: out })
    }

    fn report(&mut self, code: &'static str, message: String) {
        let span = self.op_span.clone();
        self.diagnostics.push(err(code, message, &span));
    }

    /// Erase collection types to generated record names, preserving every
    /// other type exactly. Borrow markers are kept; only the inner owner
    /// is erased.
    fn erase_ty(&self, ty: &TypeRef) -> TypeRef {
        match ty {
            TypeRef::Named(_) => ty.clone(),
            TypeRef::Generic { name, args } => {
                if name == "Vector" && args.len() == 1 {
                    if let Some(pod) = checked_pod_top(&args[0], &self.registry.entities) {
                        return TypeRef::Named(vec_name(&pod_tag(&pod)));
                    }
                    return ty.clone();
                }
                if name == "Map" && args.len() == 2 {
                    if let (Some(key), Some(value)) = (
                        checked_pod_top(&args[0], &self.registry.entities),
                        checked_pod_top(&args[1], &self.registry.entities),
                    ) {
                        return TypeRef::Named(map_name(&pod_tag(&key), &pod_tag(&value)));
                    }
                    return ty.clone();
                }
                if name == "ValueResult" && args.len() == 1 {
                    if let Some(pod) = checked_pod_top(&args[0], &self.registry.entities) {
                        return TypeRef::Named(res_name(&pod_tag(&pod)));
                    }
                    return ty.clone();
                }
                if name == "Borrow" && args.len() == 1 {
                    return TypeRef::Generic {
                        name: name.clone(),
                        args: vec![self.erase_ty(&args[0])],
                    };
                }
                ty.clone()
            }
        }
    }

    /// Signature check: every collection element type must be POD.
    fn check_signature(&mut self, operation: &OperationDecl) {
        let mut pending: Vec<&TypeRef> = Vec::new();
        for param in &operation.accepts {
            pending.push(&param.ty);
        }
        if let Some(returns) = &operation.returns {
            pending.push(returns);
        }
        while let Some(ty) = pending.pop() {
            match ty {
                TypeRef::Named(_) => {}
                TypeRef::Generic { name, args } => {
                    if (name == "Vector" || name == "ValueResult") && args.len() == 1 {
                        if checked_pod_top(&args[0], &self.registry.entities).is_none() {
                            self.report(
                                "COL201",
                                format!(
                                    "unsupported collection element type {:?}; payloads must be integers, bool, or plain C records thereof",
                                    args[0]
                                ),
                            );
                        }
                    } else if name == "Map" && args.len() == 2 {
                        for arg in args {
                            if checked_pod_top(arg, &self.registry.entities).is_none() {
                                self.report(
                                    "COL201",
                                    format!(
                                        "unsupported map key/value type {arg:?}; keys and values must be integers, bool, or plain C records thereof"
                                    ),
                                );
                            }
                        }
                    } else {
                        pending.extend(args.iter());
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Owner resolution and instance collection.
// ---------------------------------------------------------------------------

impl<'a> Pass<'a> {
    fn strip_borrow(ty: &TypeRef) -> TypeRef {
        match generic_parts(ty) {
            Some(("Borrow", [inner])) => inner.clone(),
            _ => ty.clone(),
        }
    }

    /// Resolve the static type of an owner expression: parameters and
    /// let-bound slots, `borrow(...)` reborrows, calls to known operations,
    /// and field projections through entities.
    fn resolve_ty(&self, expr: &Expr, scope: &Scope) -> Option<TypeRef> {
        match expr {
            Expr::Var(name) => scope.slots.get(name).and_then(|slot| slot.ty.clone()),
            Expr::Call { name, args } if name == "borrow" && args.len() == 1 => {
                self.resolve_ty(&args[0], scope)
            }
            Expr::Call { name, .. } => self.op_returns.get(name).cloned().flatten(),
            Expr::Field { base, field } => {
                let base = Self::strip_borrow(&self.resolve_ty(base, scope)?);
                match base {
                    TypeRef::Named(entity) => {
                        self.registry.entities.get(&entity).and_then(|(_, fields)| {
                            fields
                                .iter()
                                .find(|(name, _)| name == field)
                                .map(|(_, ty)| ty.clone())
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn resolve_owner(&self, expr: &Expr, scope: &Scope) -> Option<TypeRef> {
        self.resolve_ty(expr, scope)
            .map(|ty| Self::strip_borrow(&ty))
    }

    fn vec_term(&mut self, owner: &TypeRef) -> Option<(String, TypeRef)> {
        match generic_parts(owner) {
            Some(("Vector", [elem])) => {
                let pod = checked_pod_top(elem, &self.registry.entities)?;
                let tag = pod_tag(&pod);
                self.vec_terms
                    .entry(tag.clone())
                    .or_insert_with(|| elem.clone());
                Some((tag, elem.clone()))
            }
            _ => None,
        }
    }

    fn map_term(&mut self, owner: &TypeRef) -> Option<(String, String, TypeRef, TypeRef)> {
        match generic_parts(owner) {
            Some(("Map", [key, value])) => {
                let key_pod = checked_pod_top(key, &self.registry.entities)?;
                let value_pod = checked_pod_top(value, &self.registry.entities)?;
                let ktag = pod_tag(&key_pod);
                let vtag = pod_tag(&value_pod);
                self.map_terms
                    .entry((ktag.clone(), vtag.clone()))
                    .or_insert_with(|| (key.clone(), value.clone()));
                Some((ktag, vtag, key.clone(), value.clone()))
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Statement/expression rewrite (validate + erase in one walk).
// ---------------------------------------------------------------------------

impl<'a> Pass<'a> {
    fn rewrite_block(&mut self, body: &[Stmt], scope: &mut Scope, depth: usize) -> Vec<Stmt> {
        if depth > MAX_DEPTH {
            self.report(
                "COL208",
                "collection program exceeds supported nesting depth".into(),
            );
            return body.to_vec();
        }
        let mut out: Vec<Stmt> = Vec::with_capacity(body.len());
        for stmt in body {
            match stmt {
                Stmt::Let {
                    name,
                    mutable,
                    expr,
                } => {
                    if name.starts_with(GEN_PREFIX) {
                        self.report(
                            "COL208",
                            format!(
                                "binding `{name}` collides with the compiler collections namespace"
                            ),
                        );
                    }
                    let rewritten = self.rewrite_expr(expr, scope, depth + 1);
                    let slot = self.slot_of(expr, &rewritten, scope);
                    scope.slots.insert(name.clone(), slot);
                    out.push(Stmt::Let {
                        name: name.clone(),
                        mutable: *mutable,
                        expr: rewritten,
                    });
                }
                Stmt::Assign { name, expr } => {
                    let rewritten = self.rewrite_expr(expr, scope, depth + 1);
                    let slot = self.slot_of(expr, &rewritten, scope);
                    if let Some(entry) = scope.slots.get_mut(name) {
                        *entry = slot;
                    }
                    out.push(Stmt::Assign {
                        name: name.clone(),
                        expr: rewritten,
                    });
                }
                Stmt::Return(expr) => {
                    out.push(Stmt::Return(self.rewrite_expr(expr, scope, depth + 1)));
                }
                Stmt::ExprStmt(expr) => {
                    out.push(Stmt::ExprStmt(self.rewrite_expr(expr, scope, depth + 1)));
                }
                Stmt::If { cond, then, else_ } => {
                    let cond = self.rewrite_expr(cond, scope, depth + 1);
                    let mut then_scope = scope.clone();
                    let then = self.rewrite_block(then, &mut then_scope, depth + 1);
                    let mut else_scope = scope.clone();
                    let else_ = self.rewrite_block(else_, &mut else_scope, depth + 1);
                    out.push(Stmt::If { cond, then, else_ });
                }
                Stmt::While { cond, body } => {
                    let cond = self.rewrite_expr(cond, scope, depth + 1);
                    let mut inner = scope.clone();
                    let body = self.rewrite_block(body, &mut inner, depth + 1);
                    out.push(Stmt::While { cond, body });
                }
                Stmt::For { var, iter, body } => {
                    let iter = self.rewrite_expr(iter, scope, depth + 1);
                    let mut inner = scope.clone();
                    inner.slots.remove(var);
                    let body = self.rewrite_block(body, &mut inner, depth + 1);
                    out.push(Stmt::For {
                        var: var.clone(),
                        iter,
                        body,
                    });
                }
                Stmt::Unsafe { body } => {
                    let body = self.rewrite_block(body, scope, depth + 1);
                    out.push(Stmt::Unsafe { body });
                }
                Stmt::Break | Stmt::Continue => out.push(stmt.clone()),
            }
        }
        out
    }

    /// Classify a let-bound (or assigned) value for later borrow decisions.
    fn slot_of(&self, original: &Expr, _rewritten: &Expr, scope: &Scope) -> Slot {
        match original {
            Expr::Call { name, args } if name == "borrow" && args.len() == 1 => {
                let ty = self
                    .resolve_ty(&args[0], scope)
                    .map(|ty| match generic_parts(&ty) {
                        Some(("Borrow", _)) => ty,
                        _ => TypeRef::Generic {
                            name: "Borrow".into(),
                            args: vec![ty],
                        },
                    });
                Slot { ty, borrowed: true }
            }
            Expr::Call { name, args } if name == "vector" && args.len() == 2 => {
                let ty = match args.first() {
                    Some(Expr::Var(type_name)) => Some(TypeRef::Generic {
                        name: "Vector".into(),
                        args: vec![TypeRef::Named(type_name.clone())],
                    }),
                    _ => None,
                };
                Slot {
                    ty,
                    borrowed: false,
                }
            }
            Expr::Call { name, args } if name == "map" && args.len() == 3 => {
                let ty = match (&args.first(), args.get(1)) {
                    (Some(Expr::Var(key)), Some(Expr::Var(value))) => Some(TypeRef::Generic {
                        name: "Map".into(),
                        args: vec![TypeRef::Named(key.clone()), TypeRef::Named(value.clone())],
                    }),
                    _ => None,
                };
                Slot {
                    ty,
                    borrowed: false,
                }
            }
            Expr::Var(name) => scope.slots.get(name).cloned().unwrap_or(Slot {
                ty: None,
                borrowed: false,
            }),
            Expr::Call { name, .. } => {
                let ty = self.op_returns.get(name).cloned().flatten();
                let borrowed = ty
                    .as_ref()
                    .is_some_and(|ty| matches!(generic_parts(ty), Some(("Borrow", _))));
                Slot { ty, borrowed }
            }
            _ => Slot {
                ty: None,
                borrowed: false,
            },
        }
    }

    /// Wrap an owner argument for a `Borrow<...>` wrapper parameter: a
    /// syntactic `borrow(...)` result or a provably borrowed slot is
    /// forwarded as-is (it already denotes the original slot); an owned
    /// slot is wrapped with `borrow(...)`.
    fn borrow_arg(&mut self, arg: &Expr, scope: &Scope, depth: usize) -> Expr {
        match arg {
            Expr::Call { name, .. } if name == "borrow" => self.rewrite_expr(arg, scope, depth),
            Expr::Var(name) => {
                if scope.slots.get(name).is_some_and(|slot| slot.borrowed) {
                    Expr::Var(name.clone())
                } else {
                    Expr::Call {
                        name: "borrow".into(),
                        args: vec![Expr::Var(name.clone())],
                    }
                }
            }
            _ => {
                let rewritten = self.rewrite_expr(arg, scope, depth);
                Expr::Call {
                    name: "borrow".into(),
                    args: vec![rewritten],
                }
            }
        }
    }

    fn owner_tag_vec(&mut self, arg: &Expr, scope: &Scope, call: &str) -> Option<String> {
        match self.resolve_owner(arg, scope) {
            Some(owner) => match self.vec_term(&owner) {
                Some((tag, _)) => Some(tag),
                None => {
                    self.report(
                        "COL201",
                        format!(
                            "call `{call}` requires a POD Vector owner; payloads must be integers, bool, or plain C records thereof"
                        ),
                    );
                    None
                }
            },
            None => {
                self.report(
                    "COL202",
                    format!("call `{call}` has an undeterminable collection owner"),
                );
                None
            }
        }
    }

    fn owner_tag_map(&mut self, arg: &Expr, scope: &Scope, call: &str) -> Option<(String, String)> {
        match self.resolve_owner(arg, scope) {
            Some(owner) => match self.map_term(&owner) {
                Some((ktag, vtag, _, _)) => Some((ktag, vtag)),
                None => {
                    self.report(
                        "COL201",
                        format!(
                            "call `{call}` requires a POD Map owner; keys and values must be integers, bool, or plain C records thereof"
                        ),
                    );
                    None
                }
            },
            None => {
                self.report(
                    "COL202",
                    format!("call `{call}` has an undeterminable collection owner"),
                );
                None
            }
        }
    }

    fn rewrite_expr(&mut self, expr: &Expr, scope: &Scope, depth: usize) -> Expr {
        if depth > MAX_DEPTH {
            self.report(
                "COL208",
                "collection program exceeds supported nesting depth".into(),
            );
            return expr.clone();
        }
        match expr {
            Expr::Call { name, args } if is_canonical_call(name) => {
                self.rewrite_canonical(name, args, scope, depth)
            }
            Expr::Call { name, args } => {
                let borrowed = self.borrow_params(name);
                let mut rewritten: Vec<Expr> = Vec::with_capacity(args.len());
                for arg in args {
                    rewritten.push(self.rewrite_expr(arg, scope, depth + 1));
                }
                // Calls to known user operations: wrap owned slots passed to
                // `Borrow<...>` parameters with `borrow(...)`. Already-borrowed
                // spellings are forwarded as-is. Generated wrappers are
                // excluded: their calls are already rewritten.
                if let Some(borrowed) = borrowed.filter(|_| !name.starts_with(GEN_PREFIX)) {
                    for (index, rewrite) in rewritten.iter_mut().enumerate() {
                        if borrowed.get(index).copied().unwrap_or(false) {
                            let original = &args[index];
                            let forwarded = matches!(
                                original,
                                Expr::Call { name: callee, .. } if callee == "borrow"
                            ) || matches!(
                                original,
                                Expr::Var(var) if scope
                                    .slots
                                    .get(var)
                                    .is_some_and(|slot| slot.borrowed)
                            );
                            if !forwarded {
                                *rewrite = Expr::Call {
                                    name: "borrow".into(),
                                    args: vec![rewrite.clone()],
                                };
                            }
                        }
                    }
                }
                Expr::Call {
                    name: name.clone(),
                    args: rewritten,
                }
            }
            Expr::Field { base, field } => Expr::Field {
                base: Box::new(self.rewrite_expr(base, scope, depth + 1)),
                field: field.clone(),
            },
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(self.rewrite_expr(base, scope, depth + 1)),
                index: Box::new(self.rewrite_expr(index, scope, depth + 1)),
            },
            Expr::BinOp { op, left, right } => Expr::BinOp {
                op: *op,
                left: Box::new(self.rewrite_expr(left, scope, depth + 1)),
                right: Box::new(self.rewrite_expr(right, scope, depth + 1)),
            },
            Expr::Not(inner) => Expr::Not(Box::new(self.rewrite_expr(inner, scope, depth + 1))),
            Expr::Var(_) | Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) => {
                expr.clone()
            }
        }
    }

    /// Declared `Borrow<...>` parameter positions of a known user operation.
    /// Generated wrappers are excluded: their calls are already rewritten.
    fn borrow_params(&self, name: &str) -> Option<Vec<bool>> {
        self.op_params.get(name).map(|params| {
            params
                .iter()
                .map(|ty| matches!(generic_parts(ty), Some(("Borrow", _))))
                .collect()
        })
    }

    #[allow(clippy::too_many_lines)]
    fn rewrite_canonical(
        &mut self,
        name: &str,
        args: &[Expr],
        scope: &Scope,
        depth: usize,
    ) -> Expr {
        let fallback = Expr::Call {
            name: name.into(),
            args: args.to_vec(),
        };
        match name {
            "vector" => {
                if args.len() != 2 {
                    self.report(
                        "COL202",
                        format!("call `vector` expects 2 arguments, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some(Expr::Var(type_name)) = args.first() else {
                    self.report(
                        "COL202",
                        "call `vector` expects a type name and a capacity".into(),
                    );
                    return fallback;
                };
                let elem = TypeRef::Named(type_name.clone());
                let Some(pod) = checked_pod_top(&elem, &self.registry.entities) else {
                    self.report(
                        "COL201",
                        format!(
                            "unsupported vector element type {type_name}; payloads must be integers, bool, or plain C records thereof"
                        ),
                    );
                    return fallback;
                };
                let tag = pod_tag(&pod);
                self.vec_terms.entry(tag.clone()).or_insert(elem);
                let cap = self.rewrite_expr(&args[1], scope, depth + 1);
                Expr::Call {
                    name: format!("{GEN_PREFIX}VecNew_{tag}"),
                    args: vec![cap],
                }
            }
            "map" => {
                if args.len() != 3 {
                    self.report(
                        "COL202",
                        format!("call `map` expects 3 arguments, got {}", args.len()),
                    );
                    return fallback;
                }
                let (Some(Expr::Var(key)), Some(Expr::Var(value))) = (args.first(), args.get(1))
                else {
                    self.report(
                        "COL202",
                        "call `map` expects key/value type names and a capacity".into(),
                    );
                    return fallback;
                };
                let key_ty = TypeRef::Named(key.clone());
                let value_ty = TypeRef::Named(value.clone());
                let (Some(key_pod), Some(value_pod)) = (
                    checked_pod_top(&key_ty, &self.registry.entities),
                    checked_pod_top(&value_ty, &self.registry.entities),
                ) else {
                    self.report(
                        "COL201",
                        "unsupported map key/value type; keys and values must be integers, bool, or plain C records thereof".into(),
                    );
                    return fallback;
                };
                let ktag = pod_tag(&key_pod);
                let vtag = pod_tag(&value_pod);
                self.map_terms
                    .entry((ktag.clone(), vtag.clone()))
                    .or_insert((key_ty, value_ty));
                let cap = self.rewrite_expr(&args[2], scope, depth + 1);
                Expr::Call {
                    name: format!("{GEN_PREFIX}MapNew_{ktag}_{vtag}"),
                    args: vec![cap],
                }
            }
            "vector_drop" | "map_drop" => {
                if args.len() != 1 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 1 argument, got {}", args.len()),
                    );
                    return fallback;
                }
                let is_vector = name == "vector_drop";
                let tag = if is_vector {
                    self.owner_tag_vec(&args[0], scope, name)
                        .map(|tag| (tag, true))
                } else {
                    self.owner_tag_map(&args[0], scope, name)
                        .map(|(ktag, vtag)| (format!("{ktag}_{vtag}"), false))
                };
                let Some((tag, _)) = tag else {
                    return fallback;
                };
                if let Expr::Var(var) = &args[0] {
                    if scope.slots.get(var).is_some_and(|slot| slot.borrowed) {
                        self.report(
                            "COL204",
                            format!("call `{name}` cannot drop a borrowed slot `{var}`"),
                        );
                    }
                }
                let slot = self.rewrite_expr(&args[0], scope, depth + 1);
                Expr::Call {
                    name: if is_vector {
                        format!("{GEN_PREFIX}VecDrop_{tag}")
                    } else {
                        format!("{GEN_PREFIX}MapDrop_{tag}")
                    },
                    args: vec![slot],
                }
            }
            "vector_len" | "vector_capacity" => {
                if args.len() != 1 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 1 argument, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some(tag) = self.owner_tag_vec(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                Expr::Call {
                    name: if name == "vector_len" {
                        format!("{GEN_PREFIX}VecLen_{tag}")
                    } else {
                        format!("{GEN_PREFIX}VecCap_{tag}")
                    },
                    args: vec![slot],
                }
            }
            "map_len" | "map_capacity" => {
                if args.len() != 1 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 1 argument, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some((ktag, vtag)) = self.owner_tag_map(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                Expr::Call {
                    name: if name == "map_len" {
                        format!("{GEN_PREFIX}MapLen_{ktag}_{vtag}")
                    } else {
                        format!("{GEN_PREFIX}MapCap_{ktag}_{vtag}")
                    },
                    args: vec![slot],
                }
            }
            "vector_reserve" => {
                if args.len() != 2 {
                    self.report(
                        "COL202",
                        format!(
                            "call `vector_reserve` expects 2 arguments, got {}",
                            args.len()
                        ),
                    );
                    return fallback;
                }
                let Some(tag) = self.owner_tag_vec(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                let cap = self.rewrite_expr(&args[1], scope, depth + 1);
                Expr::Call {
                    name: format!("{GEN_PREFIX}VecReserve_{tag}"),
                    args: vec![slot, cap],
                }
            }
            "vector_push" | "vector_get" => {
                if args.len() != 2 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 2 arguments, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some(tag) = self.owner_tag_vec(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                let value = self.rewrite_expr(&args[1], scope, depth + 1);
                Expr::Call {
                    name: if name == "vector_push" {
                        format!("{GEN_PREFIX}VecPush_{tag}")
                    } else {
                        format!("{GEN_PREFIX}VecGet_{tag}")
                    },
                    args: vec![slot, value],
                }
            }
            "vector_set" | "map_insert" => {
                if args.len() != 3 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 3 arguments, got {}", args.len()),
                    );
                    return fallback;
                }
                let (slot, generated) = if name == "vector_set" {
                    let Some(tag) = self.owner_tag_vec(&args[0], scope, name) else {
                        return fallback;
                    };
                    (
                        self.borrow_arg(&args[0], scope, depth + 1),
                        format!("{GEN_PREFIX}VecSet_{tag}"),
                    )
                } else {
                    let Some((ktag, vtag)) = self.owner_tag_map(&args[0], scope, name) else {
                        return fallback;
                    };
                    (
                        self.borrow_arg(&args[0], scope, depth + 1),
                        format!("{GEN_PREFIX}MapInsert_{ktag}_{vtag}"),
                    )
                };
                let first = self.rewrite_expr(&args[1], scope, depth + 1);
                let second = self.rewrite_expr(&args[2], scope, depth + 1);
                Expr::Call {
                    name: generated,
                    args: vec![slot, first, second],
                }
            }
            "vector_pop" => {
                if args.len() != 1 {
                    self.report(
                        "COL202",
                        format!("call `vector_pop` expects 1 argument, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some(tag) = self.owner_tag_vec(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                Expr::Call {
                    name: format!("{GEN_PREFIX}VecPop_{tag}"),
                    args: vec![slot],
                }
            }
            "map_reserve" | "map_get" | "map_remove" | "map_contains" => {
                if args.len() != 2 {
                    self.report(
                        "COL202",
                        format!("call `{name}` expects 2 arguments, got {}", args.len()),
                    );
                    return fallback;
                }
                let Some((ktag, vtag)) = self.owner_tag_map(&args[0], scope, name) else {
                    return fallback;
                };
                let slot = self.borrow_arg(&args[0], scope, depth + 1);
                let key = self.rewrite_expr(&args[1], scope, depth + 1);
                Expr::Call {
                    name: match name {
                        "map_reserve" => format!("{GEN_PREFIX}MapReserve_{ktag}_{vtag}"),
                        "map_get" => format!("{GEN_PREFIX}MapGet_{ktag}_{vtag}"),
                        "map_remove" => format!("{GEN_PREFIX}MapRemove_{ktag}_{vtag}"),
                        _ => format!("{GEN_PREFIX}MapContains_{ktag}_{vtag}"),
                    },
                    args: vec![slot, key],
                }
            }
            _ => fallback,
        }
    }
}

// ---------------------------------------------------------------------------
// Generated items: records, zero/pack helpers, typed wrappers.
// ---------------------------------------------------------------------------

impl<'a> Pass<'a> {
    fn emit_record(
        &mut self,
        out: &mut Vec<Item>,
        name: String,
        fields: Vec<(String, TypeRef)>,
        span: &Span,
    ) {
        if !self.emitted_records.insert(name.clone()) {
            return;
        }
        out.push(Item::Entity(sal_syntax::EntityDecl {
            name,
            span: span.clone(),
            fields: fields
                .into_iter()
                .map(|(name, ty)| sal_syntax::FieldDecl {
                    name,
                    ty,
                    span: span.clone(),
                })
                .collect(),
            invariants: Vec::new(),
            c_layout: true,
            json: Default::default(),
            iteration: None,
            generated: true,
        }));
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_op(
        &mut self,
        out: &mut Vec<Item>,
        name: String,
        params: Vec<(String, TypeRef)>,
        returns: Option<TypeRef>,
        effects: Vec<&str>,
        span: &Span,
        body: Vec<Stmt>,
    ) {
        if !self.emitted_ops.insert(name.clone()) {
            return;
        }
        out.push(Item::Operation(OperationDecl {
            name,
            span: span.clone(),
            accepts: params
                .into_iter()
                .map(|(name, ty)| sal_syntax::ParamDecl { name, ty })
                .collect(),
            returns,
            effects: effects.into_iter().map(str::to_owned).collect(),
            requires: Vec::new(),
            ensures: Vec::new(),
            ownership: Default::default(),
            generated: true,
            responds_literal: None,
            c_export: None,
            c_import: None,
            body: vec![Stmt::Unsafe { body }],
        }));
    }

    fn exit_group(&self, code: i64) -> Stmt {
        Stmt::ExprStmt(Expr::Call {
            name: "syscall".into(),
            args: vec![
                Expr::Int(EXIT_GROUP),
                Expr::Int(code),
                Expr::Int(0),
                Expr::Int(0),
                Expr::Int(0),
                Expr::Int(0),
                Expr::Int(0),
            ],
        })
    }

    fn usize_lit(value: i64) -> Expr {
        Expr::Call {
            name: "usize".into(),
            args: vec![Expr::Int(value)],
        }
    }

    fn size_of(ty: &str) -> Expr {
        Expr::Call {
            name: "size_of".into(),
            args: vec![Expr::Var(ty.into())],
        }
    }

    fn probe_found(probe: Expr) -> Expr {
        Expr::Field {
            base: Box::new(probe),
            field: "found".into(),
        }
    }

    fn borrow_of(var: &str) -> Expr {
        Expr::Call {
            name: "borrow".into(),
            args: vec![Expr::Var(var.into())],
        }
    }

    /// `base + offset`: the only address form native lowering accepts for a
    /// `Borrow` word (offset 0 is spelled out, never a bare `base`).
    fn slot_addr(base: Expr, offset: i64) -> Expr {
        Expr::BinOp {
            op: sal_syntax::BinOp::Add,
            left: Box::new(base),
            right: Box::new(Expr::Int(offset)),
        }
    }

    fn slot_word(base: Expr, offset: i64) -> Expr {
        Expr::Call {
            name: "load64".into(),
            args: vec![Self::slot_addr(base, offset)],
        }
    }

    /// Zero value expression for one POD type.
    fn zero_expr(&self, ty: &TypeRef) -> Expr {
        match ty {
            TypeRef::Named(name) if name == "bool" => Expr::Bool(false),
            TypeRef::Named(name) if is_integer_name(name) => Expr::Int(0),
            TypeRef::Named(name) => {
                if let Some((true, fields)) = self.registry.entities.get(name) {
                    let args = fields
                        .iter()
                        .map(|(_, field)| self.zero_expr(field))
                        .collect();
                    Expr::Call {
                        name: name.clone(),
                        args,
                    }
                } else {
                    Expr::Int(0)
                }
            }
            TypeRef::Generic { .. } => Expr::Int(0),
        }
    }

    /// Flattened scalar leaf segments of one key type in declaration
    /// order: each entry is the field-projection path from the key value,
    /// the scalar width, and whether the leaf is `bool`. Records
    /// concatenate their fields; padding is never covered because no C
    /// offsets are ever read.
    #[allow(clippy::type_complexity)]
    fn key_segments(&self, ty: &TypeRef) -> Option<Vec<(Vec<String>, usize, bool)>> {
        match ty {
            TypeRef::Named(name) => {
                if let Some(width) = scalar_width(name) {
                    return Some(vec![(Vec::new(), width, name == "bool")]);
                }
                let (c_layout, fields) = self.registry.entities.get(name)?;
                if !c_layout {
                    return None;
                }
                let mut segments = Vec::new();
                for (field_name, field_ty) in fields {
                    for (mut path, width, is_bool) in self.key_segments(field_ty)? {
                        let mut full = vec![field_name.clone()];
                        full.append(&mut path);
                        segments.push((full, width, is_bool));
                    }
                }
                Some(segments)
            }
            TypeRef::Generic { .. } => None,
        }
    }

    /// Signedness of the leaf at `path` inside `root`: unsigned exactly
    /// when the resolved named type is `bool` or starts with `u`.
    fn leaf_is_unsigned(&self, path: &[String], root: &TypeRef) -> bool {
        let mut current = root;
        for field in path {
            let TypeRef::Named(entity) = current else {
                return false;
            };
            let Some((_, fields)) = self.registry.entities.get(entity) else {
                return false;
            };
            let Some((_, field_ty)) = fields.iter().find(|(name, _)| name == field) else {
                return false;
            };
            current = field_ty;
        }
        match current {
            TypeRef::Named(name) => name == "bool" || name.starts_with('u'),
            TypeRef::Generic { .. } => false,
        }
    }

    /// Checked projection of one leaf value: field path from `base`.
    /// Bool leaves normalize to 0/1 at the call site; integer leaves pass
    /// through unchanged (sign preserved, decomposition reinterprets bits).
    fn leaf_expr(base: Expr, path: &[String]) -> Expr {
        let mut expr = base;
        for field in path {
            expr = Expr::Field {
                base: Box::new(expr),
                field: field.clone(),
            };
        }
        expr
    }

    /// Emit every collected instance: records, helpers, then wrappers.
    /// Deterministic tag order throughout.
    fn emit_instances(&mut self, out: &mut Vec<Item>, span: &Span) {
        let vec_terms: Vec<(String, TypeRef)> = self
            .vec_terms
            .iter()
            .map(|(tag, ty)| (tag.clone(), ty.clone()))
            .collect();
        let map_terms: Vec<((String, String), (TypeRef, TypeRef))> = self
            .map_terms
            .iter()
            .map(|(tags, tys)| (tags.clone(), tys.clone()))
            .collect();
        for (tag, elem) in &vec_terms {
            let elem = elem.clone();
            self.emit_record(
                out,
                vec_name(tag),
                vec![
                    ("data".into(), TypeRef::Named("usize".into())),
                    ("len".into(), TypeRef::Named("usize".into())),
                    ("cap".into(), TypeRef::Named("usize".into())),
                ],
                span,
            );
            self.emit_record(
                out,
                box_name(tag),
                vec![("value".into(), elem.clone())],
                span,
            );
            self.emit_record(
                out,
                res_name(tag),
                vec![
                    ("found".into(), TypeRef::Named("bool".into())),
                    ("value".into(), elem.clone()),
                ],
                span,
            );
            self.emit_zero(out, tag, &elem, span);
        }
        for ((ktag, vtag), (key, value)) in &map_terms {
            let key = key.clone();
            let value = value.clone();
            self.emit_record(
                out,
                map_name(ktag, vtag),
                vec![
                    ("data".into(), TypeRef::Named("usize".into())),
                    ("len".into(), TypeRef::Named("usize".into())),
                    ("cap".into(), TypeRef::Named("usize".into())),
                    ("used".into(), TypeRef::Named("usize".into())),
                ],
                span,
            );
            self.emit_keybuf(out, ktag, &key, span);
            self.emit_pack(out, ktag, &key, span);
            self.emit_record(
                out,
                box_name(vtag),
                vec![("value".into(), value.clone())],
                span,
            );
            self.emit_record(
                out,
                res_name(vtag),
                vec![
                    ("found".into(), TypeRef::Named("bool".into())),
                    ("value".into(), value.clone()),
                ],
                span,
            );
            self.emit_zero(out, vtag, &value, span);
        }
        for (tag, elem) in &vec_terms {
            self.emit_vec_ops(out, tag, elem, span);
        }
        for ((ktag, vtag), (key, value)) in &map_terms {
            self.emit_map_ops(out, ktag, vtag, key, value, span);
        }
    }

    fn emit_zero(&mut self, out: &mut Vec<Item>, tag: &str, elem: &TypeRef, span: &Span) {
        let body = vec![Stmt::Return(self.zero_expr(elem))];
        self.emit_op(
            out,
            zero_name(tag),
            Vec::new(),
            Some(elem.clone()),
            vec!["Pure"],
            span,
            body,
        );
    }

    fn emit_keybuf(&mut self, out: &mut Vec<Item>, ktag: &str, key: &TypeRef, span: &Span) {
        let count = self
            .key_segments(key)
            .map(|segments| segments.iter().map(|(_, width, _)| width).sum::<usize>())
            .unwrap_or(1)
            .max(1);
        let fields = (0..count)
            .map(|index| (format!("k{index}"), TypeRef::Named("u8".into())))
            .collect();
        self.emit_record(out, keybuf_name(ktag), fields, span);
    }

    /// Canonical field-wise key packing: every scalar segment is loaded from
    /// its C offset inside a single-field box, so padding bytes are never
    /// read and never affect hashing or equality.
    fn emit_pack(&mut self, out: &mut Vec<Item>, ktag: &str, key: &TypeRef, span: &Span) {
        let Some(segments) = self.key_segments(key) else {
            return;
        };
        let keybuf = keybuf_name(ktag);
        // Per-leaf temporaries: `t{leaf}` holds the scalar leaf value,
        // `m{leaf}` its unsigned magnitude for byte decomposition.
        let mut body: Vec<Stmt> = Vec::new();
        let mut args: Vec<Expr> = Vec::new();
        let mut byte = 0_usize;
        for (leaf, (path, width, is_bool)) in segments.iter().enumerate() {
            let leaf_value = Self::leaf_expr(Expr::Var("key".into()), path);
            body.push(Stmt::Let {
                name: format!("t{leaf}"),
                mutable: false,
                expr: leaf_value,
            });
            if *width == 1 && *is_bool {
                let name = format!("b{byte}");
                body.push(Stmt::Let {
                    name: name.clone(),
                    mutable: true,
                    expr: Expr::Call {
                        name: "u8".into(),
                        args: vec![Expr::Int(0)],
                    },
                });
                body.push(Stmt::If {
                    cond: Expr::Var(format!("t{leaf}")),
                    then: vec![Stmt::Assign {
                        name: name.clone(),
                        expr: Expr::Call {
                            name: "u8".into(),
                            args: vec![Expr::Int(1)],
                        },
                    }],
                    else_: vec![],
                });
                args.push(Expr::Var(name));
                byte += 1;
            } else if *width == 1 {
                let name = format!("b{byte}");
                // Signed 8-bit leaves reinterpret bits; unsigned copy directly.
                let scalar = if self.leaf_is_unsigned(path, key) {
                    Expr::Call {
                        name: "u8".into(),
                        args: vec![Expr::Var(format!("t{leaf}"))],
                    }
                } else {
                    Expr::Call {
                        name: "bits_as".into(),
                        args: vec![Expr::Var("u8".into()), Expr::Var(format!("t{leaf}"))],
                    }
                };
                body.push(Stmt::Let {
                    name: name.clone(),
                    mutable: false,
                    expr: scalar,
                });
                args.push(Expr::Var(name));
                byte += 1;
            } else {
                let uty = match width {
                    2 => "u16",
                    4 => "u32",
                    _ => "u64",
                };
                // Signed leaves reinterpret bits (two's complement); unsigned
                // leaves convert directly. `bits_as` traps only on width
                // mismatch, never on negative values.
                let signed = !self.leaf_is_unsigned(path, key);
                let magnitude = if signed {
                    Expr::Call {
                        name: "bits_as".into(),
                        args: vec![Expr::Var(uty.into()), Expr::Var(format!("t{leaf}"))],
                    }
                } else {
                    Expr::Call {
                        name: uty.into(),
                        args: vec![Expr::Var(format!("t{leaf}"))],
                    }
                };
                body.push(Stmt::Let {
                    name: format!("m{leaf}"),
                    mutable: true,
                    expr: magnitude,
                });
                for index in 0..*width {
                    let name = format!("b{byte}");
                    body.push(Stmt::Let {
                        name: name.clone(),
                        mutable: false,
                        expr: Expr::Call {
                            name: "u8".into(),
                            args: vec![Expr::BinOp {
                                op: sal_syntax::BinOp::Rem,
                                left: Box::new(Expr::Var(format!("m{leaf}"))),
                                right: Box::new(Expr::Call {
                                    name: uty.into(),
                                    args: vec![Expr::Int(256)],
                                }),
                            }],
                        },
                    });
                    args.push(Expr::Var(name));
                    byte += 1;
                    if index + 1 < *width {
                        body.push(Stmt::Assign {
                            name: format!("m{leaf}"),
                            expr: Expr::BinOp {
                                op: sal_syntax::BinOp::Div,
                                left: Box::new(Expr::Var(format!("m{leaf}"))),
                                right: Box::new(Expr::Call {
                                    name: uty.into(),
                                    args: vec![Expr::Int(256)],
                                }),
                            },
                        });
                    }
                }
            }
        }
        body.push(Stmt::Return(Expr::Call { name: keybuf, args }));
        self.emit_op(
            out,
            pack_name(ktag),
            vec![("key".into(), key.clone())],
            Some(TypeRef::Named(keybuf_name(ktag))),
            vec!["Pure"],
            span,
            body,
        );
    }

    fn width_of(&self, tag: &str) -> Expr {
        Self::size_of(&box_name(tag))
    }

    fn emit_vec_ops(&mut self, out: &mut Vec<Item>, tag: &str, elem: &TypeRef, span: &Span) {
        let elem = elem.clone();
        let vec_ty = TypeRef::Named(vec_name(tag));
        let borrowed = TypeRef::Generic {
            name: "Borrow".into(),
            args: vec![vec_ty.clone()],
        };
        let res_ty = TypeRef::Named(res_name(tag));
        let box_ty = box_name(tag);
        let width = self.width_of(tag);
        // Constructor: zero capacity allocates nothing; any other allocation
        // failure exits nonzero (70).
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecNew_{tag}"),
            vec![("capacity".into(), TypeRef::Named("usize".into()))],
            Some(vec_ty.clone()),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "data".into(),
                    mutable: true,
                    expr: Self::usize_lit(0),
                },
                Stmt::If {
                    cond: Expr::BinOp {
                        op: sal_syntax::BinOp::Ne,
                        left: Box::new(Expr::Var("capacity".into())),
                        right: Box::new(Self::usize_lit(0)),
                    },
                    then: vec![
                        Stmt::Unsafe {
                            body: vec![Stmt::Assign {
                                name: "data".into(),
                                expr: Expr::Call {
                                    name: "CollectionVecNew".into(),
                                    args: vec![width.clone(), Expr::Var("capacity".into())],
                                },
                            }],
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Eq,
                                left: Box::new(Expr::Var("data".into())),
                                right: Box::new(Self::usize_lit(0)),
                            },
                            then: vec![self.exit_group(70)],
                            else_: vec![],
                        },
                    ],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: vec_name(tag),
                    args: vec![
                        Expr::Var("data".into()),
                        Self::usize_lit(0),
                        Expr::Var("capacity".into()),
                    ],
                }),
            ],
        );
        // Drop consumes the metadata record and releases the element area.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecDrop_{tag}"),
            vec![("slot".into(), vec_ty.clone())],
            None,
            vec!["SystemCall"],
            span,
            vec![Stmt::Unsafe {
                body: vec![Stmt::ExprStmt(Expr::Call {
                    name: "CollectionVecFree".into(),
                    args: vec![
                        Expr::Field {
                            base: Box::new(Expr::Var("slot".into())),
                            field: "data".into(),
                        },
                        Expr::BinOp {
                            op: sal_syntax::BinOp::Mul,
                            left: Box::new(Expr::Field {
                                base: Box::new(Expr::Var("slot".into())),
                                field: "cap".into(),
                            }),
                            right: Box::new(width.clone()),
                        },
                    ],
                })],
            }],
        );
        // Length / capacity read the original slot through the borrow.
        for (suffix, offset) in [("Len", 8), ("Cap", 16)] {
            self.emit_op(
                out,
                format!("{GEN_PREFIX}Vec{suffix}_{tag}"),
                vec![("slot".into(), borrowed.clone())],
                Some(TypeRef::Named("usize".into())),
                vec!["Pure"],
                span,
                vec![Stmt::Unsafe {
                    body: vec![Stmt::Return(Self::slot_word(
                        Self::borrow_of("slot"),
                        offset,
                    ))],
                }],
            );
        }
        // Reserve grows exactly to the requested capacity. Failure leaves
        // the prior table intact and reports -12.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecReserve_{tag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("capacity".into(), TypeRef::Named("usize".into())),
            ],
            Some(TypeRef::Named("i64".into())),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "status".into(),
                    mutable: true,
                    expr: Expr::Int(0),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Let {
                            name: "cap".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 16),
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Gt,
                                left: Box::new(Expr::Var("capacity".into())),
                                right: Box::new(Expr::Var("cap".into())),
                            },
                            then: vec![
                                Stmt::Let {
                                    name: "grown".into(),
                                    mutable: false,
                                    expr: Expr::Call {
                                        name: "CollectionVecGrow".into(),
                                        args: vec![
                                            Self::slot_word(Expr::Var("base".into()), 0),
                                            width.clone(),
                                            Self::slot_word(Expr::Var("base".into()), 8),
                                            Expr::Var("cap".into()),
                                            Expr::Var("capacity".into()),
                                        ],
                                    },
                                },
                                Stmt::If {
                                    cond: Expr::BinOp {
                                        op: sal_syntax::BinOp::Eq,
                                        left: Box::new(Expr::Field {
                                            base: Box::new(Expr::Var("grown".into())),
                                            field: "status".into(),
                                        }),
                                        right: Box::new(Expr::Int(0)),
                                    },
                                    then: vec![
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Self::slot_addr(Expr::Var("base".into()), 0),
                                                Expr::Field {
                                                    base: Box::new(Expr::Var("grown".into())),
                                                    field: "data".into(),
                                                },
                                            ],
                                        }),
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Expr::BinOp {
                                                    op: sal_syntax::BinOp::Add,
                                                    left: Box::new(Expr::Var("base".into())),
                                                    right: Box::new(Expr::Int(16)),
                                                },
                                                Expr::Var("capacity".into()),
                                            ],
                                        }),
                                    ],
                                    else_: vec![Stmt::Assign {
                                        name: "status".into(),
                                        expr: Expr::Int(-12),
                                    }],
                                },
                            ],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::Return(Expr::Var("status".into())),
            ],
        );
        // Push appends at the tail, growing geometrically (at least 4).
        // Failure leaves prior contents intact and reports -12.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecPush_{tag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("element".into(), elem.clone()),
            ],
            Some(TypeRef::Named("i64".into())),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_ty.clone(),
                        args: vec![Expr::Var("element".into())],
                    },
                },
                Stmt::Let {
                    name: "status".into(),
                    mutable: true,
                    expr: Expr::Int(-12),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Let {
                            name: "len".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 8),
                        },
                        Stmt::Let {
                            name: "cap".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 16),
                        },
                        Stmt::Let {
                            name: "target".into(),
                            mutable: true,
                            expr: Self::slot_word(Expr::Var("base".into()), 0),
                        },
                        Stmt::Let {
                            name: "ready".into(),
                            mutable: true,
                            expr: Expr::Bool(false),
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Eq,
                                left: Box::new(Expr::Var("len".into())),
                                right: Box::new(Expr::Var("cap".into())),
                            },
                            then: vec![Stmt::If {
                                cond: Expr::BinOp {
                                    op: sal_syntax::BinOp::Le,
                                    left: Box::new(Expr::Var("cap".into())),
                                    right: Box::new(Self::usize_lit(2305843009213693951)),
                                },
                                then: vec![
                                    Stmt::Let {
                                        name: "next".into(),
                                        mutable: true,
                                        expr: Expr::BinOp {
                                            op: sal_syntax::BinOp::Mul,
                                            left: Box::new(Expr::Var("cap".into())),
                                            right: Box::new(Self::usize_lit(2)),
                                        },
                                    },
                                    Stmt::If {
                                        cond: Expr::BinOp {
                                            op: sal_syntax::BinOp::Lt,
                                            left: Box::new(Expr::Var("next".into())),
                                            right: Box::new(Self::usize_lit(4)),
                                        },
                                        then: vec![Stmt::Assign {
                                            name: "next".into(),
                                            expr: Self::usize_lit(4),
                                        }],
                                        else_: vec![],
                                    },
                                    Stmt::Let {
                                        name: "grown".into(),
                                        mutable: false,
                                        expr: Expr::Call {
                                            name: "CollectionVecGrow".into(),
                                            args: vec![
                                                Expr::Var("target".into()),
                                                width.clone(),
                                                Expr::Var("len".into()),
                                                Expr::Var("cap".into()),
                                                Expr::Var("next".into()),
                                            ],
                                        },
                                    },
                                    Stmt::If {
                                        cond: Expr::BinOp {
                                            op: sal_syntax::BinOp::Eq,
                                            left: Box::new(Expr::Field {
                                                base: Box::new(Expr::Var("grown".into())),
                                                field: "status".into(),
                                            }),
                                            right: Box::new(Expr::Int(0)),
                                        },
                                        then: vec![
                                            Stmt::ExprStmt(Expr::Call {
                                                name: "store64".into(),
                                                args: vec![
                                                    Self::slot_addr(Expr::Var("base".into()), 0),
                                                    Expr::Field {
                                                        base: Box::new(Expr::Var("grown".into())),
                                                        field: "data".into(),
                                                    },
                                                ],
                                            }),
                                            Stmt::ExprStmt(Expr::Call {
                                                name: "store64".into(),
                                                args: vec![
                                                    Expr::BinOp {
                                                        op: sal_syntax::BinOp::Add,
                                                        left: Box::new(Expr::Var("base".into())),
                                                        right: Box::new(Expr::Int(16)),
                                                    },
                                                    Expr::Var("next".into()),
                                                ],
                                            }),
                                            Stmt::Assign {
                                                name: "target".into(),
                                                expr: Expr::Field {
                                                    base: Box::new(Expr::Var("grown".into())),
                                                    field: "data".into(),
                                                },
                                            },
                                            Stmt::Assign {
                                                name: "ready".into(),
                                                expr: Expr::Bool(true),
                                            },
                                        ],
                                        else_: vec![],
                                    },
                                ],
                                else_: vec![],
                            }],
                            else_: vec![Stmt::Assign {
                                name: "ready".into(),
                                expr: Expr::Bool(true),
                            }],
                        },
                        Stmt::If {
                            cond: Expr::Var("ready".into()),
                            then: vec![
                                Stmt::ExprStmt(Expr::Call {
                                    name: "CollectionVecPushTail".into(),
                                    args: vec![
                                        Expr::Var("target".into()),
                                        width.clone(),
                                        Expr::Var("len".into()),
                                        Expr::Call {
                                            name: "address".into(),
                                            args: vec![Expr::Var("cell".into())],
                                        },
                                    ],
                                }),
                                Stmt::ExprStmt(Expr::Call {
                                    name: "store64".into(),
                                    args: vec![
                                        Expr::BinOp {
                                            op: sal_syntax::BinOp::Add,
                                            left: Box::new(Expr::Var("base".into())),
                                            right: Box::new(Expr::Int(8)),
                                        },
                                        Expr::BinOp {
                                            op: sal_syntax::BinOp::Add,
                                            left: Box::new(Expr::Var("len".into())),
                                            right: Box::new(Self::usize_lit(1)),
                                        },
                                    ],
                                }),
                                Stmt::Assign {
                                    name: "status".into(),
                                    expr: Expr::Int(0),
                                },
                            ],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::Return(Expr::Var("status".into())),
            ],
        );
        // Get copies the element image to a box; missing stays typed.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecGet_{tag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("index".into(), TypeRef::Named("usize".into())),
            ],
            Some(res_ty.clone()),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_ty.clone(),
                        args: vec![Expr::Call {
                            name: zero_name(tag),
                            args: vec![],
                        }],
                    },
                },
                Stmt::Let {
                    name: "found".into(),
                    mutable: true,
                    expr: Expr::Bool(false),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Assign {
                            name: "found".into(),
                            expr: Expr::Call {
                                name: "CollectionVecGet".into(),
                                args: vec![
                                    Self::slot_word(Expr::Var("base".into()), 0),
                                    width.clone(),
                                    Self::slot_word(Expr::Var("base".into()), 8),
                                    Expr::Var("index".into()),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("cell".into())],
                                    },
                                ],
                            },
                        },
                    ],
                },
                Stmt::If {
                    cond: Expr::Var("found".into()),
                    then: vec![Stmt::Return(Expr::Call {
                        name: res_name(tag),
                        args: vec![
                            Expr::Bool(true),
                            Expr::Field {
                                base: Box::new(Expr::Var("cell".into())),
                                field: "value".into(),
                            },
                        ],
                    })],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: res_name(tag),
                    args: vec![
                        Expr::Bool(false),
                        Expr::Field {
                            base: Box::new(Expr::Var("cell".into())),
                            field: "value".into(),
                        },
                    ],
                }),
            ],
        );
        // Set overwrites in place; out of range reports -22.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecSet_{tag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("index".into(), TypeRef::Named("usize".into())),
                ("value".into(), elem.clone()),
            ],
            Some(TypeRef::Named("i64".into())),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_ty.clone(),
                        args: vec![Expr::Var("value".into())],
                    },
                },
                Stmt::Let {
                    name: "status".into(),
                    mutable: true,
                    expr: Expr::Int(-22),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Assign {
                            name: "status".into(),
                            expr: Expr::Call {
                                name: "CollectionVecSet".into(),
                                args: vec![
                                    Self::slot_word(Expr::Var("base".into()), 0),
                                    width.clone(),
                                    Self::slot_word(Expr::Var("base".into()), 8),
                                    Expr::Var("index".into()),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("cell".into())],
                                    },
                                ],
                            },
                        },
                    ],
                },
                Stmt::Return(Expr::Var("status".into())),
            ],
        );
        // Pop copies the tail image out and publishes `len - 1`.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}VecPop_{tag}"),
            vec![("slot".into(), borrowed.clone())],
            Some(res_ty.clone()),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_ty.clone(),
                        args: vec![Expr::Call {
                            name: zero_name(tag),
                            args: vec![],
                        }],
                    },
                },
                Stmt::Let {
                    name: "found".into(),
                    mutable: true,
                    expr: Expr::Bool(false),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Let {
                            name: "len".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 8),
                        },
                        Stmt::Assign {
                            name: "found".into(),
                            expr: Expr::Call {
                                name: "CollectionVecPopTail".into(),
                                args: vec![
                                    Self::slot_word(Expr::Var("base".into()), 0),
                                    width.clone(),
                                    Expr::Var("len".into()),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("cell".into())],
                                    },
                                ],
                            },
                        },
                        Stmt::If {
                            cond: Expr::Var("found".into()),
                            then: vec![Stmt::ExprStmt(Expr::Call {
                                name: "store64".into(),
                                args: vec![
                                    Expr::BinOp {
                                        op: sal_syntax::BinOp::Add,
                                        left: Box::new(Expr::Var("base".into())),
                                        right: Box::new(Expr::Int(8)),
                                    },
                                    Expr::BinOp {
                                        op: sal_syntax::BinOp::Sub,
                                        left: Box::new(Expr::Var("len".into())),
                                        right: Box::new(Self::usize_lit(1)),
                                    },
                                ],
                            })],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::If {
                    cond: Expr::Var("found".into()),
                    then: vec![Stmt::Return(Expr::Call {
                        name: res_name(tag),
                        args: vec![
                            Expr::Bool(true),
                            Expr::Field {
                                base: Box::new(Expr::Var("cell".into())),
                                field: "value".into(),
                            },
                        ],
                    })],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: res_name(tag),
                    args: vec![
                        Expr::Bool(false),
                        Expr::Field {
                            base: Box::new(Expr::Var("cell".into())),
                            field: "value".into(),
                        },
                    ],
                }),
            ],
        );
    }

    fn emit_map_ops(
        &mut self,
        out: &mut Vec<Item>,
        ktag: &str,
        vtag: &str,
        key: &TypeRef,
        value: &TypeRef,
        span: &Span,
    ) {
        let key = key.clone();
        let value = value.clone();
        let map_ty = TypeRef::Named(map_name(ktag, vtag));
        let borrowed = TypeRef::Generic {
            name: "Borrow".into(),
            args: vec![map_ty.clone()],
        };
        let res_ty = TypeRef::Named(res_name(vtag));
        let key_width = Self::size_of(&keybuf_name(ktag));
        let val_width = Self::size_of(&box_name(vtag));
        let stride = Expr::BinOp {
            op: sal_syntax::BinOp::Add,
            left: Box::new(Expr::BinOp {
                op: sal_syntax::BinOp::Add,
                left: Box::new(Self::usize_lit(1)),
                right: Box::new(key_width.clone()),
            }),
            right: Box::new(val_width.clone()),
        };
        // Constructor: zero capacity allocates nothing; any other allocation
        // failure exits nonzero (70). The fresh mapping is zeroed, so every
        // slot starts empty.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapNew_{ktag}_{vtag}"),
            vec![("capacity".into(), TypeRef::Named("usize".into()))],
            Some(map_ty.clone()),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "data".into(),
                    mutable: true,
                    expr: Self::usize_lit(0),
                },
                Stmt::If {
                    cond: Expr::BinOp {
                        op: sal_syntax::BinOp::Ne,
                        left: Box::new(Expr::Var("capacity".into())),
                        right: Box::new(Self::usize_lit(0)),
                    },
                    then: vec![
                        Stmt::Unsafe {
                            body: vec![Stmt::Assign {
                                name: "data".into(),
                                expr: Expr::Call {
                                    name: "CollectionVecNew".into(),
                                    args: vec![stride.clone(), Expr::Var("capacity".into())],
                                },
                            }],
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Eq,
                                left: Box::new(Expr::Var("data".into())),
                                right: Box::new(Self::usize_lit(0)),
                            },
                            then: vec![self.exit_group(70)],
                            else_: vec![],
                        },
                    ],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: map_name(ktag, vtag),
                    args: vec![
                        Expr::Var("data".into()),
                        Self::usize_lit(0),
                        Expr::Var("capacity".into()),
                        Self::usize_lit(0),
                    ],
                }),
            ],
        );
        // Drop consumes the metadata record and releases the table.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapDrop_{ktag}_{vtag}"),
            vec![("slot".into(), map_ty.clone())],
            None,
            vec!["SystemCall"],
            span,
            vec![Stmt::Unsafe {
                body: vec![Stmt::ExprStmt(Expr::Call {
                    name: "CollectionVecFree".into(),
                    args: vec![
                        Expr::Field {
                            base: Box::new(Expr::Var("slot".into())),
                            field: "data".into(),
                        },
                        Expr::BinOp {
                            op: sal_syntax::BinOp::Mul,
                            left: Box::new(Expr::Field {
                                base: Box::new(Expr::Var("slot".into())),
                                field: "cap".into(),
                            }),
                            right: Box::new(stride.clone()),
                        },
                    ],
                })],
            }],
        );
        // Length / capacity read the original slot through the borrow.
        for (suffix, offset) in [("Len", 8), ("Cap", 16)] {
            self.emit_op(
                out,
                format!("{GEN_PREFIX}Map{suffix}_{ktag}_{vtag}"),
                vec![("slot".into(), borrowed.clone())],
                Some(TypeRef::Named("usize".into())),
                vec!["Pure"],
                span,
                vec![Stmt::Unsafe {
                    body: vec![Stmt::Return(Self::slot_word(
                        Self::borrow_of("slot"),
                        offset,
                    ))],
                }],
            );
        }
        // Reserve rehashes to exactly the requested slot count, dropping
        // tombstones. Failure leaves the prior table intact (-12).
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapReserve_{ktag}_{vtag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("capacity".into(), TypeRef::Named("usize".into())),
            ],
            Some(TypeRef::Named("i64".into())),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "status".into(),
                    mutable: true,
                    expr: Expr::Int(0),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Let {
                            name: "cap".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 16),
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Gt,
                                left: Box::new(Expr::Var("capacity".into())),
                                right: Box::new(Expr::Var("cap".into())),
                            },
                            then: vec![
                                Stmt::Let {
                                    name: "fresh".into(),
                                    mutable: false,
                                    expr: Expr::Call {
                                        name: "CollectionMapRehash".into(),
                                        args: vec![
                                            Self::slot_word(Expr::Var("base".into()), 0),
                                            key_width.clone(),
                                            val_width.clone(),
                                            Expr::Var("cap".into()),
                                            Expr::Var("capacity".into()),
                                        ],
                                    },
                                },
                                Stmt::If {
                                    cond: Expr::BinOp {
                                        op: sal_syntax::BinOp::Eq,
                                        left: Box::new(Expr::Field {
                                            base: Box::new(Expr::Var("fresh".into())),
                                            field: "status".into(),
                                        }),
                                        right: Box::new(Expr::Int(0)),
                                    },
                                    then: vec![
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Self::slot_addr(Expr::Var("base".into()), 0),
                                                Expr::Field {
                                                    base: Box::new(Expr::Var("fresh".into())),
                                                    field: "data".into(),
                                                },
                                            ],
                                        }),
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Expr::BinOp {
                                                    op: sal_syntax::BinOp::Add,
                                                    left: Box::new(Expr::Var("base".into())),
                                                    right: Box::new(Expr::Int(16)),
                                                },
                                                Expr::Var("capacity".into()),
                                            ],
                                        }),
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Expr::BinOp {
                                                    op: sal_syntax::BinOp::Add,
                                                    left: Box::new(Expr::Var("base".into())),
                                                    right: Box::new(Expr::Int(24)),
                                                },
                                                Self::slot_word(Expr::Var("base".into()), 8),
                                            ],
                                        }),
                                    ],
                                    else_: vec![Stmt::Assign {
                                        name: "status".into(),
                                        expr: Expr::Int(-12),
                                    }],
                                },
                            ],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::Return(Expr::Var("status".into())),
            ],
        );
        // Insert packs the key field-wise, grows past 3/4 occupancy, then
        // replaces (1) or inserts (0). Failure reports -12.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapInsert_{ktag}_{vtag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("key".into(), key.clone()),
                ("value".into(), value.clone()),
            ],
            Some(TypeRef::Named("i64".into())),
            vec!["SystemCall"],
            span,
            vec![
                Stmt::Let {
                    name: "keycell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: pack_name(ktag),
                        args: vec![Expr::Var("key".into())],
                    },
                },
                Stmt::Let {
                    name: "valcell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_name(vtag),
                        args: vec![Expr::Var("value".into())],
                    },
                },
                Stmt::Let {
                    name: "status".into(),
                    mutable: true,
                    expr: Expr::Int(-12),
                },
                Stmt::Let {
                    name: "ready".into(),
                    mutable: true,
                    expr: Expr::Bool(false),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Let {
                            name: "len".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 8),
                        },
                        Stmt::Let {
                            name: "cap".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 16),
                        },
                        Stmt::Let {
                            name: "used".into(),
                            mutable: false,
                            expr: Self::slot_word(Expr::Var("base".into()), 24),
                        },
                        Stmt::Let {
                            name: "target".into(),
                            mutable: true,
                            expr: Self::slot_word(Expr::Var("base".into()), 0),
                        },
                        Stmt::Let {
                            name: "tcap".into(),
                            mutable: true,
                            expr: Expr::Var("cap".into()),
                        },
                        Stmt::Let {
                            name: "tused".into(),
                            mutable: true,
                            expr: Expr::Var("used".into()),
                        },
                        Stmt::If {
                            cond: Expr::BinOp {
                                op: sal_syntax::BinOp::Eq,
                                left: Box::new(Expr::Var("cap".into())),
                                right: Box::new(Self::usize_lit(0)),
                            },
                            then: vec![
                                Stmt::Let {
                                    name: "fresh".into(),
                                    mutable: false,
                                    expr: Expr::Call {
                                        name: "CollectionMapRehash".into(),
                                        args: vec![
                                            Expr::Var("target".into()),
                                            key_width.clone(),
                                            val_width.clone(),
                                            Expr::Var("cap".into()),
                                            Self::usize_lit(8),
                                        ],
                                    },
                                },
                                Stmt::If {
                                    cond: Expr::BinOp {
                                        op: sal_syntax::BinOp::Eq,
                                        left: Box::new(Expr::Field {
                                            base: Box::new(Expr::Var("fresh".into())),
                                            field: "status".into(),
                                        }),
                                        right: Box::new(Expr::Int(0)),
                                    },
                                    then: vec![
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Self::slot_addr(Expr::Var("base".into()), 0),
                                                Expr::Field {
                                                    base: Box::new(Expr::Var("fresh".into())),
                                                    field: "data".into(),
                                                },
                                            ],
                                        }),
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Expr::BinOp {
                                                    op: sal_syntax::BinOp::Add,
                                                    left: Box::new(Expr::Var("base".into())),
                                                    right: Box::new(Expr::Int(16)),
                                                },
                                                Self::usize_lit(8),
                                            ],
                                        }),
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "store64".into(),
                                            args: vec![
                                                Expr::BinOp {
                                                    op: sal_syntax::BinOp::Add,
                                                    left: Box::new(Expr::Var("base".into())),
                                                    right: Box::new(Expr::Int(24)),
                                                },
                                                Expr::Var("len".into()),
                                            ],
                                        }),
                                        Stmt::Assign {
                                            name: "target".into(),
                                            expr: Expr::Field {
                                                base: Box::new(Expr::Var("fresh".into())),
                                                field: "data".into(),
                                            },
                                        },
                                        Stmt::Assign {
                                            name: "tcap".into(),
                                            expr: Self::usize_lit(8),
                                        },
                                        Stmt::Assign {
                                            name: "tused".into(),
                                            expr: Expr::Var("len".into()),
                                        },
                                        Stmt::Assign {
                                            name: "ready".into(),
                                            expr: Expr::Bool(true),
                                        },
                                    ],
                                    else_: vec![],
                                },
                            ],
                            else_: vec![Stmt::If {
                                cond: Expr::BinOp {
                                    op: sal_syntax::BinOp::Gt,
                                    left: Box::new(Expr::BinOp {
                                        op: sal_syntax::BinOp::Add,
                                        left: Box::new(Expr::Var("used".into())),
                                        right: Box::new(Self::usize_lit(1)),
                                    }),
                                    right: Box::new(Expr::BinOp {
                                        op: sal_syntax::BinOp::Sub,
                                        left: Box::new(Expr::Var("cap".into())),
                                        right: Box::new(Expr::BinOp {
                                            op: sal_syntax::BinOp::Div,
                                            left: Box::new(Expr::Var("cap".into())),
                                            right: Box::new(Self::usize_lit(4)),
                                        }),
                                    }),
                                },
                                then: vec![Stmt::If {
                                    cond: Expr::BinOp {
                                        op: sal_syntax::BinOp::Le,
                                        left: Box::new(Expr::Var("cap".into())),
                                        right: Box::new(Self::usize_lit(2305843009213693951)),
                                    },
                                    then: vec![
                                        Stmt::Let {
                                            name: "want".into(),
                                            mutable: false,
                                            expr: Expr::BinOp {
                                                op: sal_syntax::BinOp::Mul,
                                                left: Box::new(Expr::Var("cap".into())),
                                                right: Box::new(Self::usize_lit(2)),
                                            },
                                        },
                                        Stmt::Let {
                                            name: "fresh".into(),
                                            mutable: false,
                                            expr: Expr::Call {
                                                name: "CollectionMapRehash".into(),
                                                args: vec![
                                                    Expr::Var("target".into()),
                                                    key_width.clone(),
                                                    val_width.clone(),
                                                    Expr::Var("cap".into()),
                                                    Expr::Var("want".into()),
                                                ],
                                            },
                                        },
                                        Stmt::If {
                                            cond: Expr::BinOp {
                                                op: sal_syntax::BinOp::Eq,
                                                left: Box::new(Expr::Field {
                                                    base: Box::new(Expr::Var("fresh".into())),
                                                    field: "status".into(),
                                                }),
                                                right: Box::new(Expr::Int(0)),
                                            },
                                            then: vec![
                                                Stmt::ExprStmt(Expr::Call {
                                                    name: "store64".into(),
                                                    args: vec![
                                                        Self::slot_addr(
                                                            Expr::Var("base".into()),
                                                            0,
                                                        ),
                                                        Expr::Field {
                                                            base: Box::new(Expr::Var(
                                                                "fresh".into(),
                                                            )),
                                                            field: "data".into(),
                                                        },
                                                    ],
                                                }),
                                                Stmt::ExprStmt(Expr::Call {
                                                    name: "store64".into(),
                                                    args: vec![
                                                        Expr::BinOp {
                                                            op: sal_syntax::BinOp::Add,
                                                            left: Box::new(Expr::Var(
                                                                "base".into(),
                                                            )),
                                                            right: Box::new(Expr::Int(16)),
                                                        },
                                                        Expr::Var("want".into()),
                                                    ],
                                                }),
                                                Stmt::ExprStmt(Expr::Call {
                                                    name: "store64".into(),
                                                    args: vec![
                                                        Expr::BinOp {
                                                            op: sal_syntax::BinOp::Add,
                                                            left: Box::new(Expr::Var(
                                                                "base".into(),
                                                            )),
                                                            right: Box::new(Expr::Int(24)),
                                                        },
                                                        Expr::Var("len".into()),
                                                    ],
                                                }),
                                                Stmt::Assign {
                                                    name: "target".into(),
                                                    expr: Expr::Field {
                                                        base: Box::new(Expr::Var("fresh".into())),
                                                        field: "data".into(),
                                                    },
                                                },
                                                Stmt::Assign {
                                                    name: "tcap".into(),
                                                    expr: Expr::Var("want".into()),
                                                },
                                                Stmt::Assign {
                                                    name: "tused".into(),
                                                    expr: Expr::Var("len".into()),
                                                },
                                                Stmt::Assign {
                                                    name: "ready".into(),
                                                    expr: Expr::Bool(true),
                                                },
                                            ],
                                            else_: vec![],
                                        },
                                    ],
                                    else_: vec![Stmt::Assign {
                                        name: "ready".into(),
                                        expr: Expr::Bool(true),
                                    }],
                                }],
                                else_: vec![Stmt::Assign {
                                    name: "ready".into(),
                                    expr: Expr::Bool(true),
                                }],
                            }],
                        },
                        Stmt::If {
                            cond: Expr::Var("ready".into()),
                            then: vec![
                                Stmt::Let {
                                    name: "probe".into(),
                                    mutable: false,
                                    expr: Expr::Call {
                                        name: "CollectionMapFindSlot".into(),
                                        args: vec![
                                            Expr::Var("target".into()),
                                            Expr::Var("tcap".into()),
                                            stride.clone(),
                                            Expr::Call {
                                                name: "address".into(),
                                                args: vec![Expr::Var("keycell".into())],
                                            },
                                            key_width.clone(),
                                        ],
                                    },
                                },
                                Stmt::If {
                                    cond: Expr::Field {
                                        base: Box::new(Expr::Var("probe".into())),
                                        field: "found".into(),
                                    },
                                    then: vec![
                                        Stmt::ExprStmt(Expr::Call {
                                            name: "CollectionMapSlotWriteVal".into(),
                                            args: vec![
                                                Expr::Var("target".into()),
                                                Expr::Field {
                                                    base: Box::new(Expr::Var("probe".into())),
                                                    field: "index".into(),
                                                },
                                                stride.clone(),
                                                key_width.clone(),
                                                Expr::Call {
                                                    name: "address".into(),
                                                    args: vec![Expr::Var("valcell".into())],
                                                },
                                                val_width.clone(),
                                            ],
                                        }),
                                        Stmt::Assign {
                                            name: "status".into(),
                                            expr: Expr::Int(1),
                                        },
                                    ],
                                    else_: vec![Stmt::If {
                                        cond: Expr::BinOp {
                                            op: sal_syntax::BinOp::Ne,
                                            left: Box::new(Expr::Field {
                                                base: Box::new(Expr::Var("probe".into())),
                                                field: "index".into(),
                                            }),
                                            right: Box::new(Expr::Var("tcap".into())),
                                        },
                                        then: vec![
                                            Stmt::ExprStmt(Expr::Call {
                                                name: "CollectionMapSlotInsert".into(),
                                                args: vec![
                                                    Expr::Var("target".into()),
                                                    Expr::Field {
                                                        base: Box::new(Expr::Var("probe".into())),
                                                        field: "index".into(),
                                                    },
                                                    stride.clone(),
                                                    Expr::Call {
                                                        name: "address".into(),
                                                        args: vec![Expr::Var("keycell".into())],
                                                    },
                                                    key_width.clone(),
                                                    Expr::Call {
                                                        name: "address".into(),
                                                        args: vec![Expr::Var("valcell".into())],
                                                    },
                                                    val_width.clone(),
                                                ],
                                            }),
                                            Stmt::ExprStmt(Expr::Call {
                                                name: "store64".into(),
                                                args: vec![
                                                    Expr::BinOp {
                                                        op: sal_syntax::BinOp::Add,
                                                        left: Box::new(Expr::Var("base".into())),
                                                        right: Box::new(Expr::Int(8)),
                                                    },
                                                    Expr::BinOp {
                                                        op: sal_syntax::BinOp::Add,
                                                        left: Box::new(Expr::Var("len".into())),
                                                        right: Box::new(Self::usize_lit(1)),
                                                    },
                                                ],
                                            }),
                                            Stmt::If {
                                                cond: Expr::Field {
                                                    base: Box::new(Expr::Var("probe".into())),
                                                    field: "empty".into(),
                                                },
                                                then: vec![Stmt::ExprStmt(Expr::Call {
                                                    name: "store64".into(),
                                                    args: vec![
                                                        Expr::BinOp {
                                                            op: sal_syntax::BinOp::Add,
                                                            left: Box::new(Expr::Var(
                                                                "base".into(),
                                                            )),
                                                            right: Box::new(Expr::Int(24)),
                                                        },
                                                        Expr::BinOp {
                                                            op: sal_syntax::BinOp::Add,
                                                            left: Box::new(Expr::Var(
                                                                "tused".into(),
                                                            )),
                                                            right: Box::new(Self::usize_lit(1)),
                                                        },
                                                    ],
                                                })],
                                                else_: vec![],
                                            },
                                            Stmt::Assign {
                                                name: "status".into(),
                                                expr: Expr::Int(0),
                                            },
                                        ],
                                        else_: vec![],
                                    }],
                                },
                            ],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::Return(Expr::Var("status".into())),
            ],
        );
        // Get looks up the packed key without allocating or rehashing.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapGet_{ktag}_{vtag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("key".into(), key.clone()),
            ],
            Some(res_ty.clone()),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "keycell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: pack_name(ktag),
                        args: vec![Expr::Var("key".into())],
                    },
                },
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_name(vtag),
                        args: vec![Expr::Call {
                            name: zero_name(vtag),
                            args: vec![],
                        }],
                    },
                },
                Stmt::Let {
                    name: "found".into(),
                    mutable: true,
                    expr: Expr::Bool(false),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Assign {
                            name: "found".into(),
                            expr: Self::probe_found(Expr::Call {
                                name: "CollectionMapLookup".into(),
                                args: vec![
                                    Self::slot_word(Expr::Var("base".into()), 0),
                                    Self::slot_word(Expr::Var("base".into()), 16),
                                    stride.clone(),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("keycell".into())],
                                    },
                                    key_width.clone(),
                                    val_width.clone(),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("cell".into())],
                                    },
                                    Self::usize_lit(0),
                                ],
                            }),
                        },
                    ],
                },
                Stmt::If {
                    cond: Expr::Var("found".into()),
                    then: vec![Stmt::Return(Expr::Call {
                        name: res_name(vtag),
                        args: vec![
                            Expr::Bool(true),
                            Expr::Field {
                                base: Box::new(Expr::Var("cell".into())),
                                field: "value".into(),
                            },
                        ],
                    })],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: res_name(vtag),
                    args: vec![
                        Expr::Bool(false),
                        Expr::Field {
                            base: Box::new(Expr::Var("cell".into())),
                            field: "value".into(),
                        },
                    ],
                }),
            ],
        );
        // Remove tombstones the slot and publishes `len - 1`. No rehash.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapRemove_{ktag}_{vtag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("key".into(), key.clone()),
            ],
            Some(res_ty.clone()),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "keycell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: pack_name(ktag),
                        args: vec![Expr::Var("key".into())],
                    },
                },
                Stmt::Let {
                    name: "cell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_name(vtag),
                        args: vec![Expr::Call {
                            name: zero_name(vtag),
                            args: vec![],
                        }],
                    },
                },
                Stmt::Let {
                    name: "found".into(),
                    mutable: true,
                    expr: Expr::Bool(false),
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Assign {
                            name: "found".into(),
                            expr: Self::probe_found(Expr::Call {
                                name: "CollectionMapLookup".into(),
                                args: vec![
                                    Self::slot_word(Expr::Var("base".into()), 0),
                                    Self::slot_word(Expr::Var("base".into()), 16),
                                    stride.clone(),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("keycell".into())],
                                    },
                                    key_width.clone(),
                                    val_width.clone(),
                                    Expr::Call {
                                        name: "address".into(),
                                        args: vec![Expr::Var("cell".into())],
                                    },
                                    Self::usize_lit(1),
                                ],
                            }),
                        },
                        Stmt::If {
                            cond: Expr::Var("found".into()),
                            then: vec![Stmt::ExprStmt(Expr::Call {
                                name: "store64".into(),
                                args: vec![
                                    Expr::BinOp {
                                        op: sal_syntax::BinOp::Add,
                                        left: Box::new(Expr::Var("base".into())),
                                        right: Box::new(Expr::Int(8)),
                                    },
                                    Expr::BinOp {
                                        op: sal_syntax::BinOp::Sub,
                                        left: Box::new(Self::slot_word(
                                            Self::slot_addr(Expr::Var("base".into()), 0),
                                            8,
                                        )),
                                        right: Box::new(Self::usize_lit(1)),
                                    },
                                ],
                            })],
                            else_: vec![],
                        },
                    ],
                },
                Stmt::If {
                    cond: Expr::Var("found".into()),
                    then: vec![Stmt::Return(Expr::Call {
                        name: res_name(vtag),
                        args: vec![
                            Expr::Bool(true),
                            Expr::Field {
                                base: Box::new(Expr::Var("cell".into())),
                                field: "value".into(),
                            },
                        ],
                    })],
                    else_: vec![],
                },
                Stmt::Return(Expr::Call {
                    name: res_name(vtag),
                    args: vec![
                        Expr::Bool(false),
                        Expr::Field {
                            base: Box::new(Expr::Var("cell".into())),
                            field: "value".into(),
                        },
                    ],
                }),
            ],
        );
        // Contains probes without copying any value out.
        self.emit_op(
            out,
            format!("{GEN_PREFIX}MapContains_{ktag}_{vtag}"),
            vec![
                ("slot".into(), borrowed.clone()),
                ("key".into(), key.clone()),
            ],
            Some(TypeRef::Named("bool".into())),
            vec!["Pure"],
            span,
            vec![
                Stmt::Let {
                    name: "keycell".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: pack_name(ktag),
                        args: vec![Expr::Var("key".into())],
                    },
                },
                Stmt::Unsafe {
                    body: vec![
                        Stmt::Let {
                            name: "base".into(),
                            mutable: false,
                            expr: Self::borrow_of("slot"),
                        },
                        Stmt::Return(Self::probe_found(Expr::Call {
                            name: "CollectionMapLookup".into(),
                            args: vec![
                                Self::slot_word(Expr::Var("base".into()), 0),
                                Self::slot_word(Expr::Var("base".into()), 16),
                                stride.clone(),
                                Expr::Call {
                                    name: "address".into(),
                                    args: vec![Expr::Var("keycell".into())],
                                },
                                key_width.clone(),
                                val_width.clone(),
                                Self::usize_lit(0),
                                Self::usize_lit(0),
                            ],
                        })),
                    ],
                },
            ],
        );
    }
}

#[cfg(test)]
mod tests {
    use super::is_lowered;

    const SOURCE: &str = "operation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let v = vector(i64, usize(2)).\n        let status = vector_push(v, 1).\n        vector_drop(v).\n        return status.\n";

    fn parsed() -> sal_syntax::SalFile {
        let (file, diagnostics) = sal_syntax::parse(SOURCE);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        file
    }

    #[test]
    fn lowered_output_is_recognized_and_survives_a_second_build() {
        let source = parsed();
        assert!(!is_lowered(&source));
        let (first, diagnostics) = crate::build(&source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert!(is_lowered(&first.file));
        // Native emission re-runs `build` on the already-lowered file: the
        // wrappers' `borrow(slot)` address idiom must not be re-validated as
        // ownership, and the result must be a fixed point.
        let (second, diagnostics) = crate::build(&first.file);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(format!("{:?}", second.file), format!("{:?}", first.file));
    }
}
