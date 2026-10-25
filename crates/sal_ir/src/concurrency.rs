//! Typed safe concurrency lowering: affine `Channel<T>` / `Thread<i64>` checking
//! plus erasure into ordinary SAL AST and generated wrappers.
//!
//! CONTRACT (canonical surface, heterogeneous arms):
//! - `channel(T, capacity)` binds `Channel<T>`; `channel_clone(c)` duplicates;
//!   `channel_drop(c)` consumes; `close(c)` borrows and returns `bool`;
//!   `send(c, v)` / `receive(c)` borrow and return `SendResult<T>` /
//!   `ReceiveResult<T>`; `spawn(Worker, v)` moves a `Channel` argument and
//!   returns `Thread<i64>`; `join(t)` consumes and returns `i64`.
//! - `wait_for(receive(..), send(..), timeout(ms) | otherwise())` commits
//!   exactly one arm. Arms are heterogeneous: each arm keeps its own payload
//!   type. The result is `WaitResult<T0, ..>` with `index: usize`,
//!   `status: usize` (0 committed, 1 closed, 2 fallback) and per-arm fields
//!   `armN: WaitArm<TN>` where `WaitArm<T>` is `{selected: bool, open: bool,
//!   value: T}`. There is no global `.value` field.
//! - Safe payloads are integers (`usize` counts), `bool`, and `C` records
//!   built recursively from those. Handles and result records cannot be
//!   nested inside other containers or record fields. Workers may receive
//!   one owned `Channel<T>`; their return type is always `i64`.
//! - Diagnostics are `CON201` (payload), `CON202` (call shape), `CON203`
//!   (alias/escape), `CON204` (reuse after move), `CON205` (leak), `CON206`
//!   (`wait_for` shape), `CON207` (spawn/worker), `CON208` (depth/collision).
//! - The pass is idempotent and preserves non-concurrency programs exactly:
//!   without canonical calls or `Channel` / `Thread` / result types the input
//!   file is returned cloned. Generated names all start with `SalConc`.
//! - Generated wrappers call only runtime SAL operations supplied by
//!   `std/concurrency.sal` (`SalChannelNew/Clone/Drop/Close`, `SalSelect`,
//!   `SalThreadSpawn/Join`, `SalAlloc/Free`, `ConcurrencyCopy`), the `syscall`
//!   / `address` / `size_of` / `load64` / `store64` builtins, and the
//!   `operation_address` boundary. Payload bytes travel in generated
//!   single-field C-layout boxes (`address(box)` is the stable pointer;
//!   widths come from `size_of(box)`), never through trapping scalar casts.
//!   Allocation / spawn failure terminates via `exit_group` (231) nonzero;
//!   it never dereferences null.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use sal_syntax::{Diagnostic, Expr, Item, OperationDecl, Severity, Span, Stmt, TypeRef};

mod check;
mod emit;

/// Maximum tracked AST nesting depth for analysis and rewrite.
const MAX_DEPTH: usize = 128;
/// Maximum `wait_for` arms per the runtime contract.
const MAX_ARMS: usize = 32;
/// Reserved prefix for every generated top-level name and nothing else.
const GEN_PREFIX: &str = "SalConc";
/// Linux `exit_group` syscall number used for clean allocation-failure exit.
const EXIT_GROUP: i64 = 231;

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
        "channel"
            | "channel_clone"
            | "channel_drop"
            | "send"
            | "receive"
            | "close"
            | "spawn"
            | "join"
            | "wait_for"
            | "timeout"
            | "otherwise"
    )
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

fn channel_payload(ty: &TypeRef) -> Option<&TypeRef> {
    match generic_parts(ty) {
        Some(("Channel", [one])) => Some(one),
        _ => None,
    }
}

fn thread_payload(ty: &TypeRef) -> Option<&TypeRef> {
    match generic_parts(ty) {
        Some(("Thread", [one])) => Some(one),
        _ => None,
    }
}

fn result_parts(ty: &TypeRef) -> Option<(&str, &[TypeRef])> {
    match generic_parts(ty) {
        Some((name @ ("SendResult" | "ReceiveResult" | "WaitResult" | "WaitArm"), args)) => {
            Some((name, args))
        }
        _ => None,
    }
}

/// True when a type mentions any concurrency-owned generic anywhere inside.
fn mentions_concurrency(ty: &TypeRef) -> bool {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if let TypeRef::Generic { name, args } = ty {
            if matches!(
                name.as_str(),
                "Channel" | "Thread" | "SendResult" | "ReceiveResult" | "WaitResult" | "WaitArm"
            ) {
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

/// Deterministic collision-free tag for one payload type. Scalars use a fixed
/// `P_` vocabulary; records use length- plus hash-qualified `R_` names so a
/// record literally named `I64` can never collide with primitive `i64`, and
/// two spellings sanitizing identically still differ.
fn payload_tag(ty: &TypeRef) -> Option<String> {
    match ty {
        TypeRef::Named(name) => {
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
                _ => {
                    return Some(format!(
                        "R_{}_{}_{:016X}",
                        sanitize(name),
                        name.len(),
                        fnv1a(name)
                    ))
                }
            };
            Some(format!("P_{upper}"))
        }
        TypeRef::Generic { name, args } => {
            // Only `Channel<Q>` appears here (worker ownership transfer).
            if name == "Channel" && args.len() == 1 {
                return payload_tag(&args[0]).map(|inner| format!("C_{}_{}", inner.len(), inner));
            }
            None
        }
    }
}

fn box_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Box_{tag}")
}

fn send_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Send_{tag}")
}

fn recv_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Recv_{tag}")
}

fn arm_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Arm_{tag}")
}

fn chan_new_name(tag: &str) -> String {
    format!("{GEN_PREFIX}ChanNew_{tag}")
}

fn send_op_name(tag: &str) -> String {
    format!("{GEN_PREFIX}SendOp_{tag}")
}

fn recv_op_name(tag: &str) -> String {
    format!("{GEN_PREFIX}RecvOp_{tag}")
}

fn zero_name(tag: &str) -> String {
    format!("{GEN_PREFIX}Zero_{tag}")
}

fn nodes_name(count: usize) -> String {
    format!("{GEN_PREFIX}Nodes{count}")
}

/// Length-encoded join so distinct arm lists can never spell one name.
fn wait_names(arms: &[(ArmDir, String)]) -> (String, String) {
    let mut op = format!("{GEN_PREFIX}Wait{}", arms.len());
    for (dir, tag) in arms {
        op.push_str(&format!("_{}{}_{}", dir.code(), tag.len(), tag));
    }
    let mut res = format!("{GEN_PREFIX}WaitRes{}", arms.len());
    for (_, tag) in arms {
        res.push_str(&format!("_{}_{}", tag.len(), tag));
    }
    (op, res)
}

fn tramp_name(worker: &str, tag: &str) -> String {
    format!(
        "{GEN_PREFIX}Tramp_{}_{}_{tag}",
        worker.len(),
        sanitize(worker)
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArmDir {
    Recv,
    Send,
}

impl ArmDir {
    fn code(self) -> &'static str {
        match self {
            ArmDir::Recv => "R",
            ArmDir::Send => "S",
        }
    }
}

/// Fast iterative probe: does this file need concurrency lowering at all?
/// Generated `SalConc` items alone never trigger a second pass. This probe
/// counts nothing and imposes no depth threshold: only canonical call names
/// or concurrency generics trigger the full pass.
fn needs_lower(file: &sal_syntax::SalFile) -> bool {
    for item in &file.items {
        match item {
            Item::Entity(entity) => {
                for field in &entity.fields {
                    if mentions_concurrency(&field.ty) {
                        return true;
                    }
                }
            }
            Item::Operation(operation) => {
                for param in &operation.accepts {
                    if mentions_concurrency(&param.ty) {
                        return true;
                    }
                }
                if operation.returns.as_ref().is_some_and(mentions_concurrency) {
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

/// Lower typed safe concurrency into ordinary SAL AST plus generated wrappers.
///
/// Non-concurrency files are returned cloned (byte-equivalent). Invalid
/// concurrency programs fail with `CON*` diagnostics.
pub fn lower(file: &sal_syntax::SalFile) -> Result<sal_syntax::SalFile, Vec<Diagnostic>> {
    if !needs_lower(file) {
        return Ok(file.clone());
    }
    if let Some(diagnostic) = check::preflight(file) {
        return Err(vec![diagnostic]);
    }
    Pass::run(file)
}
// ---------------------------------------------------------------------------
// Type registry: payloads, operations, entity layouts.
// ---------------------------------------------------------------------------

struct Registry {
    param_payload: HashMap<String, HashMap<String, Option<Payload>>>,
    workers: HashMap<String, (Payload, Span)>,
    entities: HashMap<String, Vec<(String, Payload)>>,
    field_types: HashMap<String, Vec<(String, TypeRef)>>,
    operations: BTreeMap<String, OperationDecl>,
}

/// One affine-safe payload shape. `Channel` doubles as its own payload for
/// worker arguments carrying ownership (payload = `Channel<Q>`).
#[derive(Debug, Clone, PartialEq, Eq)]
enum Payload {
    Scalar(String),
    Record(String),
    Channel(Box<Payload>),
}

impl Payload {
    fn spell(&self) -> String {
        match self {
            Payload::Scalar(name) | Payload::Record(name) => name.clone(),
            Payload::Channel(inner) => format!("Channel<{}>", inner.spell()),
        }
    }

    fn type_ref(&self) -> TypeRef {
        match self {
            Payload::Scalar(name) | Payload::Record(name) => TypeRef::Named(name.clone()),
            Payload::Channel(inner) => TypeRef::Generic {
                name: "Channel".into(),
                args: vec![inner.type_ref()],
            },
        }
    }
}

/// Build a payload from a type reference using only the primitive names and
/// the caller-supplied entity table (records need field info from `entities`).
fn payload_of(ty: &TypeRef) -> Option<Payload> {
    match ty {
        TypeRef::Named(name) => {
            if is_integer_name(name) || name == "bool" {
                Some(Payload::Scalar(name.clone()))
            } else {
                // Record-ness is confirmed by the caller against entities.
                Some(Payload::Record(name.clone()))
            }
        }
        TypeRef::Generic { name, args } => {
            if name == "Channel" && args.len() == 1 {
                return payload_of(&args[0]).map(|inner| Payload::Channel(Box::new(inner)));
            }
            None
        }
    }
}

/// Concrete definition of one tagged payload owned by this pass.
#[derive(Debug, Clone)]
struct PayloadDef {
    tag: String,
    payload: Payload,
}

struct Pass;

impl Pass {
    fn build_registry(file: &sal_syntax::SalFile, diagnostics: &mut Vec<Diagnostic>) -> Registry {
        let mut registry = Registry {
            param_payload: HashMap::new(),
            workers: HashMap::new(),
            entities: HashMap::new(),
            field_types: HashMap::new(),
            operations: BTreeMap::new(),
        };
        for item in &file.items {
            match item {
                Item::Entity(entity) => {
                    registry
                        .field_types
                        .entry(entity.name.clone())
                        .or_insert_with(|| {
                            entity
                                .fields
                                .iter()
                                .map(|field| (field.name.clone(), field.ty.clone()))
                                .collect()
                        });
                    if entity.c_layout {
                        registry
                            .entities
                            .entry(entity.name.clone())
                            .or_insert_with(|| {
                                entity
                                    .fields
                                    .iter()
                                    .map(|field| {
                                        (
                                            field.name.clone(),
                                            payload_of(&field.ty).unwrap_or_else(|| {
                                                Payload::Scalar("!!invalid!!".into())
                                            }),
                                        )
                                    })
                                    .collect()
                            });
                    }
                    for field in &entity.fields {
                        if mentions_concurrency(&field.ty) {
                            diagnostics.push(err(
                                "CON201",
                                "concurrency handles/results cannot be embedded in user records"
                                    .into(),
                                &field.span,
                            ));
                        }
                    }
                }
                Item::Operation(operation) => {
                    registry
                        .operations
                        .entry(operation.name.clone())
                        .or_insert_with(|| operation.clone());
                }
                _ => {}
            }
        }
        for (name, operation) in &registry.operations {
            let params = operation
                .accepts
                .iter()
                .map(|parameter| {
                    let payload = channel_payload(&parameter.ty)
                        .and_then(|ty| checked_payload(ty, &registry.entities));
                    (parameter.name.clone(), payload)
                })
                .collect();
            registry.param_payload.insert(name.clone(), params);
            if operation.c_import.is_none()
                && !operation.body.is_empty()
                && operation.accepts.len() == 1
                && operation.returns == Some(TypeRef::Named("i64".into()))
            {
                if let Some(payload) = checked_payload(&operation.accepts[0].ty, &registry.entities)
                {
                    registry
                        .workers
                        .insert(name.clone(), (payload, operation.span.clone()));
                }
            }
        }
        registry
    }
}

/// Classify with entity knowledge: bare names that are entities become
/// records, everything else must be a known plain type.
/// Parsed canonical type of one operation parameter or return.
#[derive(Debug, Clone)]
enum DeclaredTy {
    Plain,
    Chan(Payload),
    Thread(Payload),
    SendRes(Payload),
    RecvRes(Payload),
    WaitRes(Vec<Payload>),
    OtherGeneric,
}

fn classify_typed(ty: &TypeRef, entities: &HashMap<String, Vec<(String, Payload)>>) -> DeclaredTy {
    if let Some(inner) = channel_payload(ty) {
        if let Some(payload) = checked_payload(inner, entities) {
            return DeclaredTy::Chan(payload);
        }
        return DeclaredTy::OtherGeneric;
    }
    if let Some(inner) = thread_payload(ty) {
        if let Some(payload) = checked_payload(inner, entities) {
            return DeclaredTy::Thread(payload);
        }
        return DeclaredTy::OtherGeneric;
    }
    if let Some((name, args)) = result_parts(ty) {
        let mut payloads = Vec::with_capacity(args.len());
        for arg in args {
            match checked_payload(arg, entities) {
                Some(payload) => payloads.push(payload),
                None => return DeclaredTy::OtherGeneric,
            }
        }
        match name {
            "SendResult" if payloads.len() == 1 => {
                return DeclaredTy::SendRes(payloads.pop().unwrap());
            }
            "ReceiveResult" if payloads.len() == 1 => {
                return DeclaredTy::RecvRes(payloads.pop().unwrap());
            }
            "WaitResult" if !payloads.is_empty() => return DeclaredTy::WaitRes(payloads),
            "WaitArm" => return DeclaredTy::OtherGeneric,
            _ => return DeclaredTy::OtherGeneric,
        }
    }
    DeclaredTy::Plain
}

/// Payload validation with entity lookup: scalars always fine, records must
/// exist and contain only safe fields recursively.
fn checked_payload(
    ty: &TypeRef,
    entities: &HashMap<String, Vec<(String, Payload)>>,
) -> Option<Payload> {
    match ty {
        TypeRef::Named(name) => {
            if is_integer_name(name) || name == "bool" {
                return Some(Payload::Scalar(name.clone()));
            }
            if entities.contains_key(name) {
                let mut visiting = BTreeSet::new();
                if record_payload_ok(name, entities, &mut visiting) {
                    return Some(Payload::Record(name.clone()));
                }
            }
            None
        }
        TypeRef::Generic { name, args } => {
            if name == "Channel" && args.len() == 1 {
                return checked_payload(&args[0], entities)
                    .map(|inner| Payload::Channel(Box::new(inner)));
            }
            None
        }
    }
}

fn record_payload_ok(
    name: &str,
    entities: &HashMap<String, Vec<(String, Payload)>>,
    visiting: &mut BTreeSet<String>,
) -> bool {
    let Some(fields) = entities.get(name) else {
        return false;
    };
    if visiting.len() >= MAX_DEPTH || !visiting.insert(name.to_owned()) {
        return false;
    }
    // Fields were pre-parsed with `payload_of`; now confirm each scalar is
    // really a scalar/record chain with entity backing (iteratively).
    let mut stack: Vec<Payload> = fields.iter().map(|(_, payload)| payload.clone()).collect();
    while let Some(payload) = stack.pop() {
        match payload {
            Payload::Scalar(scalar) => {
                if scalar == "!!invalid!!" {
                    return false;
                }
                if is_integer_name(&scalar) || scalar == "bool" {
                    continue;
                }
                if !record_payload_ok(&scalar, entities, visiting) {
                    return false;
                }
            }
            Payload::Record(record) => {
                if !record_payload_ok(&record, entities, visiting) {
                    return false;
                }
            }
            Payload::Channel(_) => return false,
        }
    }
    visiting.remove(name);
    true
}

// ---------------------------------------------------------------------------
// C ABI guard: no handle/result generic crosses extern "C".
// ---------------------------------------------------------------------------

impl Pass {
    fn check_c_abi(file: &sal_syntax::SalFile, diagnostics: &mut Vec<Diagnostic>) -> bool {
        let mut triggered = false;
        for item in &file.items {
            let Item::Operation(operation) = item else {
                continue;
            };
            if operation.c_import.is_none() && operation.c_export.is_none() {
                continue;
            }
            let mut bad: Option<(&str, String)> = None;
            for param in &operation.accepts {
                if mentions_concurrency(&param.ty) {
                    bad = Some((param.name.as_str(), format!("{:?}", param.ty)));
                    break;
                }
            }
            if bad.is_none() {
                if let Some(returns) = &operation.returns {
                    if mentions_concurrency(returns) {
                        bad = Some(("<return>", format!("{returns:?}")));
                    }
                }
            }
            if let Some((where_, what)) = bad {
                triggered = true;
                diagnostics.push(err(
                    "CON203",
                    format!(
                        "operation `{}` cannot expose Channel/Thread/result type {what} across C ABI ({where_}); keep ownership inside SAL and pass only scalars or C records",
                        operation.name
                    ),
                    &operation.span,
                ));
            }
        }
        triggered
    }
}
// ---------------------------------------------------------------------------
// Analyzer: affine state machine over every body path.
// ---------------------------------------------------------------------------

impl Pass {
    fn run(file: &sal_syntax::SalFile) -> Result<sal_syntax::SalFile, Vec<Diagnostic>> {
        let mut diagnostics = Vec::new();
        Self::check_c_abi(file, &mut diagnostics);
        let registry = Self::build_registry(file, &mut diagnostics);
        for item in &file.items {
            let (name, span) = match item {
                Item::Entity(value) => (&value.name, &value.span),
                Item::Operation(value) => (&value.name, &value.span),
                Item::Enum(value) => (&value.name, &value.span),
                Item::Layer(value) => (&value.name, &value.span),
                Item::Service(value) => (&value.name, &value.span),
                Item::Module(value) => (&value.name, &value.span),
                Item::Server(value) => (&value.name, &value.span),
                Item::Route(value) => (&value.name, &value.span),
                Item::Application { name, span } => (name, span),
                Item::Use { .. } => continue,
            };
            if name.starts_with(GEN_PREFIX) {
                diagnostics.push(err(
                    "CON208",
                    format!("`{name}` collides with the compiler concurrency namespace"),
                    span,
                ));
            }
        }
        diagnostics.extend(check::validate(file, &registry));
        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }
        Ok(emit::rewrite(file, &registry))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> sal_syntax::SalFile {
        let (file, diagnostics) = sal_syntax::parse(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        file
    }

    fn lower_err(source: &str) -> Vec<Diagnostic> {
        match lower(&parse(source)) {
            Ok(_) => panic!("expected Err"),
            Err(diagnostics) => diagnostics,
        }
    }

    fn codes(diagnostics: &[Diagnostic]) -> Vec<&str> {
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect()
    }

    #[test]
    fn rejects_bytes_and_text_payloads() {
        for payload in ["Bytes", "Text"] {
            let diagnostics = lower_err(&format!("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel({payload}, usize(1)).\n        channel_drop(ch).\n        return 0.\n"));
            assert!(codes(&diagnostics).contains(&"CON201"), "{diagnostics:?}");
        }
    }

    #[test]
    fn rejects_record_with_handle_field() {
        let diagnostics = lower_err("use \"std/concurrency.sal\".\nentity Carrier:\n    layout \"C\".\n    has tag of type i64.\n    has ch of type Channel<i64>.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(Carrier, usize(1)).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON201"), "{diagnostics:?}");
    }

    #[test]
    fn rejects_implicit_alias_and_use_after_drop() {
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let alias = ch.\n        channel_drop(ch).\n        channel_drop(alias).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON203"), "{diagnostics:?}");
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        channel_drop(ch).\n        let sent = send(ch, 1).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON204"), "{diagnostics:?}");
    }

    #[test]
    fn rejects_leak_and_double_join_and_no_join() {
        let leak = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        return 0.\n");
        assert!(codes(&leak).contains(&"CON205"), "{leak:?}");
        let double = lower_err("use \"std/concurrency.sal\".\noperation Worker:\n    accepts value of type i64.\n    returns i64.\n    body:\n        return value.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let t = spawn(Worker, 1).\n        let a = join(t).\n        let b = join(t).\n        return 0.\n");
        assert!(codes(&double).contains(&"CON204"), "{double:?}");
        let nojoin = lower_err("use \"std/concurrency.sal\".\noperation Worker:\n    accepts value of type i64.\n    returns i64.\n    body:\n        return value.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let t = spawn(Worker, 1).\n        return 0.\n");
        assert!(codes(&nojoin).contains(&"CON205"), "{nojoin:?}");
    }

    #[test]
    fn rejects_branch_divergence() {
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        if true:\n            channel_drop(ch).\n        else:\n            let s = send(ch, 1).\n        let t = send(ch, 2).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON205"), "{diagnostics:?}");
    }

    #[test]
    fn rejects_escape_into_ordinary_callee_and_raw_cast() {
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Identity:\n    accepts v of type i64.\n    returns i64.\n    body:\n        return v.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let x = Identity(ch).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON203"), "{diagnostics:?}");
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let n = usize(ch).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON203"), "{diagnostics:?}");
    }

    #[test]
    fn rejects_nested_producers_in_value_positions() {
        // channel()/clone()/spawn() nested inside another expression are
        // rejected instead of leaking an unbound handle.
        let nested = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let n = usize(channel(i64, usize(1))).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&nested).contains(&"CON202"), "{nested:?}");
        let send_nested = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let s = send(ch, channel(i64, usize(1))).\n        channel_drop(ch).\n        return 0.\n");
        assert!(
            codes(&send_nested).contains(&"CON202") || codes(&send_nested).contains(&"CON203"),
            "{send_nested:?}"
        );
    }

    #[test]
    fn rejects_bad_wait_shapes() {
        let empty = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let w = wait_for(otherwise()).\n        return 0.\n");
        assert!(codes(&empty).contains(&"CON206"), "{empty:?}");
        let misplaced = lower_err("use \"std/concurrency.sal\".\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let w = wait_for(receive(ch), timeout(usize(1)), otherwise()).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&misplaced).contains(&"CON206"), "{misplaced:?}");
    }

    #[test]
    fn rejects_spawn_mismatch_and_c_abi_escape() {
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Worker:\n    returns i64.\n    body:\n        return 0.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let t = spawn(Worker, 1).\n        let code = join(t).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON207"), "{diagnostics:?}");
        let diagnostics = lower_err("use \"std/concurrency.sal\".\noperation Exported:\n    accepts ch of type Channel<i64>.\n    returns i64.\n    exports \"C\" as \"sal_exported\".\n    effects: SystemCall, UnsafeMemory.\n    body:\n        return 0.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON203"), "{diagnostics:?}");
    }

    #[test]
    fn rejects_nested_concurrency_in_metadata_operands() {
        for expr in [
            "size_of(channel(i64, usize(1)))",
            "align_of(channel(i64, usize(1)))",
            "offset_of(channel(i64, usize(1)), \"value\")",
            "operation_address(channel(i64, usize(1)))",
        ] {
            let diagnostics = lower_err(&format!("operation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let bad = {expr}.\n        return 0.\n"));
            assert!(codes(&diagnostics).contains(&"CON202"), "{diagnostics:?}");
        }
    }

    #[test]
    fn rejects_loop_control_without_enclosing_loop() {
        for control in ["break", "continue"] {
            let diagnostics = lower_err(&format!("operation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        channel_drop(ch).\n        {control}.\n        return 0.\n"));
            assert!(codes(&diagnostics).contains(&"CON202"), "{diagnostics:?}");
        }
    }

    #[test]
    fn for_induction_binding_shadows_outer_handle() {
        let diagnostics = lower_err("operation Check:\n    accepts values of type Vec<usize>.\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        for ch in values:\n            let bad = receive(ch).\n        channel_drop(ch).\n        return 0.\n");
        assert!(codes(&diagnostics).contains(&"CON202"), "{diagnostics:?}");
    }

    #[test]
    fn channel_loans_cover_later_payload_and_timeout_operands() {
        for expression in [
            "send(ch, Consume(ch))",
            "wait_for(receive(ch), send(other, Consume(ch)))",
            "wait_for(receive(ch), timeout(usize(Consume(ch))))",
        ] {
            let diagnostics = lower_err(&format!(
                "operation Consume:\n    accepts ch of type Channel<i64>.\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        channel_drop(ch).\n        return 1.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let other = channel(i64, usize(1)).\n        let result = {expression}.\n        channel_drop(ch).\n        channel_drop(other).\n        return 0.\n"
            ));
            assert!(codes(&diagnostics).contains(&"CON203"), "{diagnostics:?}");
        }
    }

    #[test]
    fn borrowing_unbound_channel_producers_is_rejected() {
        for expression in [
            "receive(channel_clone(ch))",
            "receive(channel(i64, usize(1)))",
            "wait_for(receive(channel_clone(ch)))",
            "send(channel_clone(ch), 1)",
        ] {
            let diagnostics = lower_err(&format!(
                "operation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let ch = channel(i64, usize(1)).\n        let result = {expression}.\n        channel_drop(ch).\n        return 0.\n"
            ));
            assert!(codes(&diagnostics).contains(&"CON202"), "{diagnostics:?}");
        }
    }
}
