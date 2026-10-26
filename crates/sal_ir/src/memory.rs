//! Affine memory ownership + provenance checker (memory flow).
//!
//! PINNED CONTRACT (authoritative: `local://sal-declarative-contract.md`):
//! - `pub fn lower(&SalFile) -> Result<SalFile, Vec<Diagnostic>>` runs in the
//!   shared pipeline `declarations -> concurrency -> memory -> collections`
//!   (`sal_ir::build`). It preserves every public safe type and only inserts
//!   `SalMemoryAssertDisjoint(view(new_loan), view(existing_loan))` guard
//!   statements for genuinely dynamic (non-constant) overlap cases.
//! - `pub fn requires_buffer_runtime(&SalFile) -> bool` is a cheap iterative
//!   AST scan for `buffer(...)` / `buffer_drop(...)` anywhere (including
//!   `unsafe:` blocks and nested call args). The source loader uses it to
//!   auto-include sealed `std/buffer.sal` through the normal import path.
//!   This pass never injects allocator definitions and never trusts a
//!   user-declared `SalBufferAllocate`/`SalBufferRelease` by name.
//! - `pub fn requires_text_runtime(&SalFile) -> bool` is the same kind of
//!   scan for the `text(...)` intrinsic; the loader auto-includes sealed
//!   `std/text.sal` so SAL source cannot counterfeit `TextValidate` and so
//!   invalid-UTF8-to-`Text` conversions always resolve the genuine runtime.
//!   Native `text()` results carry the input `Bytes` provenance.
//!
//! OWNERSHIP MODEL (safe-stdlib contract, no competing checker):
//! - `Buffer` / `Vector<T>` / `Map<K,V>` bindings are affine owners: one live
//!   handle, explicit consume (`buffer_drop` / `vector_drop` / `map_drop` or
//!   transfer into an owned formal). Ordinary owned params transfer.
//! - `Borrow<T>` params reborrow: `borrow(owner)` (syntactic `borrow(x)` call)
//!   points at the ORIGINAL owner slot, suspends it while live, ends with
//!   `borrow_end`, never forged/cast/escaped/sent.
//! - `borrow_mut(owner, off, len)` / `slice_mut(parent, off, len)` create
//!   exclusive mutable loans; `view(span)` / `slice(span, off, len)` create
//!   immutable aliases; `len(...)` is metadata-only and always permitted.
//! - Loans alias by binding: every `let` loan is its own node sharing the
//!   root owner slot. `borrow_end(binding)` resolves exactly that binding and
//!   is an idempotent no-op once resolved (ending, forwarding, and temp
//!   expiry all resolve). Any other use of a resolved loan is `MEM201`.
//! - `Bytes` / `Text` values, internal (non-C) records, and `TextList`
//!   carry full source origins (root slots or `Static`) across calls,
//!   returns, fields, aliases, conditions, loops, exits, and every operand
//!   evaluation. Record-held loan nodes gate owner drops/reuse exactly like
//!   direct loans; field projections stamp per-field paths with span sites
//!   so disjoint aggregate fields compare actual field bytes.
//! - Call results rooted in a formal listed in the callee's declarative
//!   `ownership.return_from` take exactly that provenance (verified against
//!   the actual callee body, never trusted blindly). Calls into headerless
//!   operations (inferred flows) fall back to the union of span-typed actual
//!   argument provenance. Span-typed results are children of the
//!   contributing loan; records hold the contributing loan nodes.
//! - A stored/returned result MOVES contributing exclusive (mutable) loan
//!   handles: the old name resolves (later use `MEM201`, `borrow_end` a
//!   no-op) and the result carries the loan. Read-only views are shared:
//!   the view handle stays usable and a record holding it keeps the node
//!   live until the record itself ends (record-held views gate drops).
//! - Reachability: `return`, `break`, `continue` and a break-free
//!   `while true` end their path; diverged paths never feed branch/loop
//!   joins or the fallthrough leak check. Loops join entry, body end,
//!   `continue` and `break` states (break-free `while true`: breaks only).
//!   Each branch starts from the pre-branch loan liveness. An owner consumed
//!   on only one of two reachable joined paths is `MEM203`.
//! - `Unsafe` blocks discharge only `UnsafeMemory` effect permission. They
//!   NEVER disable owner/borrow/provenance checks here.
//! - Disjoint partitions of one arena coexist: constant ranges are proved at
//!   compile time (constant overlap is `MEM202`, constant out-of-bounds is
//!   `MEM207`); genuinely dynamic pairs stay legal and get a bounded
//!   `SalMemoryAssertDisjoint` runtime check before user code runs. Dynamic
//!   overlap therefore traps at runtime instead of corrupting memory.
//! - Parent loans suspend while derived children live: mutation (`put`),
//!   owner consume, and parent `borrow_end` with live children are `MEM205`.
//!   Deriving a provably disjoint sibling and `len` metadata are permitted.
//! - Rejected: forged owners/casts (`MEM206`, incl. `address` of owners or
//!   live exclusive `Borrow<T>` handles, owners in C ABI exports or channel
//!   payloads; bounded spans address normally but still require
//!   `UnsafeMemory`), double moves/drops (`MEM203`), drops/moves with live
//!   views (`MEM205`), local-rooted returns (`MEM204`, incl. via internal
//!   records), lending an owner that a later argument consumes (`MEM205`),
//!   constant past-the-end loans (`MEM207`), and leaked owners at exit (`MEM208`).
//! - `operation.ownership.lowered` / `generated` flags are NEVER consulted:
//!   ordinary source operations lower too, so they cannot serve as origin,
//!   and generated items are never exempt from safety checks.
//!
//! IDEMPOTENCE: files without any memory surface return cloned. Guard
//! re-insertion is suppressed only by the exact unconditional guard
//! statement at the new-loan point; arbitrary source-present
//! `SalMemoryAssertDisjoint` calls elsewhere are never trusted.

use sal_syntax::{Diagnostic, Expr, Item, OperationDecl, Severity, Span, Stmt, TypeRef};
use std::collections::{BTreeSet, HashMap};

pub const MEM_STALE: &str = "MEM201";
pub const MEM_OVERLAP: &str = "MEM202";
pub const MEM_CONSUME: &str = "MEM203";
pub const MEM_ESCAPE: &str = "MEM204";
pub const MEM_LIVE_BORROW: &str = "MEM205";
pub const MEM_FORGE: &str = "MEM206";
pub const MEM_BOUNDS: &str = "MEM207";
pub const MEM_LEAK: &str = "MEM208";

const MAX_WALK: usize = 65536;

fn err(code: &'static str, message: String, span: &Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span: span.clone(),
        suggestion: None,
    }
}

// ---------------------------------------------------------------------------
// File-level probes.
// ---------------------------------------------------------------------------

fn call_mentions_memory(name: &str) -> bool {
    matches!(
        name,
        "buffer"
            | "buffer_drop"
            | "borrow_mut"
            | "slice_mut"
            | "slice"
            | "view"
            | "put"
            | "borrow_end"
            | "borrow"
            | "bytes"
            | "byte"
            | "text"
            | "len"
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
            | "channel"
            | "send"
            | "address"
            | "bytes_at"
            | "SalMemoryAssertDisjoint"
            | "SalContractAssert"
    )
}

fn type_mentions_memory(ty: &TypeRef) -> bool {
    match ty {
        TypeRef::Named(name) => !matches!(
            name.as_str(),
            "bool"
                | "String"
                | "UUID"
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
                | "Word"
                | "Character"
        ),
        TypeRef::Generic { args, .. } => args.iter().any(type_mentions_memory),
    }
}

fn expr_has_call(expr: &Expr, names: &dyn Fn(&str) -> bool) -> bool {
    let mut stack = vec![expr];
    let mut steps = 0usize;
    while let Some(expr) = stack.pop() {
        steps += 1;
        if steps > MAX_WALK {
            return true;
        }
        match expr {
            Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
            Expr::Not(inner) => stack.push(inner),
            Expr::Field { base, .. } => stack.push(base),
            Expr::Index { base, index } => {
                stack.push(base);
                stack.push(index);
            }
            Expr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Expr::Call { name, args } => {
                if names(name) {
                    return true;
                }
                stack.extend(args.iter());
            }
        }
    }
    false
}

fn block_has_call(body: &[Stmt], names: &dyn Fn(&str) -> bool) -> bool {
    let mut stmts: Vec<&Stmt> = body.iter().collect();
    let mut steps = 0usize;
    while let Some(stmt) = stmts.pop() {
        steps += 1;
        if steps > MAX_WALK {
            return true;
        }
        match stmt {
            Stmt::Let { expr, .. }
            | Stmt::Assign { expr, .. }
            | Stmt::Return(expr)
            | Stmt::ExprStmt(expr) => {
                if expr_has_call(expr, names) {
                    return true;
                }
            }
            Stmt::If { cond, then, else_ } => {
                if expr_has_call(cond, names) {
                    return true;
                }
                stmts.extend(then.iter());
                stmts.extend(else_.iter());
            }
            Stmt::While { cond, body } => {
                if expr_has_call(cond, names) {
                    return true;
                }
                stmts.extend(body.iter());
            }
            Stmt::For { iter, body, .. } => {
                if expr_has_call(iter, names) {
                    return true;
                }
                stmts.extend(body.iter());
            }
            Stmt::Unsafe { body } => stmts.extend(body.iter()),
            Stmt::Break | Stmt::Continue => {}
        }
    }
    false
}

fn file_mentions_call(file: &sal_syntax::SalFile, names: &dyn Fn(&str) -> bool) -> bool {
    for item in &file.items {
        if let Item::Operation(op) = item {
            if block_has_call(&op.body, names) {
                return true;
            }
        }
    }
    false
}

/// Cheap bounded iterative scan: true when any operation body calls
/// `buffer(...)` or `buffer_drop(...)` (including inside `unsafe:` blocks
/// and nested call arguments). Used by the source loader to auto-include
/// sealed `std/buffer.sal` through the normal import path.
pub fn requires_buffer_runtime(file: &sal_syntax::SalFile) -> bool {
    file_mentions_call(file, &|name| name == "buffer" || name == "buffer_drop")
}

/// Cheap bounded iterative scan: true when any operation body calls the
/// `text(...)` intrinsic. Used by the source loader to auto-include sealed
/// `std/text.sal` so SAL source cannot counterfeit `TextValidate` and so
/// invalid-UTF8-to-`Text` conversions resolve the genuine runtime.
pub fn requires_text_runtime(file: &sal_syntax::SalFile) -> bool {
    file_mentions_call(file, &|name| name == "text")
}

fn mentions_memory(file: &sal_syntax::SalFile) -> bool {
    for item in &file.items {
        match item {
            Item::Entity(entity) => {
                if entity.fields.iter().any(|f| type_mentions_memory(&f.ty)) {
                    return true;
                }
            }
            Item::Operation(op) => {
                if op.accepts.iter().any(|p| type_mentions_memory(&p.ty))
                    || op.returns.as_ref().is_some_and(type_mentions_memory)
                {
                    return true;
                }
                if block_has_call(&op.body, &call_mentions_memory) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Type tables.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum OwnKind {
    Buffer,
    Vector,
    Map,
}

#[derive(Clone)]
struct EntityInfo {
    fields: Vec<(String, TypeRef)>,
    c_layout: bool,
    has_span: bool,
}

fn entity_table(file: &sal_syntax::SalFile) -> HashMap<String, EntityInfo> {
    let mut table = HashMap::new();
    for item in &file.items {
        if let Item::Entity(entity) = item {
            table.insert(
                entity.name.clone(),
                EntityInfo {
                    fields: entity
                        .fields
                        .iter()
                        .map(|f| (f.name.clone(), f.ty.clone()))
                        .collect(),
                    c_layout: entity.c_layout,
                    has_span: false,
                },
            );
        }
    }
    // Fixpoint: a record carries spans if any field is an owner / loan /
    // borrow, or a record that already carries spans.
    loop {
        let mut changed = false;
        let names: Vec<String> = table.keys().cloned().collect();
        for name in names {
            if table[&name].has_span {
                continue;
            }
            let fields = table[&name].fields.clone();
            let mut carries = false;
            for (_, ty) in &fields {
                if direct_span_type(ty) || transitive_span_type(ty, &table) {
                    carries = true;
                    break;
                }
            }
            if carries {
                table.get_mut(&name).expect("entity present").has_span = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    table
}

fn direct_span_type(ty: &TypeRef) -> bool {
    match ty {
        TypeRef::Named(name) => matches!(name.as_str(), "Buffer" | "MutBytes" | "Bytes" | "Text"),
        TypeRef::Generic { name, args } => {
            (name == "Vector" || name == "Map" || name == "Borrow") && !args.is_empty()
        }
    }
}

fn transitive_span_type(ty: &TypeRef, table: &HashMap<String, EntityInfo>) -> bool {
    match ty {
        TypeRef::Named(name) => table.get(name).is_some_and(|info| info.has_span),
        TypeRef::Generic { name, args } => {
            if name == "Vector" || name == "Map" || name == "Borrow" || name == "ValueResult" {
                return false;
            }
            args.iter()
                .any(|arg| direct_span_type(arg) || transitive_span_type(arg, table))
        }
    }
}

/// True when the internal (non-C) record `name` transitively carries a
/// view (Bytes/Text/MutBytes/Borrow, nested records, TextList, ...). Such
/// record bindings are loan holders for this pass, so `borrow_end(record)`
/// is the way to end the views they hold. Shared with the body checker.
pub(crate) fn record_carries_views(
    entities: &HashMap<String, sal_syntax::EntityDecl>,
    name: &str,
) -> bool {
    let mut stack = vec![name];
    let mut seen: Vec<&str> = Vec::new();
    while let Some(current) = stack.pop() {
        if seen.contains(&current) || seen.len() > MAX_WALK {
            continue;
        }
        seen.push(current);
        let Some(entity) = entities.get(current) else {
            continue;
        };
        if entity.c_layout {
            continue;
        }
        for field in &entity.fields {
            let mut types = vec![&field.ty];
            while let Some(ty) = types.pop() {
                if direct_span_type(ty) {
                    return true;
                }
                match ty {
                    TypeRef::Named(inner) => stack.push(inner),
                    TypeRef::Generic { args, .. } => types.extend(args.iter()),
                }
            }
        }
    }
    false
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TyKind {
    Owner(OwnKind),
    Borrow,
    Span,
    RecordSpan,
    Plain,
}

fn classify_type(ty: &TypeRef, entities: &HashMap<String, EntityInfo>) -> TyKind {
    match ty {
        TypeRef::Named(name) => {
            if name == "Buffer" {
                return TyKind::Owner(OwnKind::Buffer);
            }
            if matches!(name.as_str(), "MutBytes" | "Bytes" | "Text") {
                return TyKind::Span;
            }
            if entities.get(name).is_some_and(|info| info.has_span) {
                return TyKind::RecordSpan;
            }
            TyKind::Plain
        }
        TypeRef::Generic { name, args } => {
            if name == "Vector" && !args.is_empty() {
                return TyKind::Owner(OwnKind::Vector);
            }
            if name == "Map" && !args.is_empty() {
                return TyKind::Owner(OwnKind::Map);
            }
            if name == "Borrow" && !args.is_empty() {
                return TyKind::Borrow;
            }
            if name == "ValueResult" || name == "Vec" {
                return TyKind::Plain;
            }
            if args
                .iter()
                .any(|arg| classify_type(arg, entities) != TyKind::Plain)
            {
                return TyKind::RecordSpan;
            }
            TyKind::Plain
        }
    }
}

#[derive(Clone)]
struct OpSig {
    params: Vec<(String, TypeRef)>,
    returns: Option<TypeRef>,
    declared_roots: Vec<String>,
}

fn op_table(file: &sal_syntax::SalFile) -> HashMap<String, OpSig> {
    let mut table = HashMap::new();
    for item in &file.items {
        if let Item::Operation(op) = item {
            table.entry(op.name.clone()).or_insert(OpSig {
                params: op
                    .accepts
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect(),
                returns: op.returns.clone(),
                declared_roots: op.ownership.return_from.clone(),
            });
        }
    }
    table
}

// ---------------------------------------------------------------------------
// Flow values.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Root {
    Slot(usize),
    Static,
}

#[derive(Clone)]
struct SlotInfo {
    /// False for slots created by `let` inside the analyzed operation.
    external: bool,
    /// Name of the operation parameter this slot was created for, if any.
    param: Option<String>,
    /// Known total length for `buffer(usize(N))` owners.
    size: Option<u64>,
}

#[derive(Clone)]
struct NodeInfo {
    root: Root,
    parent: Option<usize>,
    /// Absolute `(offset, length)` in the root frame when fully constant.
    abs: Option<(u64, u64)>,
    mutable: bool,
    borrow: bool,
    live: bool,
    var: Option<String>,
    /// Field path from the root binding, e.g. `value.text`: guards compare
    /// actual field bytes, not whole-aggregate windows.
    field_path: Vec<String>,
    /// Span-site id for aggregate-view results: disjointness of two views
    /// into different record fields compares field paths, never whole
    /// storage windows.
    span_site: Option<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Estate {
    Live,
    Moved,
    Dropped,
}

#[derive(Clone)]
enum Val {
    Void,
    Unknown,
    Plain,
    Owner {
        slot: usize,
        kind: OwnKind,
    },
    Loan {
        node: usize,
    },
    Alias {
        prov: BTreeSet<Root>,
        nodes: Vec<usize>,
    },
    Record {
        prov: BTreeSet<Root>,
        nodes: Vec<usize>,
    },
}

impl Val {
    fn roots(&self, checker: &Checker<'_>) -> BTreeSet<Root> {
        match self {
            Val::Owner { slot, .. } => BTreeSet::from([Root::Slot(*slot)]),
            Val::Loan { node } => checker
                .nodes
                .get(*node)
                .map(|n| BTreeSet::from([n.root]))
                .unwrap_or_default(),
            Val::Alias { prov, .. } | Val::Record { prov, .. } => prov.clone(),
            Val::Void | Val::Unknown | Val::Plain => BTreeSet::new(),
        }
    }

    fn nodes(&self) -> Vec<usize> {
        match self {
            Val::Loan { node } => vec![*node],
            Val::Alias { nodes, .. } | Val::Record { nodes, .. } => nodes.clone(),
            _ => Vec::new(),
        }
    }
}

struct Binding {
    val: Val,
    estate: Option<Estate>,
}

#[derive(Clone, Copy)]
struct Ctx {
    stored: bool,
    returned: bool,
}

#[derive(Clone)]
struct Snapshot {
    bindings: HashMap<String, (Val, Option<Estate>)>,
    binding_ty: HashMap<String, TypeRef>,
    binding_path: HashMap<String, Vec<String>>,
    nodes: Vec<NodeInfo>,
    consts: HashMap<String, u64>,
    /// The path that produced this state already left the block
    /// (`return`, `break`, `continue`, or a break-free `while true`).
    diverged: bool,
}

/// Exit states collected while analyzing one loop body.
#[derive(Default)]
struct LoopFrame {
    breaks: Vec<Snapshot>,
    continues: Vec<Snapshot>,
}

// ---------------------------------------------------------------------------
// Checker.
// ---------------------------------------------------------------------------

struct Checker<'a> {
    entities: &'a HashMap<String, EntityInfo>,
    ops: &'a HashMap<String, OpSig>,
    op_name: String,
    op_span: Span,
    diags: Vec<Diagnostic>,
    bindings: HashMap<String, Binding>,
    /// Declared/record type per binding for field-sensitive projection
    /// (`decoded.written` is Plain; `decoded.value` keeps provenance).
    binding_ty: HashMap<String, TypeRef>,
    /// Field path per binding, e.g. `value.text` for `let t = r.value.text`.
    binding_path: HashMap<String, Vec<String>>,
    /// Fresh span-site ids for aggregate-view loan results.
    next_site: usize,
    nodes: Vec<NodeInfo>,
    slots: Vec<SlotInfo>,
    consts: HashMap<String, u64>,
    temps: Vec<usize>,
    /// Current path is unreachable: statements after it are dead and its
    /// state never flows into joins or the fallthrough exit check.
    diverged: bool,
    loops: Vec<LoopFrame>,
}

impl<'a> Checker<'a> {
    fn new(
        entities: &'a HashMap<String, EntityInfo>,
        ops: &'a HashMap<String, OpSig>,
        op_name: String,
        op_span: Span,
    ) -> Self {
        Checker {
            entities,
            ops,
            op_name,
            op_span,
            diags: Vec::new(),
            bindings: HashMap::new(),
            binding_ty: HashMap::new(),
            binding_path: HashMap::new(),
            next_site: 0,
            nodes: Vec::new(),
            slots: Vec::new(),
            consts: HashMap::new(),
            temps: Vec::new(),
            diverged: false,
            loops: Vec::new(),
        }
    }

    fn fail(&mut self, code: &'static str, message: String) {
        self.diags.push(err(code, message, &self.op_span));
    }

    fn fresh_slot(&mut self, external: bool, param: Option<String>, size: Option<u64>) -> usize {
        let id = self.slots.len();
        self.slots.push(SlotInfo {
            external,
            param,
            size,
        });
        id
    }

    fn snapshot(&self) -> Snapshot {
        Snapshot {
            bindings: self
                .bindings
                .iter()
                .map(|(k, b)| (k.clone(), (b.val.clone(), b.estate)))
                .collect(),
            binding_ty: self.binding_ty.clone(),
            binding_path: self.binding_path.clone(),
            nodes: self.nodes.clone(),
            consts: self.consts.clone(),
            diverged: self.diverged,
        }
    }

    /// Reset the whole flow state to `snap`. Loan nodes created after the
    /// snapshot (on a sibling path) keep their ids as dead placeholders, so
    /// later paths never reuse an id and never feel a sibling path's loans.
    fn restore(&mut self, snap: Snapshot) {
        let mut nodes = snap.nodes;
        for node in self.nodes.iter().skip(nodes.len()) {
            let mut placeholder = node.clone();
            placeholder.live = false;
            placeholder.var = None;
            nodes.push(placeholder);
        }
        self.nodes = nodes;
        self.bindings = snap
            .bindings
            .into_iter()
            .map(|(k, (val, estate))| (k, Binding { val, estate }))
            .collect();
        self.binding_ty = snap.binding_ty;
        self.binding_path = snap.binding_path;
        self.consts = snap.consts;
        self.diverged = snap.diverged;
        self.temps.clear();
    }

    /// Join two path-end states back into `self`. A diverged path never
    /// contributes. Between reachable paths a binding/node live on either
    /// path stays live (fail-safe for cleanup tails shared across branches)
    /// and integer constants survive only on agreement. An owner consumed
    /// on one reachable path but live on the other has no single state
    /// afterwards: that is `MEM203`.
    fn join(&mut self, a: Snapshot, b: Snapshot) {
        match (a.diverged, b.diverged) {
            (true, true) => {
                self.restore(a);
                self.diverged = true;
                return;
            }
            (true, false) => {
                self.restore(b);
                return;
            }
            (false, true) => {
                self.restore(a);
                return;
            }
            (false, false) => {}
        }
        let mut bindings: HashMap<String, Binding> = HashMap::new();
        let mut binding_ty: HashMap<String, TypeRef> = HashMap::new();
        let mut binding_path: HashMap<String, Vec<String>> = HashMap::new();
        let mut names: Vec<&String> = a.bindings.keys().chain(b.bindings.keys()).collect();
        names.sort();
        names.dedup();
        let len = a.nodes.len().max(b.nodes.len());
        let mut nodes = Vec::with_capacity(len);
        for i in 0..len {
            match (a.nodes.get(i), b.nodes.get(i)) {
                (Some(na), Some(nb)) => {
                    let mut merged = na.clone();
                    merged.live = na.live || nb.live;
                    if merged.var.is_none() {
                        merged.var.clone_from(&nb.var);
                    }
                    nodes.push(merged);
                }
                (Some(n), None) | (None, Some(n)) => nodes.push(n.clone()),
                (None, None) => {}
            }
        }
        for name in names {
            let (Some((va, ea)), Some((vb, eb))) = (a.bindings.get(name), b.bindings.get(name))
            else {
                let (snap, (v, e)) = match a.bindings.get(name) {
                    Some(found) => (&a, found),
                    None => (&b, b.bindings.get(name).expect("name present")),
                };
                bindings.insert(
                    name.clone(),
                    Binding {
                        val: v.clone(),
                        estate: *e,
                    },
                );
                if let Some(ty) = snap.binding_ty.get(name) {
                    binding_ty.insert(name.clone(), ty.clone());
                }
                if let Some(path) = snap.binding_path.get(name) {
                    binding_path.insert(name.clone(), path.clone());
                }
                continue;
            };
            let estate = match (ea, eb) {
                (Some(Estate::Live), Some(Estate::Live)) => Some(Estate::Live),
                (Some(Estate::Live), Some(_)) | (Some(_), Some(Estate::Live)) => {
                    self.fail(
                        MEM_CONSUME,
                        format!(
                            "`{name}` is consumed on only one branch; consume affine owners on every path or none"
                        ),
                    );
                    Some(Estate::Live)
                }
                (Some(x), _) => Some(*x),
                (None, other) => *other,
            };
            // Fail-safe provenance: a value live on either path carries the
            // UNION of both paths' roots, so a local-rooted escape on one
            // path cannot hide behind a clean path (and static-empty
            // branches stay accepted alongside proved input roots).
            let val = union_provenance(va, vb, &nodes);
            bindings.insert(name.clone(), Binding { val, estate });
            match (a.binding_ty.get(name), b.binding_ty.get(name)) {
                (Some(ta), Some(tb)) if ta == tb => {
                    binding_ty.insert(name.clone(), ta.clone());
                }
                (None, None) => {}
                _ => {
                    binding_ty.insert(name.clone(), TypeRef::Named("Unknown".into()));
                }
            }
            if let (Some(pa), Some(pb)) = (a.binding_path.get(name), b.binding_path.get(name)) {
                if pa == pb {
                    binding_path.insert(name.clone(), pa.clone());
                }
            }
        }
        self.bindings = bindings;
        self.binding_ty = binding_ty;
        self.binding_path = binding_path;
        self.nodes = nodes;
        let mut consts = HashMap::new();
        for (k, v) in &a.consts {
            if b.consts.get(k) == Some(v) {
                consts.insert(k.clone(), *v);
            }
        }
        self.consts = consts;
        self.diverged = false;
        self.temps.clear();
    }

    /// Join every collected exit state; no reachable exit means the
    /// construct itself diverges.
    fn join_all(&mut self, exits: Vec<Snapshot>) {
        let mut exits = exits.into_iter();
        let Some(first) = exits.next() else {
            self.diverged = true;
            return;
        };
        self.restore(first);
        for next in exits {
            let current = self.snapshot();
            self.join(current, next);
        }
    }

    fn const_int(&self, expr: &Expr) -> Option<u64> {
        match expr {
            Expr::Int(n) => (*n >= 0).then_some(*n as u64),
            Expr::Var(name) => self.consts.get(name).copied(),
            Expr::Call { name, args } if args.len() == 1 => {
                if is_int_cast(name) {
                    self.const_int(&args[0])
                } else {
                    None
                }
            }
            Expr::BinOp { op, left, right } => {
                let l = self.const_int(left)?;
                let r = self.const_int(right)?;
                match op {
                    sal_syntax::BinOp::Add => l.checked_add(r),
                    sal_syntax::BinOp::Sub => l.checked_sub(r),
                    sal_syntax::BinOp::Mul => l.checked_mul(r),
                    sal_syntax::BinOp::Div => (r != 0).then(|| l / r),
                    sal_syntax::BinOp::Rem => (r != 0).then(|| l % r),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn temp_register(&mut self, node: usize, ctx: Ctx) {
        if !ctx.stored && !ctx.returned {
            self.temps.push(node);
        }
    }

    /// Scope end for call-statement temporaries: every loan created while
    /// evaluating operands that was neither stored (`let`/assign/field-arg
    /// retention) nor returned expires here — exactly the
    /// "temporaries end with call/statement unless returned/stored" rule.
    /// Nodes still retained by a stored/returned record, alias, or live
    /// binding are NOT killed: retention, not creation context, decides.
    fn drain_temps(&mut self) {
        let retained = self.retained_nodes();
        for node in self.temps.drain(..) {
            if retained.contains(&node) {
                continue;
            }
            if let Some(info) = self.nodes.get_mut(node) {
                info.live = false;
            }
        }
    }

    /// Every loan node held by a live binding or a stored/returned value:
    /// union of all `Val::Loan`/`Alias`/`Record` node sets currently live.
    fn retained_nodes(&self) -> Vec<usize> {
        let mut held = Vec::new();
        for binding in self.bindings.values() {
            for node in binding.val.nodes() {
                if !held.contains(&node) {
                    held.push(node);
                }
            }
        }
        held
    }

    fn new_loan(
        &mut self,
        root: Root,
        parent: Option<usize>,
        abs: Option<(u64, u64)>,
        mutable: bool,
        borrow: bool,
        ctx: Ctx,
    ) -> usize {
        let id = self.nodes.len();
        self.nodes.push(NodeInfo {
            root,
            parent,
            abs,
            mutable,
            borrow,
            live: true,
            var: None,
            field_path: Vec::new(),
            span_site: None,
        });
        self.temp_register(id, ctx);
        id
    }

    fn live_descendant(&self, node: usize) -> bool {
        self.nodes.iter().any(|n| {
            n.live && {
                let mut p = n.parent;
                let mut found = false;
                while let Some(id) = p {
                    if id == node {
                        found = true;
                        break;
                    }
                    p = self.nodes.get(id).and_then(|info| info.parent);
                }
                found
            }
        })
    }

    /// True when `val` is a live exclusive `Borrow<T>` handle: owner
    /// identity, never a bounded span, so address exposure is forged.
    fn loan_is_exclusive_borrow(&self, val: &Val) -> bool {
        match val {
            Val::Loan { node } => self.nodes.get(*node).is_some_and(|n| n.live && n.borrow),
            _ => false,
        }
    }

    fn live_nodes_for_slot(&self, slot: usize) -> Vec<usize> {
        self.nodes
            .iter()
            .enumerate()
            .filter(|(_, n)| n.live && n.root == Root::Slot(slot))
            .map(|(i, _)| i)
            .collect()
    }

    /// Every live loan node a live record binding transitively retains for
    /// `slot`: the record's own `nodes` plus, for record bindings whose
    /// provenance includes the slot, the live nodes of every binding that
    /// shares that provenance chain. Records therefore gate owner
    /// drops/reuse exactly like direct loans: ending one alias never hides
    /// another live alias from `buffer_drop`/`borrow_end`/move checks.
    /// Ends one binding's loan. Nodes still held by another binding (a child
    /// view, a copied record) stay live and keep pressuring their owner; the
    /// ended name is rebound to a dead loan so later use is `MEM201`.
    fn end_binding(&mut self, var: &str) {
        let nodes = self
            .bindings
            .get(var)
            .map(|b| b.val.nodes())
            .unwrap_or_default();
        self.resolve_binding(var);
        let retained = self.retained_nodes();
        for node in nodes {
            if !retained.contains(&node) {
                if let Some(info) = self.nodes.get_mut(node) {
                    info.live = false;
                    info.var = None;
                }
            }
        }
    }

    /// Rebind `var` to a fresh ended loan without touching the nodes it
    /// held: later use is `MEM201`, `borrow_end` is an idempotent no-op.
    fn resolve_binding(&mut self, var: &str) {
        let dead = self.nodes.len();
        self.nodes.push(NodeInfo {
            root: Root::Static,
            parent: None,
            abs: None,
            mutable: false,
            borrow: false,
            live: false,
            var: Some(var.to_owned()),
            field_path: Vec::new(),
            span_site: None,
        });
        self.bindings.insert(
            var.to_owned(),
            Binding {
                val: Val::Loan { node: dead },
                estate: None,
            },
        );
    }

    fn record_held_nodes(&self, slot: usize) -> Vec<usize> {
        let mut held = Vec::new();
        for binding in self.bindings.values() {
            if let Val::Record { nodes, .. } = &binding.val {
                for node in nodes {
                    if self
                        .nodes
                        .get(*node)
                        .is_some_and(|n| n.live && n.root == Root::Slot(slot))
                        && !held.contains(node)
                    {
                        held.push(*node);
                    }
                }
            }
        }
        held
    }

    /// Live loan pressure on one owner slot: direct live nodes plus
    /// record-retained nodes. Used by drop/move/consume checks.
    fn live_pressure_for_slot(&self, slot: usize) -> Vec<usize> {
        let mut all = self.live_nodes_for_slot(slot);
        for node in self.record_held_nodes(slot) {
            if !all.contains(&node) {
                all.push(node);
            }
        }
        all
    }

    /// Field path of an expression: the bound variable's recorded path
    /// extended through `.field` projections. `let t = r.value.text`
    /// records `value.text`; plain names record the empty path.
    fn field_path_of(&self, expr: &Expr) -> Vec<String> {
        match expr {
            Expr::Var(name) => self.binding_path.get(name).cloned().unwrap_or_default(),
            Expr::Field { base, field } => {
                let mut path = self.field_path_of(base);
                path.push(field.clone());
                path
            }
            _ => Vec::new(),
        }
    }

    /// Stamp a span-site id on aggregate-view results so two views into
    /// different record fields never compare whole-storage windows.
    fn fresh_site(&mut self) -> usize {
        let site = self.next_site;
        self.next_site += 1;
        site
    }

    /// True when `base.field` resolves to a plain (non-span) type, so the
    /// projection carries no borrowed roots. Unknown bases/fields stay
    /// fail-closed (treated as span-carrying) except when the field is
    /// provably a scalar projection.
    fn field_is_plain(&self, base: &Expr, field: &str) -> bool {
        let record = match base {
            // Branch joins turn records into aliases; the declared binding
            // type still names the record (or `Unknown` when the paths
            // disagree, which stays fail-closed).
            Expr::Var(name) => match self.bindings.get(name) {
                Some(Binding {
                    val: Val::Record { .. } | Val::Alias { .. },
                    ..
                }) => self.record_of_binding(name),
                _ => None,
            },
            _ => None,
        };
        let Some(entity_name) = record.or_else(|| self.record_of_call(base)) else {
            return false;
        };
        let Some(entity) = self.entities.get(&entity_name) else {
            return false;
        };
        entity
            .fields
            .iter()
            .find(|(name, _)| name == field)
            .is_none_or(|(_, ty)| classify_type(ty, self.entities) == TyKind::Plain)
    }

    /// Record entity name for a `let`-bound value when its declared type
    /// names one (call result type, entity construction, or copy source).
    fn record_of_binding(&self, name: &str) -> Option<String> {
        match self.binding_ty.get(name) {
            Some(TypeRef::Named(entity)) => Some(entity.clone()),
            _ => None,
        }
    }

    /// Record entity name for a call result from the callee signature.
    fn record_of_call(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Call { name, .. } => match self.ops.get(name) {
                Some(sig) => match &sig.returns {
                    Some(TypeRef::Named(entity)) => Some(entity.clone()),
                    _ => None,
                },
                None => self.entities.contains_key(name).then(|| name.clone()),
            },
            Expr::Field { base, field } => self
                .record_of_expr(base)
                .and_then(|r| self.entities.get(&r))
                .and_then(|info| info.fields.iter().find(|(n, _)| n == field))
                .and_then(|(_, ty)| match ty {
                    TypeRef::Named(entity) => Some(entity.clone()),
                    _ => None,
                }),
            _ => None,
        }
    }

    fn record_of_expr(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::Var(name) => self.record_of_binding(name),
            Expr::Call { .. } | Expr::Field { .. } => self.record_of_call(expr),
            _ => None,
        }
    }

    /// Declared/result type of an expression for field-sensitive
    /// projection: call return types, entity names under construction,
    /// copies inherit the source binding's type, field projections resolve
    /// through the base record's field list.
    fn expr_type(&self, expr: &Expr) -> TypeRef {
        match expr {
            Expr::Var(name) => self
                .binding_ty
                .get(name)
                .cloned()
                .unwrap_or(TypeRef::Named("Unknown".into())),
            Expr::Call { name, .. } => match self.ops.get(name) {
                Some(sig) => sig
                    .returns
                    .clone()
                    .unwrap_or(TypeRef::Named("Unknown".into())),
                None => {
                    if self.entities.contains_key(name) {
                        TypeRef::Named(name.clone())
                    } else {
                        TypeRef::Named("Unknown".into())
                    }
                }
            },
            Expr::Field { base, field } => self
                .record_of_expr(base)
                .and_then(|r| self.entities.get(&r))
                .and_then(|info| {
                    info.fields
                        .iter()
                        .find(|(n, _)| n == field)
                        .map(|(_, ty)| ty.clone())
                })
                .unwrap_or(TypeRef::Named("Unknown".into())),
            _ => TypeRef::Named("Unknown".into()),
        }
    }

    /// Evaluate `borrow_mut/slice_mut` (mutable=true) or `view/slice/bytes`
    /// (mutable=false) argument expressions EXACTLY once, in order, then
    /// derive the child loan from the already-bound actuals. The guard
    /// inserted at the new-loan `let` uses `view(new)`, `view(existing)`
    /// over bound bindings only: no re-evaluation of offset/length/whole
    /// expressions, and no accesses sit between creation and guard.
    fn loan_exact_once(&mut self, name: &str, args: &[Expr], mutable: bool, ctx: Ctx) -> Val {
        let mut vals = Vec::with_capacity(args.len());
        for arg in args {
            vals.push(self.analyze_expr(
                arg,
                Ctx {
                    stored: false,
                    returned: false,
                },
            ));
        }
        let first = vals.first().cloned().unwrap_or(Val::Unknown);
        let (parent_root, parent_abs, parent_len, parent_node) = match first {
            Val::Owner { slot, .. } => {
                let binding_live = match args.first() {
                    Some(Expr::Var(v)) => self.owner_estate(v) == Some(Estate::Live),
                    Some(_) => true,
                    None => false,
                };
                if !binding_live {
                    self.fail(
                        MEM_CONSUME,
                        format!("`{name}` borrows an owner that was already consumed"),
                    );
                    return Val::Unknown;
                }
                let size = match args.first() {
                    Some(Expr::Var(v)) => self.owner_size(v),
                    Some(_) | None => None,
                };
                (Root::Slot(slot), None, size, None)
            }
            Val::Loan { node } => match self.nodes.get(node).cloned() {
                Some(info) if info.live => (
                    info.root,
                    info.abs,
                    info.abs.map(|(_, len)| len),
                    Some(node),
                ),
                _ => {
                    self.fail(
                        MEM_STALE,
                        format!("`{name}` borrows from a loan that already ended"),
                    );
                    return Val::Unknown;
                }
            },
            Val::Alias { prov, nodes } | Val::Record { prov, nodes } => {
                let live: Vec<usize> = nodes
                    .into_iter()
                    .filter(|n| self.nodes.get(*n).is_some_and(|i| i.live))
                    .collect();
                let root = prov
                    .into_iter()
                    .find(|r| matches!(r, Root::Slot(_)))
                    .unwrap_or(Root::Static);
                (root, None, None, live.first().copied())
            }
            Val::Unknown => return Val::Unknown,
            _ => {
                self.fail(
                    MEM_CONSUME,
                    format!("`{name}` requires a live owner or loan handle"),
                );
                return Val::Unknown;
            }
        };
        if mutable {
            let off = args.get(1).and_then(|e| self.const_int(e));
            let len = args.get(2).and_then(|e| self.const_int(e));
            if let (Some(o), Some(l), Some(size)) = (off, len, parent_len) {
                match o.checked_add(l) {
                    Some(end) if end <= size => {}
                    _ => {
                        self.fail(
                            MEM_BOUNDS,
                            format!(
                                "`{name}` range [{o}, {o}+{l}) escapes its parent of length {size}"
                            ),
                        );
                        return Val::Unknown;
                    }
                }
            }
            let abs = match (off, len, parent_abs) {
                (Some(o), Some(l), _) if parent_abs.is_none() && is_owner_root(parent_root) => {
                    Some((o, l))
                }
                (Some(o), Some(l), Some((base, _))) => base.checked_add(o).map(|s| (s, l)),
                _ => None,
            };
            let node = self.new_loan(parent_root, parent_node, abs, true, false, ctx);
            Val::Loan { node }
        } else {
            let site = self.fresh_site();
            let val = self.derive_view(name, parent_root, parent_abs, parent_node, args, ctx);
            if let Val::Loan { node } = &val {
                if let Some(info) = self.nodes.get_mut(*node) {
                    info.span_site = Some(site);
                }
            }
            val
        }
    }

    /// Shared immutable-view derivation used by `loan_exact_once` for
    /// `view/slice/bytes` and by `text` for validated text: all operand
    /// expressions were already evaluated exactly once by the caller.
    fn derive_view(
        &mut self,
        name: &str,
        parent_root: Root,
        parent_abs: Option<(u64, u64)>,
        parent_node: Option<usize>,
        args: &[Expr],
        ctx: Ctx,
    ) -> Val {
        let abs = if name == "slice" {
            match (
                args.get(1).and_then(|e| self.const_int(e)),
                args.get(2).and_then(|e| self.const_int(e)),
                parent_abs,
            ) {
                (Some(o), Some(l), Some((base, total))) => {
                    match (o.checked_add(l), base.checked_add(o)) {
                        (Some(end), Some(start)) if end <= total => Some((start, l)),
                        _ => {
                            self.fail(
                                MEM_BOUNDS,
                                format!("`slice` range escapes its parent of length {total}"),
                            );
                            return Val::Unknown;
                        }
                    }
                }
                _ => None,
            }
        } else {
            parent_abs
        };
        let node = self.new_loan(parent_root, parent_node, abs, false, false, ctx);
        Val::Loan { node }
    }

    // -- binding helpers ------------------------------------------------

    fn check_loan_use(&mut self, name: &str, what: &str) -> Option<usize> {
        match self.bindings.get(name) {
            None => None,
            Some(Binding {
                val: Val::Loan { node },
                ..
            }) => {
                let node = *node;
                if self.nodes.get(node).is_some_and(|n| n.live) {
                    Some(node)
                } else {
                    self.fail(
                        MEM_STALE,
                        format!(
                            "`{name}` {what} after its loan ended; ended borrows cannot be reused"
                        ),
                    );
                    None
                }
            }
            Some(Binding {
                val: Val::Owner { .. },
                estate,
            }) => {
                if *estate == Some(Estate::Live) {
                    self.fail(
                        MEM_FORGE,
                        format!("`{name}` {what} expects a loan, not an owner handle"),
                    );
                } else {
                    self.fail(
                        MEM_CONSUME,
                        format!("`{name}` {what} after it was consumed"),
                    );
                }
                None
            }
            Some(_) => None,
        }
    }

    // -- operation entry -------------------------------------------------

    fn check_operation(&mut self, op: &mut OperationDecl) {
        if op.body.is_empty() {
            return;
        }
        for param in &op.accepts {
            let name = param.name.clone();
            match classify_type(&param.ty, self.entities) {
                TyKind::Owner(kind) => {
                    self.binding_ty.insert(name.clone(), param.ty.clone());
                    let slot = self.fresh_slot(true, Some(name.clone()), None);
                    self.bindings.insert(
                        name.clone(),
                        Binding {
                            val: Val::Owner { slot, kind },
                            estate: Some(Estate::Live),
                        },
                    );
                }
                TyKind::Borrow => {
                    self.binding_ty.insert(name.clone(), param.ty.clone());
                    let slot = self.fresh_slot(true, Some(name.clone()), None);
                    let node = self.nodes.len();
                    self.nodes.push(NodeInfo {
                        root: Root::Slot(slot),
                        parent: None,
                        abs: None,
                        mutable: false,
                        borrow: true,
                        live: true,
                        var: Some(name.clone()),
                        field_path: Vec::new(),
                        span_site: None,
                    });
                    self.bindings.insert(
                        name,
                        Binding {
                            val: Val::Loan { node },
                            estate: None,
                        },
                    );
                }
                TyKind::Span => {
                    self.binding_ty.insert(name.clone(), param.ty.clone());
                    let slot = self.fresh_slot(true, Some(name.clone()), None);
                    let node = self.nodes.len();
                    self.nodes.push(NodeInfo {
                        root: Root::Slot(slot),
                        parent: None,
                        abs: None,
                        mutable: matches!(&param.ty, TypeRef::Named(n) if n == "MutBytes"),
                        borrow: false,
                        live: true,
                        var: Some(name.clone()),
                        field_path: Vec::new(),
                        span_site: None,
                    });
                    self.bindings.insert(
                        name,
                        Binding {
                            val: Val::Loan { node },
                            estate: None,
                        },
                    );
                }
                TyKind::RecordSpan => {
                    self.binding_ty.insert(name.clone(), param.ty.clone());
                    let mut prov = BTreeSet::new();
                    prov.insert(Root::Static);
                    let slot = self.fresh_slot(true, Some(name.clone()), None);
                    prov.insert(Root::Slot(slot));
                    self.bindings.insert(
                        name,
                        Binding {
                            val: Val::Record {
                                prov,
                                nodes: Vec::new(),
                            },
                            estate: None,
                        },
                    );
                }
                TyKind::Plain => {
                    self.binding_ty.insert(name.clone(), param.ty.clone());
                    self.bindings.insert(
                        name.clone(),
                        Binding {
                            val: Val::Plain,
                            estate: None,
                        },
                    );
                    if let Some(v) = self.const_int(&Expr::Var(name.clone())) {
                        self.consts.insert(name, v);
                    }
                }
            }
        }
        let mut body = std::mem::take(&mut op.body);
        self.analyze_block(&mut body);
        op.body = body;
        if !self.diverged {
            self.check_exit(None);
        }
    }

    fn analyze_block(&mut self, stmts: &mut Vec<Stmt>) {
        let mut i = 0;
        while i < stmts.len() {
            if self.diverged {
                // Unreachable tail: no state flows from here.
                break;
            }
            let mut stmt = std::mem::replace(&mut stmts[i], Stmt::Break);
            let guards = self.analyze_stmt(&mut stmt);
            stmts[i] = stmt;
            let mut j = i + 1;
            for guard in guards {
                if stmts.get(j).is_some_and(|s| s == &guard) {
                    j += 1;
                } else {
                    stmts.insert(j, guard);
                    j += 1;
                }
            }
            i = j;
        }
    }

    fn analyze_stmt(&mut self, stmt: &mut Stmt) -> Vec<Stmt> {
        match stmt {
            Stmt::Let { name, expr, .. } => {
                let is_loan_ctor = is_mut_loan_call(expr);
                let val = self.analyze_expr(
                    expr,
                    Ctx {
                        stored: true,
                        returned: false,
                    },
                );
                self.drain_temps();
                if let Some(c) = self.const_int(expr) {
                    self.consts.insert(name.clone(), c);
                }
                let mut guards = Vec::new();
                if is_loan_ctor {
                    if let Val::Loan { node } = &val {
                        let node = *node;
                        if let Some(info) = self.nodes.get_mut(node) {
                            info.var = Some(name.clone());
                        }
                        guards = self.dynamic_guards(name, node);
                    }
                } else if let Val::Loan { node } = &val {
                    let node = *node;
                    if let Some(info) = self.nodes.get_mut(node) {
                        if info.var.is_none() {
                            info.var = Some(name.clone());
                        }
                    }
                }
                if let Some(binding) = self.bindings.get(name) {
                    if matches!(binding.val, Val::Owner { .. })
                        && binding.estate == Some(Estate::Live)
                    {
                        self.fail(
                            MEM_LEAK,
                            format!("`{name}` is rebound while still holding a live owner or loan"),
                        );
                    }
                }
                let estate = matches!(val, Val::Owner { .. }).then_some(Estate::Live);
                self.binding_ty.insert(name.clone(), self.expr_type(expr));
                self.binding_path
                    .insert(name.clone(), self.field_path_of(expr));
                self.bindings.insert(name.clone(), Binding { val, estate });
                guards
            }
            Stmt::Assign { name, expr } => {
                let val = self.analyze_expr(
                    expr,
                    Ctx {
                        stored: true,
                        returned: false,
                    },
                );
                self.drain_temps();
                self.consts.remove(name);
                if let Some(c) = self.const_int(expr) {
                    self.consts.insert(name.clone(), c);
                }
                if self.bindings.contains_key(name) {
                    if let Some(binding) = self.bindings.get(name) {
                        if binding_live(binding, &self.nodes) {
                            self.fail(
                                MEM_LEAK,
                                format!(
                                    "`{name}` is reassigned while still holding a live owner or loan"
                                ),
                            );
                        }
                    }
                    let estate = matches!(val, Val::Owner { .. }).then_some(Estate::Live);
                    self.binding_ty.insert(name.clone(), self.expr_type(expr));
                    self.binding_path
                        .insert(name.clone(), self.field_path_of(expr));
                    self.bindings.insert(name.clone(), Binding { val, estate });
                }
                Vec::new()
            }
            Stmt::Return(expr) => {
                let val = self.analyze_expr(
                    expr,
                    Ctx {
                        stored: false,
                        returned: true,
                    },
                );
                self.drain_temps();
                self.check_return(&val, expr);
                self.diverged = true;
                Vec::new()
            }
            Stmt::ExprStmt(expr) => {
                self.analyze_expr(
                    expr,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.drain_temps();
                Vec::new()
            }
            Stmt::If { cond, then, else_ } => {
                self.analyze_expr(
                    cond,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.drain_temps();
                let saved = self.snapshot();
                self.analyze_block(then);
                let a = self.snapshot();
                self.restore(saved);
                self.analyze_block(else_);
                let b = self.snapshot();
                self.join(a, b);
                Vec::new()
            }
            Stmt::While { cond, body } => {
                self.analyze_expr(
                    cond,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.drain_temps();
                let infinite = matches!(cond, Expr::Bool(true));
                self.analyze_loop(body, None, infinite);
                Vec::new()
            }
            Stmt::For { var, iter, body } => {
                self.analyze_expr(
                    iter,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.drain_temps();
                self.analyze_loop(body, Some(var.clone()), false);
                Vec::new()
            }
            Stmt::Unsafe { body } => {
                // Unsafe discharges effect permission only; every
                // owner/borrow/provenance check still applies.
                self.analyze_block(body);
                Vec::new()
            }
            Stmt::Break => {
                let snap = self.snapshot();
                if let Some(frame) = self.loops.last_mut() {
                    frame.breaks.push(snap);
                }
                self.diverged = true;
                Vec::new()
            }
            Stmt::Continue => {
                let snap = self.snapshot();
                if let Some(frame) = self.loops.last_mut() {
                    frame.continues.push(snap);
                }
                self.diverged = true;
                Vec::new()
            }
        }
    }

    /// One pass over a loop body. The state after the loop joins every
    /// reachable exit: `break` states always; for conditional loops also the
    /// entry state, the body-end state and `continue` states (the condition
    /// may fail at any loop head). A break-free `while true` has no exit and
    /// diverges, so nothing after it is reachable.
    fn analyze_loop(&mut self, body: &mut Vec<Stmt>, var: Option<String>, infinite: bool) {
        let entry = self.snapshot();
        if let Some(var) = var {
            self.bindings.insert(
                var,
                Binding {
                    val: Val::Plain,
                    estate: None,
                },
            );
        }
        self.loops.push(LoopFrame::default());
        self.analyze_block(body);
        let frame = self.loops.pop().unwrap_or_default();
        let end = self.snapshot();
        let mut exits = frame.breaks;
        if !infinite {
            exits.push(entry);
            exits.push(end);
            exits.extend(frame.continues);
        }
        self.join_all(exits);
    }

    /// Guards for a newly created mutable loan: one
    /// `SalMemoryAssertDisjoint(view(new), view(existing))` per live
    /// conflicting loan of the same root whose ranges are not provably
    /// disjoint. Constant overlap is a compile error instead. Field names
    /// never prove disjointness: two fields may view the same bytes.
    fn dynamic_guards(&mut self, name: &str, node: usize) -> Vec<Stmt> {
        let (root, abs) = match self.nodes.get(node) {
            Some(info) => (info.root, info.abs),
            None => return Vec::new(),
        };
        if root == Root::Static {
            // Static literal data is immutable and never shares bytes with
            // an owner mapping; there is nothing to prove disjoint.
            return Vec::new();
        }
        let mut ancestors = Vec::new();
        let mut cursor = self.nodes.get(node).and_then(|n| n.parent);
        while let Some(id) = cursor {
            ancestors.push(id);
            cursor = self.nodes.get(id).and_then(|n| n.parent);
        }
        let mut guards = Vec::new();
        for id in 0..self.nodes.len() {
            if id == node || ancestors.contains(&id) {
                continue;
            }
            let other = &self.nodes[id];
            if !other.live || other.root != root {
                continue;
            }
            if other.borrow {
                self.fail(
                    MEM_LIVE_BORROW,
                    format!("`{name}` aliases an exclusively borrowed owner; end the borrow first"),
                );
                continue;
            }
            match (abs, other.abs) {
                (Some(a), Some(b)) if !ranges_overlap(a, b) => {}
                (Some(a), Some(b)) if ranges_overlap(a, b) => {
                    self.fail(MEM_OVERLAP, format!("`{name}` overlaps a live loan of the same owner; disjoint partitions must not overlap"));
                }
                _ => {
                    let existing = match other.var.clone() {
                        Some(v) => v,
                        None => {
                            self.fail(
                                MEM_OVERLAP,
                                format!("`{name}` may overlap a live loan of the same owner"),
                            );
                            continue;
                        }
                    };
                    guards.push(disjoint_guard(name, &existing));
                }
            }
        }
        guards
    }

    fn check_return(&mut self, val: &Val, expr: &Expr) {
        let returned_var = match expr {
            Expr::Var(name) => Some(name.clone()),
            _ => None,
        };
        let declared: BTreeSet<String> = self
            .ops
            .get(&self.op_name)
            .map(|sig| sig.declared_roots.iter().cloned().collect())
            .unwrap_or_default();
        for root in val.roots(self) {
            if let Root::Slot(slot) = root {
                if let Some(info) = self.slots.get(slot).cloned() {
                    if !info.external {
                        self.fail(
                            MEM_ESCAPE,
                            "returned view is rooted in a local owner; views may only escape through caller inputs or static data".into(),
                        );
                    } else if let Some(param) = info.param {
                        if !declared.is_empty() && !declared.contains(&param) {
                            self.fail(
                                MEM_ESCAPE,
                                format!(
                                    "returned view is rooted in `{param}`, which is not listed in return_from"
                                ),
                            );
                        }
                    }
                }
            }
        }
        self.check_exit(returned_var);
    }

    fn check_exit(&mut self, returned_var: Option<String>) {
        let live_owners: Vec<(String, usize)> = self
            .bindings
            .iter()
            .filter_map(|(name, b)| match (&b.val, b.estate) {
                (Val::Owner { slot, .. }, Some(Estate::Live)) => {
                    if returned_var.as_deref() == Some(name.as_str()) {
                        None
                    } else {
                        Some((name.clone(), *slot))
                    }
                }
                _ => None,
            })
            .collect();
        for (name, _) in live_owners {
            self.fail(
                MEM_LEAK,
                format!(
                    "`{name}` is still owned at exit; affine owners must be dropped or transferred on every path"
                ),
            );
        }
    }

    // -- expressions ---------------------------------------------------

    fn analyze_expr(&mut self, expr: &Expr, ctx: Ctx) -> Val {
        match expr {
            Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) => Val::Plain,
            Expr::Not(inner) => {
                self.analyze_expr(
                    inner,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                Val::Plain
            }
            Expr::Var(name) => {
                let val = match self.bindings.get(name) {
                    Some(binding) => binding.val.clone(),
                    None => Val::Unknown,
                };
                match &val {
                    // Sharing one mutable node between two bindings would
                    // allow `put` through both with no overlap guard and let
                    // ending one alias hide the other from owner_drop.
                    // Mutable loans therefore NEVER alias implicitly: each
                    // copy is a tracked reborrow of the same root (child
                    // node, parent suspended), or, for `Borrow<T>`-exclusive
                    // handles, a rejected second live copy.
                    Val::Loan { node } => {
                        let node = *node;
                        let info = match self.nodes.get(node) {
                            Some(info) => info.clone(),
                            None => return Val::Unknown,
                        };
                        if !info.live {
                            self.fail(
                                MEM_STALE,
                                format!(
                                    "`{name}` is used after its loan ended; ended borrows cannot be reused"
                                ),
                            );
                            return Val::Unknown;
                        }
                        if info.mutable && ctx.stored {
                            if info.borrow {
                                self.fail(
                                    MEM_LIVE_BORROW,
                                    format!(
                                        "`{name}` is an exclusive borrow; it cannot be copied while live"
                                    ),
                                );
                                return Val::Unknown;
                            }
                            let child =
                                self.new_loan(info.root, Some(node), info.abs, true, false, ctx);
                            Val::Loan { node: child }
                        } else {
                            val
                        }
                    }
                    _ => val,
                }
            }
            Expr::Field { base, field } => {
                let val = self.analyze_expr(
                    base,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                match val {
                    Val::Record { prov, nodes } | Val::Alias { prov, nodes } => {
                        if self.field_is_plain(base, field) {
                            Val::Plain
                        } else {
                            let mut path = self.field_path_of(base);
                            path.push(field.clone());
                            for node in nodes.iter().copied() {
                                if let Some(info) = self.nodes.get_mut(node) {
                                    if info.live {
                                        info.field_path = path.clone();
                                    }
                                }
                            }
                            Val::Alias { prov, nodes }
                        }
                    }
                    Val::Plain | Val::Unknown => {
                        let _ = field;
                        Val::Unknown
                    }
                    Val::Owner { .. } | Val::Loan { .. } | Val::Void => {
                        self.fail(
                            MEM_FORGE,
                            format!(
                                "field `{field}` cannot be projected from an owner or loan handle"
                            ),
                        );
                        Val::Unknown
                    }
                }
            }
            Expr::Index { base, index } => {
                let base = self.analyze_expr(
                    base,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.analyze_expr(
                    index,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                match base {
                    Val::Plain | Val::Unknown => Val::Plain,
                    _ => {
                        self.fail(
                            MEM_FORGE,
                            "indexing applies to plain vectors only, not owners or loans".into(),
                        );
                        Val::Unknown
                    }
                }
            }
            Expr::BinOp { left, right, .. } => {
                self.analyze_expr(
                    left,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                self.analyze_expr(
                    right,
                    Ctx {
                        stored: false,
                        returned: false,
                    },
                );
                Val::Plain
            }
            Expr::Call { name, args } => self.analyze_call(name, args, ctx),
        }
    }

    #[allow(clippy::too_many_lines)]
    fn analyze_call(&mut self, name: &str, args: &[Expr], ctx: Ctx) -> Val {
        match name {
            "buffer" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                let size = args.first().and_then(|e| self.const_int(e));
                let slot = self.fresh_slot(false, None, size);
                Val::Owner {
                    slot,
                    kind: OwnKind::Buffer,
                }
            }
            "vector" | "map" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                let kind = if name == "vector" {
                    OwnKind::Vector
                } else {
                    OwnKind::Map
                };
                let slot = self.fresh_slot(false, None, None);
                Val::Owner { slot, kind }
            }
            "buffer_drop" | "vector_drop" | "map_drop" => {
                let expected = match name {
                    "buffer_drop" => OwnKind::Buffer,
                    "vector_drop" => OwnKind::Vector,
                    _ => OwnKind::Map,
                };
                if let Some(arg) = args.first() {
                    self.consume_owner(arg, expected, name);
                    for extra in &args[1..] {
                        self.analyze_expr(
                            extra,
                            Ctx {
                                stored: false,
                                returned: false,
                            },
                        );
                    }
                }
                Val::Void
            }
            "borrow" => {
                if let Some(arg) = args.first() {
                    let val = self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                    match (arg, val) {
                        (Expr::Var(var), Val::Owner { slot, .. }) => {
                            if self.owner_estate(var) != Some(Estate::Live) {
                                self.fail(
                                    MEM_CONSUME,
                                    format!("`{var}` is borrowed after it was consumed"),
                                );
                                return Val::Unknown;
                            }
                            if !self.live_pressure_for_slot(slot).is_empty() {
                                self.fail(
                                    MEM_LIVE_BORROW,
                                    format!(
                                        "`{var}` cannot be exclusively borrowed while loans are live"
                                    ),
                                );
                                return Val::Unknown;
                            }
                            let node =
                                self.new_loan(Root::Slot(slot), None, None, false, true, ctx);
                            return Val::Loan { node };
                        }
                        (_, Val::Unknown) => return Val::Unknown,
                        (Expr::Var(var), _) => {
                            self.fail(
                                MEM_CONSUME,
                                format!("borrow(`{var}`) requires an affine owner"),
                            );
                            return Val::Unknown;
                        }
                        _ => {
                            self.fail(
                                MEM_FORGE,
                                "borrow() requires the original owner slot binding".into(),
                            );
                            return Val::Unknown;
                        }
                    }
                }
                Val::Unknown
            }
            "borrow_mut" | "slice_mut" => self.loan_exact_once(name, args, true, ctx),
            "view" | "slice" | "bytes" => {
                // `bytes("literal")` with no variable base: static data.
                if name == "bytes" && !matches!(args.first(), Some(Expr::Var(_))) {
                    for arg in args {
                        self.analyze_expr(
                            arg,
                            Ctx {
                                stored: false,
                                returned: false,
                            },
                        );
                    }
                    let mut prov = BTreeSet::new();
                    prov.insert(Root::Static);
                    return Val::Alias {
                        prov,
                        nodes: Vec::new(),
                    };
                }
                self.loan_exact_once(name, args, false, ctx)
            }

            "text" => {
                // Single evaluation: analyze actuals once, then derive.
                let mut vals = Vec::with_capacity(args.len());
                for arg in args {
                    vals.push(self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    ));
                }
                let (base_val, base_var) = match (vals.first(), args.first()) {
                    (Some(v), Some(Expr::Var(var))) => (v.clone(), Some(var.clone())),
                    (Some(v), _) => (v.clone(), None),
                    _ => (Val::Unknown, None),
                };
                match (base_var, base_val) {
                    (Some(var), Val::Loan { node }) => {
                        if !self.nodes.get(node).is_some_and(|n| n.live) {
                            self.fail(
                                MEM_STALE,
                                format!("`{var}` is converted after its loan ended"),
                            );
                            return Val::Unknown;
                        }
                        // Native `text()` carries the input Bytes provenance:
                        // validated Text aliases the SAME root, read-only.
                        let (root, abs) = {
                            let info = &self.nodes[node];
                            (info.root, info.abs)
                        };
                        let child = self.new_loan(root, Some(node), abs, false, false, ctx);
                        Val::Loan { node: child }
                    }
                    (_, Val::Alias { prov, nodes }) => Val::Alias { prov, nodes },
                    (Some(var), _) => {
                        self.fail(MEM_FORGE, format!("text(`{var}`) requires live Bytes"));
                        Val::Unknown
                    }
                    _ => {
                        self.fail(MEM_FORGE, "text() requires a direct Bytes binding".into());
                        Val::Unknown
                    }
                }
            }
            "byte" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                if let (Some(Expr::Var(var)), Some(idx)) = (args.first(), args.get(1)) {
                    let live_nodes: Vec<usize> = match self.bindings.get(var) {
                        Some(Binding {
                            val: Val::Loan { node },
                            ..
                        }) => vec![*node],
                        Some(Binding {
                            val: Val::Alias { nodes, .. },
                            ..
                        })
                        | Some(Binding {
                            val: Val::Record { nodes, .. },
                            ..
                        }) => nodes.clone(),
                        Some(Binding {
                            val: Val::Owner { .. },
                            ..
                        }) => {
                            self.fail(MEM_STALE, format!("byte(`{var}`, ..) requires a live loan"));
                            Vec::new()
                        }
                        _ => Vec::new(),
                    };
                    for node in live_nodes {
                        match self.nodes.get(node) {
                            Some(info) if info.live => {
                                if let (Some(len), Some(i)) =
                                    (info.abs.map(|(_, l)| l), self.const_int(idx))
                                {
                                    if i >= len {
                                        self.fail(
                                            MEM_BOUNDS,
                                            format!("byte(`{var}`, {i}) escapes length {len}"),
                                        );
                                    }
                                }
                            }
                            _ => {
                                self.fail(
                                    MEM_STALE,
                                    format!("byte(`{var}`, ..) reads a loan that already ended"),
                                );
                            }
                        }
                    }
                }
                Val::Plain
            }
            "len" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                // Metadata only: permitted on owners, loans, and suspended
                // parents alike. Liveness is still reported for
                // moved/dropped handles to catch use-after-consume.
                if let Some(Expr::Var(var)) = args.first() {
                    match self.bindings.get(var) {
                        Some(Binding {
                            val: Val::Owner { .. },
                            estate: Some(Estate::Live),
                        }) => {}
                        Some(Binding {
                            val: Val::Loan { node },
                            ..
                        }) if self.nodes.get(*node).is_some_and(|n| n.live) => {}
                        Some(Binding {
                            val: Val::Alias { nodes, .. },
                            ..
                        })
                        | Some(Binding {
                            val: Val::Record { nodes, .. },
                            ..
                        }) if nodes
                            .iter()
                            .all(|n| self.nodes.get(*n).is_some_and(|i| i.live)) => {}
                        Some(Binding {
                            val: Val::Plain | Val::Unknown,
                            ..
                        }) => {}
                        Some(_) => {
                            self.fail(
                                MEM_STALE,
                                format!("len(`{var}`) reads a handle that already ended or was consumed"),
                            );
                        }
                        None => {}
                    }
                }
                Val::Plain
            }
            "put" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                let target = match args.first() {
                    Some(Expr::Var(var)) => var.clone(),
                    _ => {
                        self.fail(MEM_FORGE, "put() requires a direct loan binding".into());
                        return Val::Void;
                    }
                };
                let node = match self.check_loan_use(&target, "is written") {
                    Some(node) => node,
                    None => return Val::Void,
                };
                let info = self.nodes[node].clone();
                if !info.mutable || info.borrow {
                    self.fail(
                        MEM_LIVE_BORROW,
                        format!("put(`{target}`, ..) writes through a read-only view"),
                    );
                    return Val::Void;
                }
                if self.live_descendant(node) {
                    self.fail(
                        MEM_LIVE_BORROW,
                        format!(
                            "put(`{target}`, ..) mutates while a derived view is live; end the view first"
                        ),
                    );
                }
                if let (Some(len), Some(idx)) = (
                    info.abs.map(|(_, l)| l),
                    args.get(1).and_then(|e| self.const_int(e)),
                ) {
                    if idx >= len {
                        self.fail(
                            MEM_BOUNDS,
                            format!("put(`{target}`, {idx}) escapes length {len}"),
                        );
                    }
                }
                Val::Void
            }
            "borrow_end" => {
                if let Some(arg) = args.first() {
                    // Ending an already resolved handle (ended, moved into a
                    // stored result, or expired) is an idempotent no-op.
                    if let Expr::Var(var) = arg {
                        if let Some(Binding {
                            val: Val::Loan { node },
                            ..
                        }) = self.bindings.get(var)
                        {
                            if self.nodes.get(*node).is_some_and(|n| !n.live) {
                                return Val::Void;
                            }
                        }
                    }
                    let val = self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                    match (arg, &val) {
                        (Expr::Var(_), Val::Owner { .. }) => self.fail(
                            MEM_CONSUME,
                            "borrow_end() ends loans, not owners; drop owners with buffer_drop/vector_drop/map_drop".into(),
                        ),
                        (Expr::Var(var), Val::Loan { .. } | Val::Alias { .. } | Val::Record { .. }) => {
                            self.end_binding(var);
                        }
                        _ => {}
                    }
                    for extra in &args[1..] {
                        self.analyze_expr(
                            extra,
                            Ctx {
                                stored: false,
                                returned: false,
                            },
                        );
                    }
                }
                Val::Void
            }
            "SalMemoryAssertDisjoint" | "SalContractAssert" => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                self.drain_temps();
                Val::Void
            }
            _ if is_int_cast(name) || is_numeric_op(name) => {
                // Opaque owners/spans never convert into integers.
                if args.len() == 1 {
                    let val = self.analyze_expr(
                        args.first().expect("checked arity"),
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                    if matches!(val, Val::Owner { .. } | Val::Loan { .. })
                        || record_or_alias_with_roots(&val)
                    {
                        self.fail(
                            MEM_FORGE,
                            format!(
                                "call `{name}` cannot convert an owner or loan into an integer"
                            ),
                        );
                        return Val::Unknown;
                    }
                    return Val::Plain;
                }
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                Val::Plain
            }
            _ if name == "address" || name == "bytes_at" => {
                let mut vals = Vec::new();
                for arg in args {
                    vals.push(self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    ));
                }
                let owner_leak = vals
                    .iter()
                    .any(|v| matches!(v, Val::Owner { .. }) || self.loan_is_exclusive_borrow(v));
                if owner_leak {
                    self.fail(MEM_FORGE, format!("call `{name}` cannot expose an affine owner handle as a raw address; bounded Bytes/Text/MutBytes spans address normally but owner identity never leaks"));
                    return Val::Unknown;
                }
                Val::Plain
            }
            _ if is_raw_mem(name) => {
                let mut vals = Vec::new();
                for arg in args {
                    vals.push(self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    ));
                }
                if vals.iter().any(|v| {
                    matches!(v, Val::Owner { .. } | Val::Loan { .. })
                        || record_or_alias_with_roots(v)
                }) {
                    self.fail(MEM_FORGE, format!("call `{name}` cannot expose an owner or loan as raw memory, even inside unsafe:"));
                    return Val::Unknown;
                }
                Val::Plain
            }
            _ if name == "channel" || name == "send" => {
                let mut vals = Vec::new();
                for arg in args {
                    vals.push(self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    ));
                }
                if vals.iter().any(|v| {
                    matches!(v, Val::Owner { .. } | Val::Loan { .. })
                        || record_or_alias_with_roots(v)
                }) {
                    self.fail(
                        MEM_FORGE,
                        format!("channel payloads cannot carry owners or loans (`{name}`)"),
                    );
                    return Val::Unknown;
                }
                Val::Plain
            }
            _ if self.entities.contains_key(name) => {
                // Internal record construction: positional fields.
                let info = self.entities[name].clone();
                if info.c_layout {
                    for arg in args {
                        let val = self.analyze_expr(
                            arg,
                            Ctx {
                                stored: false,
                                returned: false,
                            },
                        );
                        if matches!(val, Val::Owner { .. } | Val::Loan { .. })
                            || record_or_alias_with_roots(&val)
                        {
                            self.fail(
                                MEM_FORGE,
                                format!("C-layout record `{name}` cannot hold owners or loans"),
                            );
                        }
                    }
                    return Val::Plain;
                }
                let mut prov = BTreeSet::new();
                let mut nodes = Vec::new();
                for arg in args {
                    let val = self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                    prov.extend(val.roots(self));
                    for node in val.nodes() {
                        // Ending the parent handle below must not erase a
                        // live view now owned by this record: records retain
                        // the actual loan nodes, so record-held views gate
                        // owner drops/reuse until the record itself is dead.
                        if self.nodes.get(node).is_some_and(|n| n.live) && !nodes.contains(&node) {
                            nodes.push(node);
                        }
                    }
                }
                if prov.is_empty() {
                    prov.insert(Root::Static);
                }
                Val::Record { prov, nodes }
            }
            _ => self.analyze_user_call(name, args, ctx),
        }
    }

    fn analyze_user_call(&mut self, name: &str, args: &[Expr], ctx: Ctx) -> Val {
        let sig = match self.ops.get(name) {
            Some(sig) => sig.clone(),
            None => {
                for arg in args {
                    self.analyze_expr(
                        arg,
                        Ctx {
                            stored: false,
                            returned: false,
                        },
                    );
                }
                return Val::Plain;
            }
        };
        let mut arg_vals = Vec::with_capacity(args.len());
        for arg in args {
            arg_vals.push(self.analyze_expr(
                arg,
                Ctx {
                    stored: false,
                    returned: false,
                },
            ));
        }
        // Evaluate arguments in order. The original owner slot is locked
        // before later arguments: an owner consumed as a later argument
        // while an earlier argument still borrows from it is rejected, so a
        // later argument can never free an owner an earlier loan needs.
        for (index, (formal, val)) in sig.params.iter().zip(arg_vals.iter()).enumerate() {
            let actual = args.get(index);
            let kind = classify_type(&formal.1, self.entities);
            let var = match actual {
                Some(Expr::Var(v)) => Some(v.clone()),
                _ => None,
            };
            match kind {
                TyKind::Owner(_) => {
                    if let Some(v) = var {
                        match self.bindings.get(&v) {
                            Some(Binding {
                                val: Val::Owner { slot, .. },
                                estate: Some(Estate::Live),
                            }) => {
                                let slot = *slot;
                                let mut live = self.live_pressure_for_slot(slot);
                                // Earlier span/borrow actuals in this same
                                // call that root at this slot keep it locked
                                // even if their nodes were forwarded/expired
                                // above: re-derive liveness from arg_vals.
                                for prior in arg_vals.iter().take(index) {
                                    for r in prior.roots(self) {
                                        if r == Root::Slot(slot) {
                                            live.push(usize::MAX);
                                            break;
                                        }
                                    }
                                }
                                if !live.is_empty() {
                                    self.fail(
                                        MEM_LIVE_BORROW,
                                        format!(
                                            "`{v}` cannot move into `{name}` while a derived loan is live"
                                        ),
                                    );
                                } else if let Some(b) = self.bindings.get_mut(&v) {
                                    b.estate = Some(Estate::Moved);
                                    self.consts.remove(&v);
                                }
                            }
                            Some(Binding {
                                val: Val::Owner { .. },
                                ..
                            }) => {
                                self.fail(
                                    MEM_CONSUME,
                                    format!("`{v}` is moved into `{name}` after it was consumed"),
                                );
                            }
                            Some(_) => {
                                self.fail(
                                    MEM_CONSUME,
                                    format!(
                                        "`{v}` cannot move into `{name}`; expected an affine owner"
                                    ),
                                );
                            }
                            None => {}
                        }
                    } else if !matches!(val, Val::Unknown) {
                        self.fail(
                            MEM_FORGE,
                            format!(
                                "`{name}` expects the original owner slot binding for `{}`",
                                formal.0
                            ),
                        );
                    }
                    let _ = formal;
                }
                TyKind::Borrow => {
                    // Reborrow: the original slot stays live; no consume.
                    if let Some(v) = var {
                        let live = match self.bindings.get(&v) {
                            Some(Binding {
                                val: Val::Owner { .. },
                                estate: Some(Estate::Live),
                            }) => true,
                            Some(Binding {
                                val: Val::Loan { node },
                                ..
                            }) => self.nodes.get(*node).is_some_and(|n| n.live),
                            None => true,
                            _ => false,
                        };
                        if !live {
                            self.fail(
                                MEM_STALE,
                                format!("`{v}` is reborrowed after it ended or was consumed"),
                            );
                        }
                    } else if let Some(Expr::Call {
                        name: callee,
                        args: inner,
                    }) = actual
                    {
                        if callee == "borrow" {
                            if let Some(Expr::Var(v)) = inner.first() {
                                let live = match self.bindings.get(v) {
                                    Some(Binding {
                                        val: Val::Owner { .. },
                                        estate: Some(Estate::Live),
                                    }) => true,
                                    Some(Binding {
                                        val: Val::Loan { node },
                                        ..
                                    }) => self.nodes.get(*node).is_some_and(|n| n.live),
                                    None => true,
                                    _ => false,
                                };
                                if !live {
                                    self.fail(
                                        MEM_STALE,
                                        format!(
                                            "`{v}` is reborrowed after it ended or was consumed"
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
                TyKind::Span | TyKind::RecordSpan => {
                    if let Some(v) = var {
                        match self.bindings.get(&v) {
                            Some(Binding {
                                val: Val::Loan { node },
                                ..
                            }) if self.nodes.get(*node).is_some_and(|n| !n.live) => {
                                self.fail(
                                    MEM_STALE,
                                    format!("`{v}` is passed to `{name}` after its loan ended"),
                                );
                            }
                            Some(Binding {
                                val: Val::Owner { .. },
                                estate,
                            }) if *estate != Some(Estate::Live) => {
                                self.fail(
                                    MEM_CONSUME,
                                    format!("`{v}` is passed to `{name}` after it was consumed"),
                                );
                            }
                            _ => {}
                        }
                    }
                }
                TyKind::Plain => {}
            }
        }
        let ret_kind = sig
            .returns
            .as_ref()
            .map(|ty| classify_type(ty, self.entities))
            .unwrap_or(TyKind::Plain);
        match ret_kind {
            TyKind::Plain => Val::Plain,
            _ => {
                // Provenance: declared `return_from` formals when present
                // (verified), else the union of span-typed actuals.
                let mut prov = BTreeSet::new();
                let mut nodes: Vec<usize> = Vec::new();
                let mut contributors: Vec<Option<String>> = Vec::new();
                if sig.declared_roots.is_empty() {
                    for (actual, val) in args.iter().zip(arg_vals.iter()) {
                        let roots = val.roots(self);
                        if !roots.is_empty() {
                            prov.extend(roots);
                            for node in val.nodes() {
                                if self.nodes.get(node).is_some_and(|n| n.live)
                                    && !nodes.contains(&node)
                                {
                                    nodes.push(node);
                                }
                            }
                            contributors.push(match actual {
                                Expr::Var(v) => Some(v.clone()),
                                _ => None,
                            });
                        }
                    }
                    if prov.is_empty() {
                        prov.insert(Root::Static);
                    }
                } else {
                    for wanted in &sig.declared_roots {
                        if let Some((idx, _)) = sig
                            .params
                            .iter()
                            .enumerate()
                            .find(|(_, (n, _))| n == wanted)
                        {
                            if let Some(val) = arg_vals.get(idx) {
                                prov.extend(val.roots(self));
                                for node in val.nodes() {
                                    if self.nodes.get(node).is_some_and(|n| n.live)
                                        && !nodes.contains(&node)
                                    {
                                        nodes.push(node);
                                    }
                                }
                                contributors.push(match args.get(idx) {
                                    Some(Expr::Var(v)) => Some(v.clone()),
                                    _ => None,
                                });
                            }
                        }
                    }
                }
                let value = match ret_kind {
                    TyKind::Owner { .. } => {
                        let slot = self.fresh_slot(false, None, None);
                        let kind = match &sig.returns {
                            Some(TypeRef::Generic { name, .. }) if name == "Vector" => {
                                OwnKind::Vector
                            }
                            Some(TypeRef::Generic { name, .. }) if name == "Map" => OwnKind::Map,
                            _ => OwnKind::Buffer,
                        };
                        Val::Owner { slot, kind }
                    }
                    TyKind::Borrow | TyKind::Span => {
                        let root = prov
                            .iter()
                            .find_map(|r| match r {
                                Root::Slot(_) => Some(*r),
                                Root::Static => None,
                            })
                            .unwrap_or(Root::Static);
                        // The returned span derives from the contributing
                        // loan of that root: it is that loan's child, so the
                        // contributor stays suspended while the result lives.
                        let parent = nodes
                            .iter()
                            .copied()
                            .find(|n| self.nodes.get(*n).is_some_and(|i| i.live && i.root == root));
                        let writable =
                            matches!(&sig.returns, Some(TypeRef::Named(w)) if w == "MutBytes");
                        let site = self.fresh_site();
                        let node = self.new_loan(
                            root,
                            parent,
                            None,
                            writable,
                            ret_kind == TyKind::Borrow,
                            ctx,
                        );
                        if let Some(info) = self.nodes.get_mut(node) {
                            info.span_site = Some(site);
                        }
                        Val::Loan { node }
                    }
                    _ => Val::Record { prov, nodes },
                };
                // A stored/returned result MOVES contributing exclusive
                // (mutable) loan handles: the result now carries that loan
                // (records hold the node itself, span results are its child)
                // and the old name resolves to an ended loan, so a later use
                // is `MEM201` while `borrow_end` on it stays an idempotent
                // no-op. Read-only views are shared, not moved: records keep
                // their nodes live (record-held views gate owner drops until
                // the record ends) and the view handle stays usable.
                if ctx.stored || ctx.returned {
                    for var in contributors.into_iter().flatten() {
                        let Some(Binding {
                            val: Val::Loan { node },
                            ..
                        }) = self.bindings.get(&var)
                        else {
                            continue;
                        };
                        let node = *node;
                        if !self.nodes.get(node).is_some_and(|n| n.mutable && !n.borrow) {
                            continue;
                        }
                        let carried = match &value {
                            Val::Loan { node: result } => {
                                self.nodes.get(*result).and_then(|n| n.parent) == Some(node)
                            }
                            Val::Alias { nodes, .. } | Val::Record { nodes, .. } => {
                                nodes.contains(&node)
                            }
                            _ => false,
                        };
                        if !carried {
                            continue;
                        }
                        self.resolve_binding(&var);
                        let held_elsewhere = self.retained_nodes().contains(&node);
                        if let Some(info) = self.nodes.get_mut(node) {
                            info.var = None;
                            if matches!(value, Val::Loan { .. }) && !held_elsewhere {
                                // The child result keeps the root pressure
                                // and the ancestor chain; the moved handle's
                                // own node is gone with its name.
                                info.live = false;
                            }
                        }
                    }
                }
                value
            }
        }
    }

    fn consume_owner(&mut self, arg: &Expr, expected: OwnKind, op: &str) {
        let val = self.analyze_expr(
            arg,
            Ctx {
                stored: false,
                returned: false,
            },
        );
        let var = match arg {
            Expr::Var(v) => Some(v.clone()),
            _ => None,
        };
        match (var, val) {
            (Some(v), Val::Owner { slot, kind }) => {
                if self.owner_estate(&v) != Some(Estate::Live) {
                    self.fail(
                        MEM_CONSUME,
                        format!("`{v}` is dropped twice; affine owners drop exactly once"),
                    );
                    return;
                }
                if kind != expected {
                    self.fail(
                        MEM_CONSUME,
                        format!("`{op}` cannot drop `{v}`; owner kind mismatch"),
                    );
                    return;
                }
                if !self.live_pressure_for_slot(slot).is_empty() {
                    self.fail(
                        MEM_LIVE_BORROW,
                        format!(
                            "`{v}` cannot drop while a derived loan is live (including record-held views); end every view first"
                        ),
                    );
                    return;
                }
                if let Some(b) = self.bindings.get_mut(&v) {
                    b.estate = Some(Estate::Dropped);
                }
                self.consts.remove(&v);
            }
            (Some(v), Val::Loan { .. }) => {
                let _ = v;
                self.fail(
                    MEM_CONSUME,
                    format!("`{op}` drops owners, not loans; end loans with borrow_end"),
                );
            }
            (_, Val::Unknown) => {}
            _ => {
                self.fail(
                    MEM_CONSUME,
                    format!("`{op}` expects a live affine owner binding"),
                );
            }
        }
    }

    fn owner_estate(&self, name: &str) -> Option<Estate> {
        self.bindings.get(name).and_then(|b| b.estate)
    }

    fn owner_size(&self, name: &str) -> Option<u64> {
        match self.bindings.get(name) {
            Some(Binding {
                val: Val::Owner { slot, .. },
                estate: Some(Estate::Live),
            }) => self.slots.get(*slot).and_then(|s| s.size),
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Small helpers.
// ---------------------------------------------------------------------------

/// Join one binding's values from two branch ends. Identical loans stay the
/// same loan, records stay records, plain scalars stay plain; anything else
/// becomes an alias carrying the UNION of both paths' roots (including the
/// roots of direct loans) and loan nodes.
fn union_provenance(a: &Val, b: &Val, arena: &[NodeInfo]) -> Val {
    match (a, b) {
        (Val::Owner { .. }, _) => a.clone(),
        (_, Val::Owner { .. }) => a.clone(),
        (Val::Void, _) => b.clone(),
        (_, Val::Void) => a.clone(),
        (Val::Plain, Val::Plain) => Val::Plain,
        (Val::Plain | Val::Unknown, Val::Plain | Val::Unknown) => Val::Unknown,
        (Val::Loan { node: x }, Val::Loan { node: y }) if x == y => a.clone(),
        _ => {
            let mut prov = BTreeSet::new();
            let mut nodes = Vec::new();
            for v in [a, b] {
                match v {
                    Val::Loan { node } => {
                        if let Some(info) = arena.get(*node) {
                            prov.insert(info.root);
                        }
                        nodes.push(*node);
                    }
                    Val::Alias { prov: p, nodes: ns } | Val::Record { prov: p, nodes: ns } => {
                        prov.extend(p.iter().copied());
                        nodes.extend(ns.iter().copied());
                    }
                    _ => {}
                }
            }
            nodes.sort_unstable();
            nodes.dedup();
            if matches!((a, b), (Val::Record { .. }, Val::Record { .. })) {
                Val::Record { prov, nodes }
            } else {
                Val::Alias { prov, nodes }
            }
        }
    }
}

fn binding_live(binding: &Binding, arena: &[NodeInfo]) -> bool {
    match (&binding.val, binding.estate) {
        (Val::Owner { .. }, Some(Estate::Live)) => true,
        (Val::Loan { node }, _) => arena.get(*node).is_some_and(|n| n.live),
        (Val::Alias { nodes, .. }, _) | (Val::Record { nodes, .. }, _) => {
            nodes.iter().any(|n| arena.get(*n).is_some_and(|i| i.live))
        }
        _ => false,
    }
}

fn ranges_overlap(a: (u64, u64), b: (u64, u64)) -> bool {
    let (a_end, b_end) = (a.0.saturating_add(a.1), b.0.saturating_add(b.1));
    a.0 < b_end && b.0 < a_end
}

fn is_owner_root(root: Root) -> bool {
    matches!(root, Root::Slot(_))
}

fn is_mut_loan_call(expr: &Expr) -> bool {
    matches!(expr, Expr::Call { name, .. } if name == "borrow_mut" || name == "slice_mut")
}

fn disjoint_guard(new_var: &str, existing_var: &str) -> Stmt {
    Stmt::ExprStmt(Expr::Call {
        name: "SalMemoryAssertDisjoint".into(),
        args: vec![
            Expr::Call {
                name: "view".into(),
                args: vec![Expr::Var(new_var.into())],
            },
            Expr::Call {
                name: "view".into(),
                args: vec![Expr::Var(existing_var.into())],
            },
        ],
    })
}

fn is_int_cast(name: &str) -> bool {
    matches!(
        name,
        "usize"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "u128"
            | "i128"
    )
}

fn is_numeric_op(name: &str) -> bool {
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

fn is_raw_mem(name: &str) -> bool {
    matches!(
        name,
        "load8"
            | "store8"
            | "load64"
            | "store64"
            | "atomic_load"
            | "atomic_store"
            | "atomic_cas"
            | "syscall"
            | "thread_launch"
            | "operation_address"
            | "concurrency_state"
            | "size_of"
            | "align_of"
            | "offset_of"
    )
}

fn record_or_alias_with_roots(val: &Val) -> bool {
    match val {
        Val::Alias { prov, .. } | Val::Record { prov, .. } => !prov.is_empty(),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Lower affine memory ownership: validate every operation body, preserve
/// all public types, and insert `SalMemoryAssertDisjoint` guards only for
/// genuinely dynamic (non-constant) simultaneous mutable loans of one root.
///
/// Files without any memory surface return cloned. Diagnostics use
/// `MEM201` (stale use after end), `MEM202` (constant overlap),
/// `MEM203` (use after consume / double drop / misuse), `MEM204`
/// (local-rooted escape or undeclared return root), `MEM205` (live-borrow
/// conflict), `MEM206` (forged / cast / C-ABI / channel escape),
/// `MEM207` (constant out-of-bounds), `MEM208` (leaked owner at exit).
pub fn lower(file: &sal_syntax::SalFile) -> Result<sal_syntax::SalFile, Vec<Diagnostic>> {
    if !mentions_memory(file) {
        return Ok(file.clone());
    }
    let entities = entity_table(file);
    let ops = op_table(file);
    let mut out = file.clone();
    let mut diags = Vec::new();
    for item in &mut out.items {
        if let Item::Operation(op) = item {
            // Declared return roots are verified against the actual body in
            // check_return; nothing here trusts the annotation.
            let mut checker = Checker::new(&entities, &ops, op.name.clone(), op.span.clone());
            checker.check_operation(op);
            diags.append(&mut checker.diags);
        }
    }
    if diags.is_empty() {
        Ok(out)
    } else {
        Err(diags)
    }
}
