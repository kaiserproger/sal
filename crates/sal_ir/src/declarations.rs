//! Declarative contracts + typed JSON schemas (full implementation).
//!
//! See the pinned declarative contract for the authoritative surface. This
//! pass runs BEFORE concurrency -> memory -> collections.

use sal_syntax::{
    BinOp, ContractClause, Diagnostic, EntityDecl, Expr, Item, OperationDecl, SalFile, Severity,
    Span, Stmt, TypeRef,
};
use std::collections::{HashMap, HashSet};

const GEN_TOP: &str = "SalDecl";
const MAX_DEPTH: usize = 128;
const KEY_MIN: i64 = 32;
const SKIP_DEPTH: i64 = 64;

fn err(code: &'static str, message: String, span: &Span) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        span: span.clone(),
        suggestion: None,
    }
}

pub fn requires_json_runtime(file: &SalFile) -> bool {
    file.items.iter().any(|item| match item {
        Item::Entity(e) => e.json.enabled,
        Item::Operation(o) => {
            o.generated
                && (o.name.ends_with("DecodeJson")
                    || o.name.ends_with("DecodeJsonAt")
                    || o.name.ends_with("EncodeJson"))
        }
        _ => false,
    })
}

pub fn lower(file: &SalFile) -> Result<SalFile, Vec<Diagnostic>> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    for item in &file.items {
        if let Item::Service(s) = item {
            if !s.requires.is_empty() || !s.ensures.is_empty() {
                diags.push(err(
                    "DEC102",
                    format!(
                        "service `{}` has prose requires/ensures; executable typed contracts are operation-level only",
                        s.name
                    ),
                    &s.span,
                ));
            }
            if s.atomic || !s.allowed_effects.is_empty() || !s.forbidden_effects.is_empty() {
                diags.push(err(
                    "DEC102",
                    format!(
                        "service `{}` declares unimplemented atomic/effects promises",
                        s.name
                    ),
                    &s.span,
                ));
            }
        }
        if let Item::Entity(e) = item {
            if !e.invariants.is_empty() {
                diags.push(err(
                    "DEC102",
                    format!(
                        "entity `{}` has prose invariants; use typed `requires:` clauses",
                        e.name
                    ),
                    &e.span,
                ));
            }
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    if !needs_lower(file) {
        return Ok(file.clone());
    }
    let entities: HashMap<&str, &EntityDecl> = file
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Entity(e) => Some((e.name.as_str(), e)),
            _ => None,
        })
        .collect();
    let operations: HashMap<&str, &OperationDecl> = file
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Operation(o) => Some((o.name.as_str(), o)),
            _ => None,
        })
        .collect();
    for item in &file.items {
        if let Item::Entity(e) = item {
            if e.json.enabled {
                validate_json_entity(e, &entities, &mut diags);
            }
        }
    }
    for item in &file.items {
        if let Item::Operation(o) = item {
            if !o.ownership.lowered {
                validate_ownership(o, &mut diags);
            }
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    let mut lowered_ops: HashMap<String, OperationDecl> = HashMap::new();
    for (name, op) in &operations {
        match lower_operation(op, &entities, &operations) {
            Ok(next) => {
                lowered_ops.insert((*name).to_owned(), next);
            }
            Err(mut more) => diags.append(&mut more),
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    let mut derived: Vec<Item> = Vec::new();
    {
        let mut taken: HashSet<String> = file
            .items
            .iter()
            .filter_map(|i| match i {
                Item::Entity(e) => Some(e.name.clone()),
                Item::Operation(o) => Some(o.name.clone()),
                _ => None,
            })
            .collect();
        let mut order: Vec<&EntityDecl> = entities.values().copied().collect();
        order.sort_by(|a, b| a.name.cmp(&b.name));
        for entity in order {
            if !entity.json.enabled || entity.generated {
                continue;
            }
            let want = [
                format!("{GEN_TOP}{}JsonResult", entity.name),
                format!("{}DecodeJson", entity.name),
                format!("{}DecodeJsonAt", entity.name),
                format!("{}EncodeJson", entity.name),
            ];
            if want.iter().all(|n| taken.contains(n)) {
                continue;
            }
            match derive_json(entity, &entities, &mut taken) {
                Ok(mut items) => derived.append(&mut items),
                Err(mut more) => diags.append(&mut more),
            }
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    let mut out = SalFile::default();
    for item in &file.items {
        match item {
            Item::Operation(o) => {
                if let Some(next) = lowered_ops.get(&o.name) {
                    out.items.push(Item::Operation(next.clone()));
                } else {
                    out.items.push(item.clone());
                }
            }
            _ => out.items.push(item.clone()),
        }
    }
    out.items.extend(derived);
    Ok(out)
}

fn needs_lower(file: &SalFile) -> bool {
    for item in &file.items {
        match item {
            Item::Entity(e) => {
                // `iteration` metadata persists after lowering (do NOT use it
                // as a retrigger: only unlowered `for` loops retrigger, via the
                // body probe below).
                if e.json.enabled && !e.generated {
                    return true;
                }
            }
            Item::Operation(o) => {
                // Generated items are already lowered; never retrigger on them
                // (their bodies legitimately contain `len(` calls).
                if o.generated {
                    continue;
                }
                if !o.requires.is_empty() || !o.ensures.is_empty() {
                    return true;
                }
                if !o.ownership.lowered
                    && (!o.ownership.borrows.is_empty()
                        || !o.ownership.consumes.is_empty()
                        || !o.ownership.return_from.is_empty())
                {
                    return true;
                }
                if stmts_mention_for(&o.body) || stmts_mention_len(&o.body) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn stmts_mention_len(body: &[Stmt]) -> bool {
    let mut stack: Vec<&Stmt> = body.iter().collect();
    let mut n = 0usize;
    while let Some(s) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 32 {
            return false;
        }
        match s {
            Stmt::Let { expr, .. } | Stmt::Assign { expr, .. } | Stmt::Return(expr) => {
                if expr_mentions(expr, "len") {
                    return true;
                }
            }
            Stmt::ExprStmt(e) => {
                if expr_mentions(e, "len") {
                    return true;
                }
            }
            Stmt::If { cond, then, else_ } => {
                if expr_mentions(cond, "len") {
                    return true;
                }
                stack.extend(then.iter());
                stack.extend(else_.iter());
            }
            Stmt::While { cond, body } => {
                if expr_mentions(cond, "len") {
                    return true;
                }
                stack.extend(body.iter());
            }
            Stmt::For { iter, body, .. } => {
                if expr_mentions(iter, "len") {
                    return true;
                }
                stack.extend(body.iter());
            }
            Stmt::Unsafe { body } => stack.extend(body.iter()),
            Stmt::Break | Stmt::Continue => {}
        }
    }
    false
}

fn stmts_mention_for(body: &[Stmt]) -> bool {
    let mut stack: Vec<&Stmt> = body.iter().collect();
    let mut n = 0usize;
    while let Some(s) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 32 {
            return false;
        }
        match s {
            Stmt::For { .. } => return true,
            Stmt::If { then, else_, .. } => {
                stack.extend(then.iter());
                stack.extend(else_.iter());
            }
            Stmt::While { body, .. } | Stmt::Unsafe { body } => stack.extend(body.iter()),
            _ => {}
        }
    }
    false
}

fn expr_mentions(expr: &Expr, name: &str) -> bool {
    let mut stack = vec![expr];
    let mut n = 0usize;
    while let Some(e) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 32 {
            return false;
        }
        match e {
            Expr::Call { name: n, args } => {
                if n == name {
                    return true;
                }
                stack.extend(args.iter());
            }
            Expr::Field { base, .. } | Expr::Not(base) => stack.push(base),
            Expr::Index { base, index } => {
                stack.push(base);
                stack.push(index);
            }
            Expr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
        }
    }
    false
}
// ---------------------------------------------------------------------------
// Ownership header validation.
// ---------------------------------------------------------------------------

fn validate_ownership(op: &OperationDecl, diags: &mut Vec<Diagnostic>) {
    let params: HashSet<&str> = op.accepts.iter().map(|p| p.name.as_str()).collect();
    let mut seen: HashSet<&str> = HashSet::new();
    for name in op
        .ownership
        .borrows
        .iter()
        .chain(op.ownership.consumes.iter())
    {
        if !params.contains(name.as_str()) {
            diags.push(err(
                "DEC201",
                format!(
                    "operation `{}` ownership mode names unknown parameter `{name}`",
                    op.name
                ),
                &op.span,
            ));
        }
        if !seen.insert(name) {
            diags.push(err(
                "DEC201",
                format!(
                    "operation `{}` names parameter `{name}` in more than one ownership mode",
                    op.name
                ),
                &op.span,
            ));
        }
    }
    for name in &op.ownership.return_from {
        if !params.contains(name.as_str()) {
            diags.push(err(
                "DEC202",
                format!(
                    "operation `{}` returns from unknown parameter `{name}`",
                    op.name
                ),
                &op.span,
            ));
        }
    }
    if op.ownership.return_from.len() > 1 {
        // Multiple provenance roots: memory cannot prove disjointness.
        diags.push(err(
            "DEC202",
            format!(
                "operation `{}` returns from multiple owners; declare a single provenance root",
                op.name
            ),
            &op.span,
        ));
    }
}

// ---------------------------------------------------------------------------
// JSON schema validation: types, defaults, acyclic nesting.
// ---------------------------------------------------------------------------

fn schema_scalar(ty: &TypeRef) -> bool {
    matches!(
        ty,
        TypeRef::Named(n) if n == "i64" || n == "u64" || n == "bool" || n == "Text" || n == "TextList"
    )
}

fn validate_json_entity(
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    diags: &mut Vec<Diagnostic>,
) {
    let mut seen: HashSet<&str> = HashSet::new();
    for field in &entity.fields {
        if !seen.insert(field.name.as_str()) {
            diags.push(err(
                "DEC301",
                format!(
                    "entity `{}` declares duplicate field `{}`",
                    entity.name, field.name
                ),
                &field.span,
            ));
        }
        let nested_ok = match &field.ty {
            TypeRef::Named(n)
                if n == "i64" || n == "u64" || n == "bool" || n == "Text" || n == "TextList" =>
            {
                true
            }
            TypeRef::Named(n) => match entities.get(n.as_str()) {
                Some(target) if target.json.enabled => {
                    if target.name == entity.name {
                        diags.push(err(
                            "DEC302",
                            format!(
                                "entity `{}` recursively nests itself via field `{}`",
                                entity.name, field.name
                            ),
                            &field.span,
                        ));
                        false
                    } else {
                        true
                    }
                }
                _ => {
                    diags.push(err(
                        "DEC301",
                        format!(
                            "entity `{}` field `{}` has non-JSON type; schemas allow i64/u64/bool/Text/TextList or nested JSON entities",
                            entity.name, field.name
                        ),
                        &field.span,
                    ));
                    false
                }
            },
            _ => {
                diags.push(err(
                    "DEC301",
                    format!(
                        "entity `{}` field `{}` has non-JSON type; schemas allow i64/u64/bool/Text/TextList or nested JSON entities",
                        entity.name, field.name
                    ),
                    &field.span,
                ));
                false
            }
        };
        let _ = nested_ok;
    }
    // Acyclic nesting across the enabled schema graph, iterative.
    {
        let mut path: Vec<&str> = vec![entity.name.as_str()];
        let mut cursor: Vec<(&EntityDecl, usize)> = vec![(entity, 0)];
        while let Some((current, index)) = cursor.pop() {
            let mut next_index = index;
            let mut pushed = false;
            while next_index < current.fields.len() {
                let field = &current.fields[next_index];
                next_index += 1;
                if let TypeRef::Named(n) = &field.ty {
                    if let Some(target) = entities.get(n.as_str()) {
                        if target.json.enabled {
                            if path.contains(&target.name.as_str()) {
                                diags.push(err(
                                    "DEC302",
                                    format!(
                                        "entity `{}` reaches cyclic JSON nesting via `{}`",
                                        entity.name, target.name
                                    ),
                                    &field.span,
                                ));
                            } else {
                                path.push(target.name.as_str());
                                cursor.push((current, next_index));
                                cursor.push((target, 0));
                                pushed = true;
                                break;
                            }
                        }
                    }
                }
            }
            if !pushed && !path.is_empty() {
                path.pop();
            }
        }
    }
    let fields: HashSet<&str> = entity.fields.iter().map(|f| f.name.as_str()).collect();
    for default in &entity.json.defaults {
        if !fields.contains(default.name.as_str()) {
            diags.push(err(
                "DEC303",
                format!(
                    "entity `{}` defaults unknown field `{}`",
                    entity.name, default.name
                ),
                &entity.span,
            ));
        }
        if let Some(field) = entity.fields.iter().find(|f| f.name == default.name) {
            let want = scalar_hint(&field.ty);
            let got = expr_hint(&default.value, &HashMap::new(), entities);
            if let (Some(w), Some(g)) = (want, got) {
                if w != g {
                    diags.push(err(
                        "DEC303",
                        format!(
                            "entity `{}` default for `{}` expects {}, got {}",
                            entity.name, default.name, w, g
                        ),
                        &entity.span,
                    ));
                }
            }
        }
    }
    for clause in &entity.json.requires {
        check_condition_types(
            &clause.condition,
            entity,
            entities,
            "bool",
            &entity.span,
            diags,
        );
        if let Some(otherwise) = &clause.otherwise {
            check_condition_types(otherwise, entity, entities, "i64", &entity.span, diags);
            let status = const_i64(otherwise);
            match status {
                Some(v) if v == -22 || v == -28 => {}
                _ => diags.push(err(
                    "DEC304",
                    format!(
                        "entity `{}` schema otherwise must yield status -22 or -28",
                        entity.name
                    ),
                    &entity.span,
                )),
            }
        }
    }
}

/// Scalar type hint for default checking.
fn scalar_hint(ty: &TypeRef) -> Option<&'static str> {
    match ty {
        TypeRef::Named(n) => match n.as_str() {
            "i64" => Some("i64"),
            "u64" => Some("u64"),
            "bool" => Some("bool"),
            "Text" => Some("Text"),
            "TextList" => Some("TextList"),
            _ => None,
        },
        _ => None,
    }
}
// ---------------------------------------------------------------------------
// Local type inference: params, lets, calls, fields. Enough to resolve
// declared iterables and len(TextList); not a second full body checker.
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
enum LocalTy {
    Named(String),
    Generic { name: String, args: Vec<LocalTy> },
    Unknown,
}

impl LocalTy {
    fn from_ref(ty: &TypeRef) -> Self {
        match ty {
            TypeRef::Named(n) => LocalTy::Named(n.clone()),
            TypeRef::Generic { name, args } => LocalTy::Generic {
                name: name.clone(),
                args: args.iter().map(LocalTy::from_ref).collect(),
            },
        }
    }
    fn is_text_list(&self) -> bool {
        matches!(self, LocalTy::Named(n) if n == "TextList")
    }
}

fn expr_hint(
    expr: &Expr,
    env: &HashMap<String, LocalTy>,
    entities: &HashMap<&str, &EntityDecl>,
) -> Option<&'static str> {
    match expr {
        Expr::Bool(_) => Some("bool"),
        Expr::Int(_) => Some("i64"),
        Expr::Lit(_) => Some("Text"),
        Expr::Var(v) => match env.get(v) {
            Some(LocalTy::Named(n)) => match n.as_str() {
                "i64" => Some("i64"),
                "u64" => Some("u64"),
                "bool" => Some("bool"),
                "Text" => Some("Text"),
                "TextList" => Some("TextList"),
                "usize" => Some("usize"),
                _ => None,
            },
            _ => None,
        },
        Expr::Call { name, .. } => match name.as_str() {
            "TextListLen" => Some("usize"),
            "len" => Some("usize"),
            "TextListEachNonEmpty" | "TextListEachAtMost" | "TextListNoNul" | "TextListUnique" => {
                Some("bool")
            }
            "usize" => Some("usize"),
            _ => None,
        },
        Expr::Field { base, field } => {
            let LocalTy::Named(entity) = infer_expr(base, env, entities) else {
                return None;
            };
            let decl = entities.get(entity.as_str())?;
            let f = decl.fields.iter().find(|f| &f.name == field)?;
            scalar_hint(&f.ty)
        }
        Expr::BinOp { op, .. } => match op {
            BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::Eq
            | BinOp::Ne
            | BinOp::And
            | BinOp::Or => Some("bool"),
            _ => None,
        },
        Expr::Not(_) => Some("bool"),
        Expr::Index { .. } | Expr::Float(_) => None,
    }
}

fn infer_expr(
    expr: &Expr,
    env: &HashMap<String, LocalTy>,
    entities: &HashMap<&str, &EntityDecl>,
) -> LocalTy {
    match expr {
        Expr::Var(v) => env.get(v).cloned().unwrap_or(LocalTy::Unknown),
        Expr::Lit(_) => LocalTy::Named("Text".into()),
        Expr::Int(_) => LocalTy::Named("i64".into()),
        Expr::Bool(_) => LocalTy::Named("bool".into()),
        Expr::Float(_) => LocalTy::Named("f64".into()),
        Expr::Not(_) => LocalTy::Named("bool".into()),
        Expr::BinOp { op, left, right } => {
            let l = infer_expr(left, env, entities);
            let r = infer_expr(right, env, entities);
            match op {
                BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::And
                | BinOp::Or => LocalTy::Named("bool".into()),
                _ => {
                    if l == r {
                        l
                    } else {
                        LocalTy::Unknown
                    }
                }
            }
        }
        Expr::Field { base, field } => {
            let LocalTy::Named(entity) = infer_expr(base, env, entities) else {
                return LocalTy::Unknown;
            };
            let Some(decl) = entities.get(entity.as_str()) else {
                return LocalTy::Unknown;
            };
            decl.fields
                .iter()
                .find(|f| &f.name == field)
                .map(|f| LocalTy::from_ref(&f.ty))
                .unwrap_or(LocalTy::Unknown)
        }
        Expr::Index { .. } => LocalTy::Unknown,
        Expr::Call { name, .. } => {
            if name == "len" {
                return LocalTy::Named("usize".into());
            }
            if name == "TextListLen" {
                return LocalTy::Named("usize".into());
            }
            if matches!(
                name.as_str(),
                "TextListEachNonEmpty" | "TextListEachAtMost" | "TextListNoNul" | "TextListUnique"
            ) {
                return LocalTy::Named("bool".into());
            }
            // Entity construction yields the entity type; operation calls
            // yield their declared return when known.
            LocalTy::Unknown
        }
    }
}

fn check_condition_types(
    expr: &Expr,
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    want: &str,
    span: &Span,
    diags: &mut Vec<Diagnostic>,
) {
    let mut env: HashMap<String, LocalTy> = HashMap::new();
    for f in &entity.fields {
        env.insert(f.name.clone(), LocalTy::from_ref(&f.ty));
    }
    if expr_hint(expr, &env, entities).is_some_and(|got| got != want) {
        diags.push(err(
            "DEC305",
            format!(
                "entity `{}` contract expects {}, type inference disagrees",
                entity.name, want
            ),
            span,
        ));
    }
    // Walk names: unknown identifiers fail closed.
    let mut stack = vec![expr];
    let mut n = 0usize;
    while let Some(e) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 64 {
            return;
        }
        match e {
            Expr::Var(v) => {
                if !env.contains_key(v) {
                    diags.push(err(
                        "DEC305",
                        format!(
                            "entity `{}` contract names unknown field `{v}`",
                            entity.name
                        ),
                        span,
                    ));
                }
            }
            Expr::Call { args, .. } => stack.extend(args.iter()),
            Expr::Field { base, .. } => stack.push(base),
            Expr::Index { base, index } => {
                stack.push(base);
                stack.push(index);
            }
            Expr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Expr::Not(inner) => stack.push(inner),
            _ => {}
        }
    }
}

fn const_i64(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Int(v) => Some(*v),
        _ => None,
    }
}
// ---------------------------------------------------------------------------
// Contract purity: real callee-graph inspection.
// ---------------------------------------------------------------------------

/// Intrinsics that observably mutate borrowed state even though they are
/// capability-Pure (no `intrinsic_effects` entry). Read-only `len`/`byte` /
/// `slice`/`view`/`text`-validators / `TextList*` predicates are fine, and so
/// is `borrow_end`: ending a read view is loan bookkeeping, not a write
/// (every actual write still surfaces as `put`/raw memory/a listed writer).
fn is_mutating_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "put"
            | "slice_mut"
            | "borrow_mut"
            | "borrow"
            | "buffer"
            | "buffer_drop"
            | "vector"
            | "vector_drop"
            | "vector_reserve"
            | "vector_push"
            | "vector_set"
            | "vector_pop"
            | "map"
            | "map_drop"
            | "map_reserve"
            | "map_insert"
            | "map_remove"
            | "syscall"
            | "thread_launch"
            | "address"
            | "bytes_at"
            | "load8"
            | "store8"
            | "atomic_load"
            | "atomic_store"
            | "atomic_cas"
            | "load64"
            | "store64"
            | "concurrency_state"
            | "operation_address"
            | "BytesCopy"
            | "BytesDecimal"
            | "BytesDecimalPadded"
            | "JsonEmitScalar"
            | "JsonDecodeString"
            | "LinuxWriteAll"
            | "LinuxReadInto"
            | "LinuxReadExact"
    )
}

fn is_readonly_call(name: &str) -> bool {
    matches!(
        name,
        "len"
            | "byte"
            | "slice"
            | "view"
            | "borrow_end"
            | "text"
            | "bytes"
            | "usize"
            | "i64"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "i8"
            | "i16"
            | "i32"
            | "isize"
            | "TextValidate"
            | "TextIsBoundary"
            | "TextEnd"
            | "TextListLen"
            | "TextListEachNonEmpty"
            | "TextListEachAtMost"
            | "TextListNoNul"
            | "TextListUnique"
            | "JsonWhitespaceEnd"
            | "JsonValueEnd"
            | "SalContractAssert"
            | "SalMemoryAssertDisjoint"
    ) || name.starts_with("TextList") && {
        // TextList* semantic helpers are read-only by contract; any other
        // TextList-prefixed operation must be proven, not assumed.
        matches!(
            name,
            "TextListLen"
                | "TextListEachNonEmpty"
                | "TextListEachAtMost"
                | "TextListNoNul"
                | "TextListUnique"
                | "TextListNext"
        )
    }
}

/// Callee universe for contract purity: operations are walked, record
/// constructors only build values and are pure by construction.
struct Callees<'a> {
    operations: &'a HashMap<&'a str, &'a OperationDecl>,
    entities: &'a HashMap<&'a str, &'a EntityDecl>,
}

/// Fail-closed purity: walks the actual callee graph for observable
/// mutation. `Pure` declarations alone do NOT imply read-only (capability
/// Pure covers borrowed-arg mutation). `let mut`/`set` locals are fine.
fn contract_call_pure(
    name: &str,
    operations: &Callees,
    visiting: &mut Vec<String>,
    depth: usize,
) -> bool {
    if is_mutating_intrinsic(name) {
        return false;
    }
    if is_readonly_call(name) {
        return true;
    }
    if name == "SalContractAssert"
        || name == "SalMemoryAssertDisjoint"
        || operations.entities.contains_key(name)
    {
        return true;
    }
    let Some(callee) = operations.operations.get(name) else {
        // Unknown callee: numeric/builtin casts are pure, external C entry
        // points and unresolved names fail closed.
        return matches!(
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
        );
    };
    if visiting.contains(&name.to_owned()) {
        return false;
    }
    if depth > MAX_DEPTH {
        return false;
    }
    // Raw boundaries fail even under `unsafe:` wrapping inside the callee.
    visiting.push(name.to_owned());
    let mut pure = true;
    let mut stack: Vec<&Stmt> = callee.body.iter().collect();
    let mut n = 0usize;
    while let Some(stmt) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 64 {
            pure = false;
            break;
        }
        match stmt {
            Stmt::Let { expr, .. } | Stmt::Assign { expr, .. } | Stmt::Return(expr) => {
                if !expr_pure(expr, operations, visiting, depth + 1) {
                    pure = false;
                    break;
                }
            }
            Stmt::ExprStmt(e) => {
                if !expr_pure(e, operations, visiting, depth + 1) {
                    pure = false;
                    break;
                }
            }
            Stmt::If { cond, then, else_ } => {
                if !expr_pure(cond, operations, visiting, depth + 1) {
                    pure = false;
                    break;
                }
                stack.extend(then.iter());
                stack.extend(else_.iter());
            }
            Stmt::While { cond, body } => {
                if !expr_pure(cond, operations, visiting, depth + 1) {
                    pure = false;
                    break;
                }
                stack.extend(body.iter());
            }
            Stmt::For { iter, body, .. } => {
                if !expr_pure(iter, operations, visiting, depth + 1) {
                    pure = false;
                    break;
                }
                stack.extend(body.iter());
            }
            Stmt::Unsafe { .. } => {
                // Raw unsafe blocks inside a contract callee are observable
                // mutation boundaries; contracts reject them outright.
                pure = false;
                break;
            }
            Stmt::Break | Stmt::Continue => {}
        }
    }
    visiting.pop();
    pure
}

fn expr_pure(expr: &Expr, operations: &Callees, visiting: &mut Vec<String>, depth: usize) -> bool {
    let mut stack = vec![expr];
    let mut n = 0usize;
    while let Some(e) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 64 {
            return false;
        }
        match e {
            Expr::Call { name, args } => {
                if !contract_call_pure(name, operations, visiting, depth) {
                    return false;
                }
                stack.extend(args.iter());
            }
            Expr::Field { base, .. } => stack.push(base),
            Expr::Index { base, index } => {
                stack.push(base);
                stack.push(index);
            }
            Expr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Expr::Not(inner) => stack.push(inner),
            Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
        }
    }
    true
}

fn check_contract_purity(
    expr: &Expr,
    op: &OperationDecl,
    operations: &Callees,
    diags: &mut Vec<Diagnostic>,
) {
    if !expr_pure(expr, operations, &mut Vec::new(), 0) {
        diags.push(err(
            "DEC203",
            format!(
                "operation `{}` contract calls an effectful callee; contracts must be Pure and read-only",
                op.name
            ),
            &op.span,
        ));
    }
}
// ---------------------------------------------------------------------------
// Per-operation lowering: contracts, ownership erasure, loops, len().
// ---------------------------------------------------------------------------

fn lower_operation(
    op: &OperationDecl,
    entities: &HashMap<&str, &EntityDecl>,
    operations: &HashMap<&str, &OperationDecl>,
) -> Result<OperationDecl, Vec<Diagnostic>> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    let callees = Callees {
        operations,
        entities,
    };
    let mut next = op.clone();
    if next.ownership.lowered {
        return Ok(next);
    }
    let param_names: HashSet<&str> = op.accepts.iter().map(|p| p.name.as_str()).collect();
    // Ownership header consistency against declared parameters.
    {
        let mut seen: HashSet<&str> = HashSet::new();
        for name in next
            .ownership
            .borrows
            .iter()
            .chain(next.ownership.consumes.iter())
        {
            if !param_names.contains(name.as_str()) {
                diags.push(err(
                    "DEC201",
                    format!(
                        "operation `{}` ownership mode names unknown parameter `{name}`",
                        op.name
                    ),
                    &op.span,
                ));
            }
            if !seen.insert(name) {
                diags.push(err(
                    "DEC201",
                    format!(
                        "operation `{}` names parameter `{name}` in more than one ownership mode",
                        op.name
                    ),
                    &op.span,
                ));
            }
        }
        for name in &next.ownership.return_from {
            if !param_names.contains(name.as_str()) {
                diags.push(err(
                    "DEC202",
                    format!(
                        "operation `{}` returns from unknown parameter `{name}`",
                        op.name
                    ),
                    &op.span,
                ));
            }
        }
        if next.ownership.return_from.len() > 1 {
            diags.push(err(
                "DEC202",
                format!(
                    "operation `{}` returns from multiple owners; declare a single provenance root",
                    op.name
                ),
                &op.span,
            ));
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    let borrowed: HashSet<String> = next.ownership.borrows.iter().cloned().collect();
    // Rewrite header Borrow<T> params to their owned inner type: `borrows
    // owner` transforms the owned parameter to `Borrow<T>`, so callsites
    // borrow the ORIGINAL owner slot (no by-value metadata copy). The
    // declaration pass records the erasure; the memory pass lowers the call.
    for param in &mut next.accepts {
        if borrowed.contains(&param.name) {
            match &param.ty {
                TypeRef::Generic { name, args } if name == "Borrow" && args.len() == 1 => {}
                _ => {
                    let inner = param.ty.clone();
                    param.ty = TypeRef::Generic {
                        name: "Borrow".into(),
                        args: vec![inner],
                    };
                }
            }
        }
    }
    // Auto-borrow owner callsites: for each call argument position that
    // takes Borrow<T>, wrap the ORIGINAL bound owner slot (parameter or
    // local) so no metadata copy escapes. Names that already hold a borrow
    // (Borrow parameters, `let x = borrow(..)`) are passed through as-is.
    {
        let mut borrowed: HashSet<String> = next
            .accepts
            .iter()
            .filter(|p| matches!(&p.ty, TypeRef::Generic { name, .. } if name == "Borrow"))
            .map(|p| p.name.clone())
            .collect();
        collect_borrow_locals(&next.body, &mut borrowed, 0);
        let mut wrap: HashMap<String, Vec<usize>> = HashMap::new();
        for (callee_name, callee) in operations.iter() {
            if *callee_name == op.name {
                continue;
            }
            for (index, param) in callee.accepts.iter().enumerate() {
                let declared_borrow = callee.ownership.borrows.contains(&param.name);
                if declared_borrow
                    || matches!(&param.ty, TypeRef::Generic { name, args } if name == "Borrow" && args.len() == 1)
                {
                    wrap.entry(callee_name.to_string()).or_default().push(index);
                }
            }
        }
        if !wrap.is_empty() {
            let mut stmts = std::mem::take(&mut next.body);
            auto_borrow_calls(&mut stmts, &wrap, &borrowed, 0);
            next.body = stmts;
        }
    }
    // Contract checking: typecheck conditions, error values, declared names
    // and parameter modes; reject effectful calls via the real callee graph.
    let mut env: HashMap<String, LocalTy> = HashMap::new();
    for p in &next.accepts {
        env.insert(p.name.clone(), LocalTy::from_ref(&p.ty));
    }
    for clause in &op.requires {
        check_contract_purity(&clause.condition, op, &callees, &mut diags);
        if let Some(otherwise) = &clause.otherwise {
            check_contract_purity(otherwise, op, &callees, &mut diags);
            check_names_bound(otherwise, &env, op, &mut diags);
            check_names_bound(&clause.condition, &env, op, &mut diags);
            // Error-value type must match the operation return type.
            if let Some(ret) = &op.returns {
                let want = LocalTy::from_ref(ret);
                let got = infer_expr(otherwise, &env, entities);
                if got != LocalTy::Unknown && got != want {
                    diags.push(err(
                        "DEC204",
                        format!(
                            "operation `{}` requires otherwise value mismatches return type",
                            op.name
                        ),
                        &op.span,
                    ));
                }
            } else {
                diags.push(err(
                    "DEC204",
                    format!(
                        "operation `{}` requires otherwise value but declares no return type",
                        op.name
                    ),
                    &op.span,
                ));
            }
        } else {
            check_names_bound(&clause.condition, &env, op, &mut diags);
        }
        let hint = expr_hint(&clause.condition, &env, entities);
        if hint.is_some_and(|h| h != "bool") {
            diags.push(err(
                "DEC204",
                format!("operation `{}` requires condition must be bool", op.name),
                &op.span,
            ));
        }
    }
    for post in &op.ensures {
        check_contract_purity(post, op, &callees, &mut diags);
        let mut post_env = env.clone();
        if let Some(ret) = &op.returns {
            // `result` names the actual returned value in the HEADER
            // environment only; body locals named `result` stay valid.
            post_env.insert("result".into(), LocalTy::from_ref(ret));
        }
        check_names_bound_env(post, &post_env, op, &mut diags);
        let hint = expr_hint(post, &post_env, entities);
        if hint.is_some_and(|h| h != "bool") {
            diags.push(err(
                "DEC204",
                format!("operation `{}` ensures condition must be bool", op.name),
                &op.span,
            ));
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    // Lower contract guards into the body: preconditions evaluate once in
    // declaration order (otherwise = typed early return, else trap);
    // postconditions evaluate after the return expression exactly once via a
    // scope-aware return rewrite (no double evaluation of the value).
    let prefix = lower_requires(&op.requires, op, &mut env);
    let mut body = lower_for_loops(&next.body, entities, &env, op, &mut diags);
    body = rewrite_len_textlist(&body, &env);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    if next.body.is_empty() && (!op.requires.is_empty() || !op.ensures.is_empty()) {
        diags.push(err(
            "DEC204",
            format!(
                "operation `{}` declares contracts on a bodyless specification; executable contracts require a body",
                op.name
            ),
            &op.span,
        ));
        return Err(diags);
    }
    let mut combined = prefix;
    combined.extend(body);
    next.body = combined;
    if op.returns.is_some() && !op.ensures.is_empty() {
        let taken: HashSet<String> = bound_names(&next.body);
        let ret_tmp = fresh_local(&taken, &["result"], "SalDeclResult");
        next.body = rewrite_returns(next.body, op, &ret_tmp);
    } else if op.returns.is_none() && !op.ensures.is_empty() {
        diags.push(err(
            "DEC204",
            format!(
                "operation `{}` declares ensures without a return type",
                op.name
            ),
            &op.span,
        ));
        return Err(diags);
    }
    next.requires.clear();
    next.ensures.clear();
    next.ownership.lowered = true;
    Ok(next)
}

fn check_names_bound(
    expr: &Expr,
    env: &HashMap<String, LocalTy>,
    op: &OperationDecl,
    diags: &mut Vec<Diagnostic>,
) {
    check_names_bound_env(expr, env, op, diags);
}

fn check_names_bound_env(
    expr: &Expr,
    env: &HashMap<String, LocalTy>,
    op: &OperationDecl,
    diags: &mut Vec<Diagnostic>,
) {
    let mut stack = vec![expr];
    let mut n = 0usize;
    while let Some(e) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 64 {
            return;
        }
        match e {
            Expr::Var(v) => {
                if !env.contains_key(v) && v != "result" && v != "true" && v != "false" {
                    diags.push(err(
                        "DEC205",
                        format!(
                            "operation `{}` contract names unknown binding `{v}`",
                            op.name
                        ),
                        &op.span,
                    ));
                }
            }
            Expr::Call { name, args } => {
                // `result` is reserved for postconditions; calls named
                // `result` are rejected to protect the header binding.
                if name == "result" {
                    diags.push(err(
                        "DEC205",
                        format!(
                            "operation `{}` contract calls reserved name `result`",
                            op.name
                        ),
                        &op.span,
                    ));
                }
                stack.extend(args.iter());
            }
            Expr::Field { base, .. } => stack.push(base),
            Expr::Index { base, index } => {
                stack.push(base);
                stack.push(index);
            }
            Expr::BinOp { left, right, .. } => {
                stack.push(left);
                stack.push(right);
            }
            Expr::Not(inner) => stack.push(inner),
            _ => {}
        }
    }
}

/// Names bound directly to a `borrow(..)` expression anywhere in `stmts`.
fn collect_borrow_locals(stmts: &[Stmt], borrowed: &mut HashSet<String>, depth: usize) {
    if depth > MAX_DEPTH {
        return;
    }
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                name,
                expr: Expr::Call { name: callee, .. },
                ..
            } if callee == "borrow" => {
                borrowed.insert(name.clone());
            }
            Stmt::If { then, else_, .. } => {
                collect_borrow_locals(then, borrowed, depth + 1);
                collect_borrow_locals(else_, borrowed, depth + 1);
            }
            Stmt::While { body, .. } | Stmt::For { body, .. } | Stmt::Unsafe { body } => {
                collect_borrow_locals(body, borrowed, depth + 1);
            }
            _ => {}
        }
    }
}

fn auto_borrow_calls(
    stmts: &mut [Stmt],
    wrap: &HashMap<String, Vec<usize>>,
    borrowed: &HashSet<String>,
    depth: usize,
) {
    if depth > MAX_DEPTH {
        return;
    }
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::Let { expr, .. } | Stmt::Assign { expr, .. } | Stmt::Return(expr) => {
                auto_borrow_expr(expr, wrap, borrowed, depth + 1);
            }
            Stmt::ExprStmt(e) => auto_borrow_expr(e, wrap, borrowed, depth + 1),
            Stmt::If { cond, then, else_ } => {
                auto_borrow_expr(cond, wrap, borrowed, depth + 1);
                auto_borrow_calls(then, wrap, borrowed, depth + 1);
                auto_borrow_calls(else_, wrap, borrowed, depth + 1);
            }
            Stmt::While { cond, body } => {
                auto_borrow_expr(cond, wrap, borrowed, depth + 1);
                auto_borrow_calls(body, wrap, borrowed, depth + 1);
            }
            Stmt::For { iter, body, .. } => {
                auto_borrow_expr(iter, wrap, borrowed, depth + 1);
                auto_borrow_calls(body, wrap, borrowed, depth + 1);
            }
            Stmt::Unsafe { body } => auto_borrow_calls(body, wrap, borrowed, depth + 1),
            Stmt::Break | Stmt::Continue => {}
        }
    }
}

fn auto_borrow_expr(
    expr: &mut Expr,
    wrap: &HashMap<String, Vec<usize>>,
    borrowed: &HashSet<String>,
    depth: usize,
) {
    if depth > MAX_DEPTH {
        return;
    }
    match expr {
        Expr::Call { name, args } => {
            for arg in args.iter_mut() {
                auto_borrow_expr(arg, wrap, borrowed, depth + 1);
            }
            if let Some(indices) = wrap.get(name) {
                for &index in indices {
                    if let Some(arg) = args.get_mut(index) {
                        if matches!(arg, Expr::Var(v) if !borrowed.contains(v.as_str())) {
                            let slot = std::mem::replace(arg, Expr::Bool(false));
                            *arg = Expr::Call {
                                name: "borrow".into(),
                                args: vec![slot],
                            };
                        }
                    }
                }
            }
        }
        Expr::Field { base, .. } => auto_borrow_expr(base, wrap, borrowed, depth + 1),
        Expr::Index { base, index } => {
            auto_borrow_expr(base, wrap, borrowed, depth + 1);
            auto_borrow_expr(index, wrap, borrowed, depth + 1);
        }
        Expr::BinOp { left, right, .. } => {
            auto_borrow_expr(left, wrap, borrowed, depth + 1);
            auto_borrow_expr(right, wrap, borrowed, depth + 1);
        }
        Expr::Not(inner) => auto_borrow_expr(inner, wrap, borrowed, depth + 1),
        _ => {}
    }
}

/// Preconditions evaluate once, in declaration order: `otherwise` is the
/// actual typed early-return value; without it the contract traps via the
/// pure compiler intrinsic `SalContractAssert(bool) -> Void`.
fn lower_requires(
    clauses: &[ContractClause],
    op: &OperationDecl,
    env: &mut HashMap<String, LocalTy>,
) -> Vec<Stmt> {
    let mut out = Vec::new();
    for clause in clauses {
        if let Some(otherwise) = &clause.otherwise {
            out.push(Stmt::If {
                cond: Expr::Not(Box::new(clause.condition.clone())),
                then: vec![Stmt::Return(otherwise.clone())],
                else_: Vec::new(),
            });
        } else {
            out.push(Stmt::ExprStmt(Expr::Call {
                name: "SalContractAssert".into(),
                args: vec![clause.condition.clone()],
            }));
        }
    }
    let _ = (op, env);
    out
}
// ---------------------------------------------------------------------------
// Local-name utilities, ensures rewrite, for-loop lowering, len() rewrite.
// ---------------------------------------------------------------------------

fn bound_names(body: &[Stmt]) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut stack: Vec<&Stmt> = body.iter().collect();
    let mut n = 0usize;
    while let Some(s) = stack.pop() {
        n += 1;
        if n > MAX_DEPTH * 128 {
            break;
        }
        match s {
            Stmt::Let { name, .. } => {
                names.insert(name.clone());
            }
            Stmt::For { var, body, .. } => {
                names.insert(var.clone());
                stack.extend(body.iter());
            }
            Stmt::If { then, else_, .. } => {
                stack.extend(then.iter());
                stack.extend(else_.iter());
            }
            Stmt::While { body, .. } | Stmt::Unsafe { body } => stack.extend(body.iter()),
            _ => {}
        }
    }
    names
}

fn fresh_local(taken: &HashSet<String>, avoid: &[&str], stem: &str) -> String {
    let mut candidate = format!("{GEN_TOP}{stem}");
    let mut seq = 0usize;
    while taken.contains(&candidate) || avoid.contains(&candidate.as_str()) {
        candidate = format!("{GEN_TOP}{stem}{seq}");
        seq += 1;
    }
    candidate
}

/// Postconditions evaluate after the return expression exactly once: every
/// `return VALUE` becomes `let TMP = VALUE; <asserts>; return TMP`.
/// Scope-aware (incl. inside unsafe/loops); `result` inside asserts maps to
/// the actual once-evaluated return binding, never a body collision.
fn rewrite_returns(body: Vec<Stmt>, op: &OperationDecl, tmp: &str) -> Vec<Stmt> {
    fn go(stmts: Vec<Stmt>, op: &OperationDecl, tmp: &str, depth: usize) -> Vec<Stmt> {
        if depth > MAX_DEPTH {
            return stmts;
        }
        let mut out = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            match stmt {
                Stmt::Return(value) => {
                    out.push(Stmt::Let {
                        name: tmp.to_owned(),
                        mutable: false,
                        expr: value,
                    });
                    for post in &op.ensures {
                        let cond = substitute_result(post, tmp);
                        out.push(Stmt::ExprStmt(Expr::Call {
                            name: "SalContractAssert".into(),
                            args: vec![cond],
                        }));
                    }
                    out.push(Stmt::Return(Expr::Var(tmp.to_owned())));
                }
                Stmt::If { cond, then, else_ } => out.push(Stmt::If {
                    cond,
                    then: go(then, op, tmp, depth + 1),
                    else_: go(else_, op, tmp, depth + 1),
                }),
                Stmt::While { cond, body } => out.push(Stmt::While {
                    cond,
                    body: go(body, op, tmp, depth + 1),
                }),
                Stmt::For { var, iter, body } => out.push(Stmt::For {
                    var,
                    iter,
                    body: go(body, op, tmp, depth + 1),
                }),
                Stmt::Unsafe { body } => out.push(Stmt::Unsafe {
                    body: go(body, op, tmp, depth + 1),
                }),
                other => out.push(other),
            }
        }
        out
    }
    go(body, op, tmp, 0)
}

fn substitute_result(expr: &Expr, tmp: &str) -> Expr {
    match expr {
        Expr::Var(v) if v == "result" => Expr::Var(tmp.to_owned()),
        Expr::Call { name, args } => Expr::Call {
            name: name.clone(),
            args: args.iter().map(|a| substitute_result(a, tmp)).collect(),
        },
        Expr::Field { base, field } => Expr::Field {
            base: Box::new(substitute_result(base, tmp)),
            field: field.clone(),
        },
        Expr::Index { base, index } => Expr::Index {
            base: Box::new(substitute_result(base, tmp)),
            index: Box::new(substitute_result(index, tmp)),
        },
        Expr::BinOp { op, left, right } => Expr::BinOp {
            op: *op,
            left: Box::new(substitute_result(left, tmp)),
            right: Box::new(substitute_result(right, tmp)),
        },
        Expr::Not(inner) => Expr::Not(Box::new(substitute_result(inner, tmp))),
        other => other.clone(),
    }
}

/// Lower `for x in ITER` over an entity declaring `iterates T using Next`
/// to a once-evaluated cursor loop using the `Next` result record
/// `{valid, has, value, next}`. `valid` is checked via SalContractAssert.
/// The iterator advances BEFORE the user body so `continue` cannot repeat
/// an item. Break/continue/scopes and borrowed provenance are preserved.
fn lower_for_loops(
    body: &[Stmt],
    entities: &HashMap<&str, &EntityDecl>,
    env: &HashMap<String, LocalTy>,
    op: &OperationDecl,
    diags: &mut Vec<Diagnostic>,
) -> Vec<Stmt> {
    let mut out = Vec::with_capacity(body.len());
    for stmt in body {
        match stmt {
            Stmt::For {
                var,
                iter,
                body: inner,
            } => {
                match resolve_iteration(iter, env, entities) {
                    Some(resolved) => {
                        out.extend(expand_for(var, iter, inner, &resolved, entities, op, diags));
                    }
                    None => {
                        // Not a declared-iterable target: leave the loop for
                        // the normal body checker (Vec iteration).
                        out.push(Stmt::For {
                            var: var.clone(),
                            iter: iter.clone(),
                            body: lower_for_loops(inner, entities, env, op, diags),
                        });
                    }
                }
            }
            Stmt::If { cond, then, else_ } => out.push(Stmt::If {
                cond: cond.clone(),
                then: lower_for_loops(then, entities, env, op, diags),
                else_: lower_for_loops(else_, entities, env, op, diags),
            }),
            Stmt::While { cond, body: inner } => out.push(Stmt::While {
                cond: cond.clone(),
                body: lower_for_loops(inner, entities, env, op, diags),
            }),
            Stmt::Unsafe { body: inner } => out.push(Stmt::Unsafe {
                body: lower_for_loops(inner, entities, env, op, diags),
            }),
            other => out.push(other.clone()),
        }
    }
    out
}

struct ResolvedIter {
    next_op: String,
    item_ty: LocalTy,
}

fn resolve_iteration(
    iter: &Expr,
    env: &HashMap<String, LocalTy>,
    entities: &HashMap<&str, &EntityDecl>,
) -> Option<ResolvedIter> {
    let ty = infer_expr(iter, env, entities);
    let LocalTy::Named(name) = &ty else {
        return None;
    };
    let decl = entities.get(name.as_str())?;
    let iteration = decl.iteration.as_ref()?;
    Some(ResolvedIter {
        next_op: iteration.next.clone(),
        item_ty: LocalTy::from_ref(&iteration.item),
    })
}

fn expand_for(
    var: &str,
    iter: &Expr,
    body: &[Stmt],
    resolved: &ResolvedIter,
    entities: &HashMap<&str, &EntityDecl>,
    op: &OperationDecl,
    diags: &mut Vec<Diagnostic>,
) -> Vec<Stmt> {
    let taken = bound_names(body);
    let mut taken_all = taken.clone();
    for p in &op.accepts {
        taken_all.insert(p.name.clone());
    }
    taken_all.insert(var.to_owned());
    let cursor = fresh_local(&taken_all, &[], "Cursor");
    taken_all.insert(cursor.clone());
    let step = fresh_local(&taken_all, &[], "Step");
    taken_all.insert(step.clone());
    let advance = |stmts: Vec<Stmt>| -> Vec<Stmt> {
        // Advance BEFORE the user body: valid check, has check, bind value,
        // advance cursor, then user body. Continue-safe by construction.
        vec![
            Stmt::Let {
                name: step.clone(),
                mutable: false,
                expr: Expr::Call {
                    name: resolved.next_op.clone(),
                    args: vec![Expr::Var(cursor.clone())],
                },
            },
            Stmt::ExprStmt(Expr::Call {
                name: "SalContractAssert".into(),
                args: vec![Expr::Field {
                    base: Box::new(Expr::Var(step.clone())),
                    field: "valid".into(),
                }],
            }),
            Stmt::If {
                cond: Expr::Not(Box::new(Expr::Field {
                    base: Box::new(Expr::Var(step.clone())),
                    field: "has".into(),
                })),
                then: vec![Stmt::Break],
                else_: Vec::new(),
            },
            Stmt::Let {
                name: var.to_owned(),
                mutable: false,
                expr: Expr::Field {
                    base: Box::new(Expr::Var(step.clone())),
                    field: "value".into(),
                },
            },
            Stmt::Assign {
                name: cursor.clone(),
                expr: Expr::Field {
                    base: Box::new(Expr::Var(step.clone())),
                    field: "next".into(),
                },
            },
        ]
        .into_iter()
        .chain(stmts)
        .collect()
    };
    let _ = &resolved.item_ty;
    let _ = entities;
    let lowered_inner = lower_for_loops(body, entities, &HashMap::new(), op, diags);
    vec![
        Stmt::Let {
            name: cursor.clone(),
            mutable: true,
            expr: iter.clone(),
        },
        Stmt::While {
            cond: Expr::Bool(true),
            body: advance(lowered_inner),
        },
    ]
}

/// `len(TextList)` resolves via `TextListLen`; all other `len()` calls are
/// left for the normal body checker.
fn rewrite_len_textlist(body: &[Stmt], env: &HashMap<String, LocalTy>) -> Vec<Stmt> {
    fn go_expr(expr: &Expr, env: &HashMap<String, LocalTy>, depth: usize) -> Expr {
        if depth > MAX_DEPTH {
            return expr.clone();
        }
        match expr {
            Expr::Call { name, args } if name == "len" && args.len() == 1 => {
                let inner = go_expr(&args[0], env, depth + 1);
                // Resolve via the local environment; Vec/Text/Bytes/Word and
                // other owners keep plain `len`.
                let probe = Expr::Var("__probe__".into());
                let _ = probe;
                if let Expr::Var(v) = &inner {
                    if env.get(v).is_some_and(|t| t.is_text_list()) {
                        return Expr::Call {
                            name: "TextListLen".into(),
                            args: vec![inner],
                        };
                    }
                }
                Expr::Call {
                    name: "len".into(),
                    args: vec![inner],
                }
            }
            Expr::Call { name, args } => Expr::Call {
                name: name.clone(),
                args: args.iter().map(|a| go_expr(a, env, depth + 1)).collect(),
            },
            Expr::Field { base, field } => Expr::Field {
                base: Box::new(go_expr(base, env, depth + 1)),
                field: field.clone(),
            },
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(go_expr(base, env, depth + 1)),
                index: Box::new(go_expr(index, env, depth + 1)),
            },
            Expr::BinOp { op, left, right } => Expr::BinOp {
                op: *op,
                left: Box::new(go_expr(left, env, depth + 1)),
                right: Box::new(go_expr(right, env, depth + 1)),
            },
            Expr::Not(inner) => Expr::Not(Box::new(go_expr(inner, env, depth + 1))),
            other => other.clone(),
        }
    }
    fn go_stmts(body: &[Stmt], env: &HashMap<String, LocalTy>, depth: usize) -> Vec<Stmt> {
        if depth > MAX_DEPTH {
            return body.to_vec();
        }
        body.iter()
            .map(|s| match s {
                Stmt::Let {
                    name,
                    mutable,
                    expr,
                } => Stmt::Let {
                    name: name.clone(),
                    mutable: *mutable,
                    expr: go_expr(expr, env, depth + 1),
                },
                Stmt::Assign { name, expr } => Stmt::Assign {
                    name: name.clone(),
                    expr: go_expr(expr, env, depth + 1),
                },
                Stmt::Return(e) => Stmt::Return(go_expr(e, env, depth + 1)),
                Stmt::ExprStmt(e) => Stmt::ExprStmt(go_expr(e, env, depth + 1)),
                Stmt::If { cond, then, else_ } => Stmt::If {
                    cond: go_expr(cond, env, depth + 1),
                    then: go_stmts(then, env, depth + 1),
                    else_: go_stmts(else_, env, depth + 1),
                },
                Stmt::While { cond, body } => Stmt::While {
                    cond: go_expr(cond, env, depth + 1),
                    body: go_stmts(body, env, depth + 1),
                },
                Stmt::For { var, iter, body } => Stmt::For {
                    var: var.clone(),
                    iter: go_expr(iter, env, depth + 1),
                    body: go_stmts(body, env, depth + 1),
                },
                Stmt::Unsafe { body } => Stmt::Unsafe {
                    body: go_stmts(body, env, depth + 1),
                },
                other => other.clone(),
            })
            .collect()
    }
    go_stmts(body, env, 0)
}
// ---------------------------------------------------------------------------
// JSON derivation: per-entity records + Decode/DecodeAt/Encode operations.
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct JsonField {
    name: String,
    ty: TypeRef,
    nested: Option<String>,
    required: bool,
    /// Declared `defaults <field> to <value>`; missing fields take it.
    default: Option<Expr>,
    upper: Option<i64>,
    item_upper: Option<i64>,
}

fn collect_json_fields(
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    diags: &mut Vec<Diagnostic>,
) -> Vec<JsonField> {
    let defaults: HashMap<&str, &Expr> = entity
        .json
        .defaults
        .iter()
        .map(|d| (d.name.as_str(), &d.value))
        .collect();
    let mut out = Vec::new();
    for field in &entity.fields {
        let nested = match &field.ty {
            TypeRef::Named(n) if schema_scalar(&field.ty) => None,
            TypeRef::Named(n) => entities
                .get(n.as_str())
                .filter(|t| t.json.enabled)
                .map(|t| t.name.clone()),
            _ => None,
        };
        let (upper, item_upper) = early_bounds(entity, &field.name);
        // Required unless a default exists. Schema `requires` clauses may
        // still reference the field; missing-field failure is -22 when no
        // otherwise supplies -28 semantics (checked at derive time).
        let default = defaults
            .get(field.name.as_str())
            .map(|value| (*value).clone());
        let required = default.is_none();
        if nested.is_none() && !schema_scalar(&field.ty) {
            diags.push(err(
                "DEC301",
                format!(
                    "entity `{}` field `{}` is not a JSON scalar or nested JSON entity",
                    entity.name, field.name
                ),
                &field.span,
            ));
        }
        out.push(JsonField {
            name: field.name.clone(),
            ty: field.ty.clone(),
            nested,
            required,
            default,
            upper,
            item_upper,
        });
    }
    out
}

/// Canonical upper-bound clauses become early decode limits:
/// `len(list) <= N otherwise -28` and `TextListEachAtMost(list, usize(N))
/// otherwise -28`.
fn early_bounds(entity: &EntityDecl, field: &str) -> (Option<i64>, Option<i64>) {
    let mut upper = None;
    let mut item_upper = None;
    for clause in &entity.json.requires {
        if clause.otherwise.as_ref().and_then(const_i64) != Some(-28) {
            continue;
        }
        match &clause.condition {
            Expr::BinOp {
                op: BinOp::Le,
                left,
                right,
            } => {
                if let Expr::Call { name, args } = left.as_ref() {
                    if name == "len"
                        && args.len() == 1
                        && matches!(&args[0], Expr::Var(v) if v == field)
                    {
                        if let Expr::Int(n) = right.as_ref() {
                            upper = Some(*n);
                        }
                    }
                }
            }
            Expr::Call { name, args } if name == "TextListEachAtMost" && args.len() == 2 => {
                if matches!(&args[0], Expr::Var(v) if v == field) {
                    if let Expr::Call {
                        name: inner,
                        args: inner_args,
                    } = &args[1]
                    {
                        if inner == "usize" && inner_args.len() == 1 {
                            if let Expr::Int(n) = &inner_args[0] {
                                item_upper = Some(*n);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    (upper, item_upper)
}

fn derive_json(
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    taken: &mut HashSet<String>,
) -> Result<Vec<Item>, Vec<Diagnostic>> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    let fields = collect_json_fields(entity, entities, &mut diags);
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    let result_name = format!("{GEN_TOP}{}JsonResult", entity.name);
    let decode_name = format!("{}DecodeJson", entity.name);
    let decode_at_name = format!("{}DecodeJsonAt", entity.name);
    let encode_name = format!("{}EncodeJson", entity.name);
    for name in [&result_name, &decode_name, &decode_at_name, &encode_name] {
        if taken.contains(name.as_str()) {
            diags.push(err(
                "DEC306",
                format!(
                    "derived JSON name `{name}` collides with a source declaration for entity `{}`",
                    entity.name
                ),
                &entity.span,
            ));
        }
    }
    if diags.iter().any(|d| d.severity == Severity::Error) {
        return Err(diags);
    }
    for name in [&result_name, &decode_name, &decode_at_name, &encode_name] {
        taken.insert(name.clone());
    }
    Ok(vec![
        derive_result_record(entity, &result_name),
        derive_decode(entity, &fields, entities, &result_name, &decode_name, false),
        derive_decode(
            entity,
            &fields,
            entities,
            &result_name,
            &decode_at_name,
            true,
        ),
        real_derive_encode(entity, &fields, &encode_name),
    ])
}

fn derive_result_record(entity: &EntityDecl, name: &str) -> Item {
    let span = entity.span.clone();
    Item::Entity(EntityDecl {
        name: name.into(),
        span,
        fields: vec![
            sal_syntax::FieldDecl {
                name: "status".into(),
                ty: TypeRef::Named("i64".into()),
                span: entity.span.clone(),
            },
            sal_syntax::FieldDecl {
                name: "value".into(),
                ty: TypeRef::Named(entity.name.clone()),
                span: entity.span.clone(),
            },
            sal_syntax::FieldDecl {
                name: "written".into(),
                ty: TypeRef::Named("usize".into()),
                span: entity.span.clone(),
            },
            sal_syntax::FieldDecl {
                name: "read_end".into(),
                ty: TypeRef::Named("usize".into()),
                span: entity.span.clone(),
            },
        ],
        invariants: Vec::new(),
        c_layout: false,
        json: Default::default(),
        iteration: None,
        generated: true,
    })
}

fn call(name: impl Into<String>, args: Vec<Expr>) -> Expr {
    Expr::Call {
        name: name.into(),
        args,
    }
}
fn var(name: impl Into<String>) -> Expr {
    Expr::Var(name.into())
}
fn int(v: i64) -> Expr {
    Expr::Int(v)
}
fn field(base: Expr, name: &str) -> Expr {
    Expr::Field {
        base: Box::new(base),
        field: name.into(),
    }
}

/// Derived decoder. Shape (SAL source emitted as AST):
/// - open `JsonModelBegin`; on -22 return the result with that status.
/// - scratch: `let payload = slice_mut(storage, 0, usable)` (payload grows
///   from the front) and `let keybuf = slice_mut(storage, usable, scratch)`
///   at the storage end; `usable = len(storage) - scratch`, `scratch =
///   max(32, longest declared field name)`. Payload/key windows are
///   disjoint by construction; both end before value construction.
/// - cursor loop: `JsonModelNext(input, cursor, key)` parses separators /
///   key / colon only, NOT the value. `key_length = -1` means a valid but.
///   overlong key: never fatal, skip via `JsonValueEnd`.
/// - recognized fields decode via `JsonModelRead*` (incremental, so bound
///   excess fails -28 before later input is scanned) or nested decoders;
///   duplicate decoded field names (post-escape) are rejected.
/// - unknown fields are fully validated then ignored via
///   `JsonValueEnd(input, value_start, 64)`.
/// - cursor advances as `JsonModelCursor(read_end, false)` after every
///   member; `}` ends the loop with `read_end` after the brace.
/// - defaults fill missing fields; missing required fields fail -22;
///   schema `requires` evaluate after decode with `-28` early-limit bounds
///   enforced BEFORE later input is scanned where the shape allows.
/// - top-level `Decode` validates whole input incl trailing bytes
///   (`JsonWhitespaceEnd(read_end) == len(input)`); `DecodeAt` permits
///   trailing outer fields and reports `read_end` at the brace.
fn derive_decode(
    entity: &EntityDecl,
    fields: &[JsonField],
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
    op_name: &str,
    at: bool,
) -> Item {
    let span = entity.span.clone();
    let max_field = fields
        .iter()
        .map(|f| f.name.len() as i64)
        .max()
        .unwrap_or(0)
        .max(KEY_MIN);
    let start_arg: Expr = if at {
        var("start")
    } else {
        call("usize", vec![int(0)])
    };
    let start_pos: Expr = if at { var("start") } else { int(0) };
    let mut body: Vec<Stmt> = vec![Stmt::Let {
        name: "SalDeclBeg".into(),
        mutable: false,
        expr: call("JsonModelBegin", vec![var("input"), start_arg]),
    }];
    body.push(Stmt::If {
        cond: Expr::BinOp {
            op: BinOp::Ne,
            left: Box::new(field(var("SalDeclBeg"), "status")),
            right: Box::new(int(0)),
        },
        then: vec![Stmt::Return(call(
            result_name,
            vec![
                field(var("SalDeclBeg"), "status"),
                call(&entity.name, default_args_for(entity, entities)),
                call("usize", vec![int(0)]),
                start_pos.clone(),
            ],
        ))],
        else_: Vec::new(),
    });
    // Scratch bookkeeping: payload front, key window at the storage end.
    // usable = len(storage) - scratch; disjoint by construction.
    body.push(Stmt::Let {
        name: "SalDeclTotal".into(),
        mutable: false,
        expr: call("len", vec![var("storage")]),
    });
    body.push(Stmt::If {
        cond: Expr::BinOp {
            op: BinOp::Lt,
            left: Box::new(var("SalDeclTotal")),
            right: Box::new(call("usize", vec![int(max_field)])),
        },
        then: vec![Stmt::Return(call(
            result_name,
            vec![
                int(-28),
                call(&entity.name, default_args_for(entity, entities)),
                call("usize", vec![int(0)]),
                start_pos.clone(),
            ],
        ))],
        else_: Vec::new(),
    });
    body.push(Stmt::Let {
        name: "SalDeclUsable".into(),
        mutable: false,
        expr: Expr::BinOp {
            op: BinOp::Sub,
            left: Box::new(var("SalDeclTotal")),
            right: Box::new(call("usize", vec![int(max_field)])),
        },
    });
    body.push(Stmt::Let {
        name: "SalDeclPayload".into(),
        mutable: false,
        expr: call(
            "slice_mut",
            vec![
                var("storage"),
                call("usize", vec![int(0)]),
                var("SalDeclUsable"),
            ],
        ),
    });
    body.push(Stmt::Let {
        name: "SalDeclKey".into(),
        mutable: false,
        expr: call(
            "slice_mut",
            vec![
                var("storage"),
                var("SalDeclUsable"),
                call("usize", vec![int(max_field)]),
            ],
        ),
    });
    body.push(Stmt::Let {
        name: "SalDeclEnd".into(),
        mutable: true,
        expr: call("usize", vec![int(0)]),
    });
    for f in fields {
        body.push(Stmt::Let {
            name: format!("SalDeclSeen{}", f.name),
            mutable: true,
            expr: Expr::Bool(false),
        });
        body.push(Stmt::Let {
            name: format!("SalDeclVal{}", f.name),
            mutable: true,
            expr: f
                .default
                .clone()
                .unwrap_or_else(|| default_holder(f, entities)),
        });
    }
    body.push(Stmt::Let {
        name: "SalDeclCursor".into(),
        mutable: true,
        expr: field(var("SalDeclBeg"), "cursor"),
    });
    body.push(Stmt::Let {
        name: "SalDeclDone".into(),
        mutable: true,
        expr: Expr::Bool(false),
    });
    body.push(Stmt::Let {
        name: "SalDeclHandled".into(),
        mutable: true,
        expr: Expr::Bool(false),
    });
    body.push(real_loop_stmt(entity, fields, entities, result_name));
    // End read views before mutation/return: payload/key loans end here so
    // only output-rooted values escape.
    body.push(Stmt::ExprStmt(call(
        "borrow_end",
        vec![var("SalDeclPayload")],
    )));
    body.push(Stmt::ExprStmt(call("borrow_end", vec![var("SalDeclKey")])));
    body.extend(real_decode_tail(entity, fields, entities, result_name, at));
    let mut accepts = vec![
        sal_syntax::ParamDecl {
            name: "input".into(),
            ty: TypeRef::Named("Bytes".into()),
        },
        sal_syntax::ParamDecl {
            name: "storage".into(),
            ty: TypeRef::Named("MutBytes".into()),
        },
    ];
    if at {
        accepts.insert(
            1,
            sal_syntax::ParamDecl {
                name: "start".into(),
                ty: TypeRef::Named("usize".into()),
            },
        );
    }
    Item::Operation(OperationDecl {
        name: op_name.into(),
        span,
        accepts,
        returns: Some(TypeRef::Named(result_name.into())),
        effects: Vec::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        ownership: sal_syntax::OwnershipDecl {
            lowered: true,
            ..Default::default()
        },
        generated: true,
        responds_literal: None,
        c_export: None,
        c_import: None,
        body,
    })
}

// Real decoder emission: member loop, tail, encoder.
// ---------------------------------------------------------------------------

/// Emit one member-loop iteration as straight-line SAL AST. State holdings:
/// `SalDeclEnd` (usize write cursor into payload front), presence flags
/// `SalDeclSeen<field>`, value holders `SalDeclVal<field>`, plus the
/// scratch-length `SalDeclKeyLen`. The caller wraps this in the while loop.
fn member_iteration(
    entity: &EntityDecl,
    fields: &[JsonField],
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
) -> Vec<Stmt> {
    // Parse separators/key/colon only, NOT the value.
    let mut out = vec![Stmt::Let {
        name: "SalDeclMem".into(),
        mutable: false,
        expr: call(
            "JsonModelNext",
            vec![var("input"), var("SalDeclCursor"), var("SalDeclKey")],
        ),
    }];
    out.push(Stmt::If {
        cond: Expr::BinOp {
            op: BinOp::Ne,
            left: Box::new(field(var("SalDeclMem"), "status")),
            right: Box::new(int(0)),
        },
        then: vec![Stmt::Return(call(
            result_name,
            vec![
                field(var("SalDeclMem"), "status"),
                call(&entity.name, default_args_for(entity, entities)),
                call("usize", vec![int(0)]),
                field(var("SalDeclMem"), "read_end"),
            ],
        ))],
        else_: Vec::new(),
    });
    // Closing brace: end of object with read_end after `}`.
    out.push(Stmt::If {
        cond: Expr::Not(Box::new(field(var("SalDeclMem"), "present"))),
        then: vec![Stmt::Assign {
            name: "SalDeclDone".into(),
            expr: Expr::Bool(true),
        }],
        else_: Vec::new(),
    });
    out.push(Stmt::If {
        cond: field(var("SalDeclMem"), "present"),
        then: member_dispatch(entity, fields, entities, result_name),
        else_: Vec::new(),
    });
    out.push(Stmt::If {
        cond: Expr::Not(Box::new(var("SalDeclHandled"))),
        then: vec![Stmt::Assign {
            name: "SalDeclCursor".into(),
            expr: call(
                "JsonModelCursor",
                vec![field(var("SalDeclMem"), "read_end"), Expr::Bool(false)],
            ),
        }],
        else_: Vec::new(),
    });
    out.push(Stmt::Assign {
        name: "SalDeclHandled".into(),
        expr: Expr::Bool(false),
    });
    out.push(Stmt::If {
        cond: var("SalDeclDone"),
        then: vec![Stmt::Break],
        else_: Vec::new(),
    });
    out
}

fn default_args_for(entity: &EntityDecl, entities: &HashMap<&str, &EntityDecl>) -> Vec<Expr> {
    default_args_inner(entity, entities, 0)
}

fn default_args_inner(
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    depth: usize,
) -> Vec<Expr> {
    entity
        .fields
        .iter()
        .map(|f| default_field_value(f, entities, depth))
        .collect()
}

fn default_field_value(
    f: &sal_syntax::FieldDecl,
    entities: &HashMap<&str, &EntityDecl>,
    depth: usize,
) -> Expr {
    match &f.ty {
        TypeRef::Named(n) if n == "Text" => Expr::Lit(String::new()),
        TypeRef::Named(n) if n == "bool" => Expr::Bool(false),
        TypeRef::Named(n) if n == "u64" => call("u64", vec![int(0)]),
        TypeRef::Named(n) if n == "TextList" => call(
            "TextList",
            vec![
                call("bytes", vec![Expr::Lit(String::new())]),
                call("usize", vec![int(0)]),
            ],
        ),
        TypeRef::Named(n) if depth < MAX_DEPTH => match entities.get(n.as_str()) {
            Some(target) if target.json.enabled => {
                call(n, default_args_inner(target, entities, depth + 1))
            }
            _ => int(0),
        },
        _ => int(0),
    }
}

fn default_holder(f: &JsonField, entities: &HashMap<&str, &EntityDecl>) -> Expr {
    match &f.ty {
        TypeRef::Named(n) if n == "Text" => Expr::Lit(String::new()),
        TypeRef::Named(n) if n == "bool" => Expr::Bool(false),
        TypeRef::Named(n) if n == "u64" => call("u64", vec![int(0)]),
        TypeRef::Named(n) if n == "TextList" => call(
            "TextList",
            vec![
                call("bytes", vec![Expr::Lit(String::new())]),
                call("usize", vec![int(0)]),
            ],
        ),
        TypeRef::Named(n) => match entities.get(n.as_str()) {
            Some(target) if target.json.enabled => call(n, default_args_inner(target, entities, 1)),
            _ => int(0),
        },
        _ => int(0),
    }
}

/// Field dispatch: `if KeyEquals(...) { decode } else if ... else { skip }`.
/// Each recognized arm rejects duplicate decoded field names, decodes the
/// value exactly once, and advances the cursor. Unknown fields are fully
/// validated via `JsonValueEnd` then ignored. Too-long valid keys
/// (`key_length == -1`) can never match; they fall to the skip arm.
fn member_dispatch(
    entity: &EntityDecl,
    fields: &[JsonField],
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
) -> Vec<Stmt> {
    let mut otherwise: Vec<Stmt> = vec![
        Stmt::Let {
            name: "SalDeclSkip".into(),
            mutable: false,
            expr: call(
                "JsonValueEnd",
                vec![
                    var("input"),
                    field(var("SalDeclMem"), "value_start"),
                    call("usize", vec![int(SKIP_DEPTH)]),
                ],
            ),
        },
        Stmt::If {
            cond: Expr::BinOp {
                op: BinOp::Lt,
                left: Box::new(var("SalDeclSkip")),
                right: Box::new(int(0)),
            },
            then: vec![Stmt::Return(call(
                result_name,
                vec![
                    int(-22),
                    call(&entity.name, default_args_for(entity, entities)),
                    call("usize", vec![int(0)]),
                    field(var("SalDeclMem"), "value_start"),
                ],
            ))],
            else_: Vec::new(),
        },
        Stmt::Assign {
            name: "SalDeclCursor".into(),
            expr: call(
                "JsonModelCursor",
                vec![call("usize", vec![var("SalDeclSkip")]), Expr::Bool(false)],
            ),
        },
        Stmt::Assign {
            name: "SalDeclHandled".into(),
            expr: Expr::Bool(true),
        },
    ];
    for f in fields.iter().rev() {
        let arm = field_arm(entity, f, entities, result_name);
        otherwise = vec![Stmt::If {
            cond: call(
                "JsonModelKeyEquals",
                vec![
                    var("SalDeclKey"),
                    field(var("SalDeclMem"), "key_length"),
                    Expr::Lit(f.name.clone()),
                ],
            ),
            then: arm,
            else_: otherwise,
        }];
    }
    otherwise
}

fn field_arm(
    entity: &EntityDecl,
    f: &JsonField,
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
) -> Vec<Stmt> {
    let mut arm: Vec<Stmt> = Vec::new();
    // Duplicate decoded field names are rejected (post-escape comparison).
    arm.push(Stmt::If {
        cond: var(format!("SalDeclSeen{}", f.name)),
        then: vec![Stmt::Return(call(
            result_name,
            vec![
                int(-22),
                call(&entity.name, default_args_for(entity, entities)),
                call("usize", vec![int(0)]),
                field(var("SalDeclMem"), "value_start"),
            ],
        ))],
        else_: Vec::new(),
    });
    let start = field(var("SalDeclMem"), "value_start");
    match field_reader(f) {
        ReaderKind::I64 => {
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call("JsonModelReadI64", vec![var("input"), start]),
            });
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(advance_cursor_from("SalDeclRead"));
        }
        ReaderKind::U64 => {
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call("JsonModelReadU64", vec![var("input"), start]),
            });
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(advance_cursor_from("SalDeclRead"));
        }
        ReaderKind::Bool => {
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call("JsonModelReadBool", vec![var("input"), start]),
            });
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(advance_cursor_from("SalDeclRead"));
        }
        ReaderKind::Text => {
            // Decoded UTF8 borrows the payload window: carve the value slice
            // from the payload front at SalDeclEnd, decode into it, freeze
            // with text(), end the view, advance SalDeclEnd by written.
            arm.push(Stmt::Let {
                name: "SalDeclSpan".into(),
                mutable: false,
                expr: call(
                    "slice_mut",
                    vec![
                        var("SalDeclPayload"),
                        var("SalDeclEnd"),
                        Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(call("len", vec![var("SalDeclPayload")])),
                            right: Box::new(var("SalDeclEnd")),
                        },
                    ],
                ),
            });
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call(
                    "JsonModelReadText",
                    vec![var("input"), start, var("SalDeclSpan")],
                ),
            });
            arm.push(Stmt::ExprStmt(call("borrow_end", vec![var("SalDeclSpan")])));
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            // -28 maps to capacity failure here; value is unusable unless 0.
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(Stmt::Assign {
                name: "SalDeclEnd".into(),
                expr: Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(var("SalDeclEnd")),
                    right: Box::new(field(var("SalDeclRead"), "written")),
                },
            });
            arm.push(advance_cursor_from("SalDeclRead"));
        }
        ReaderKind::TextList { upper, item_upper } => {
            arm.push(Stmt::Let {
                name: "SalDeclSpan".into(),
                mutable: false,
                expr: call(
                    "slice_mut",
                    vec![
                        var("SalDeclPayload"),
                        var("SalDeclEnd"),
                        Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(call("len", vec![var("SalDeclPayload")])),
                            right: Box::new(var("SalDeclEnd")),
                        },
                    ],
                ),
            });
            let (max_items, max_item_bytes) = (
                upper
                    .map(int)
                    .unwrap_or_else(|| call("usize", vec![int(0)])),
                item_upper
                    .map(int)
                    .unwrap_or_else(|| call("usize", vec![int(0)])),
            );
            // usize() wrap for limit params (0 = unbounded except capacity).
            let max_items = match upper {
                Some(_) => call("usize", vec![max_items]),
                None => call("usize", vec![int(0)]),
            };
            let max_item_bytes = match item_upper {
                Some(_) => call("usize", vec![max_item_bytes]),
                None => call("usize", vec![int(0)]),
            };
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call(
                    "JsonModelReadTextList",
                    vec![
                        var("input"),
                        start,
                        var("SalDeclSpan"),
                        max_items,
                        max_item_bytes,
                    ],
                ),
            });
            arm.push(Stmt::ExprStmt(call("borrow_end", vec![var("SalDeclSpan")])));
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(Stmt::Assign {
                name: "SalDeclEnd".into(),
                expr: Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(var("SalDeclEnd")),
                    right: Box::new(field(var("SalDeclRead"), "written")),
                },
            });
            arm.push(advance_cursor_from("SalDeclRead"));
        }
        ReaderKind::Nested(nested) => {
            // Nested entity decoder writes into a checked target subspan;
            // decode at the member value start with the payload remainder.
            arm.push(Stmt::Let {
                name: "SalDeclSpan".into(),
                mutable: false,
                expr: call(
                    "slice_mut",
                    vec![
                        var("SalDeclPayload"),
                        var("SalDeclEnd"),
                        Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(call("len", vec![var("SalDeclPayload")])),
                            right: Box::new(var("SalDeclEnd")),
                        },
                    ],
                ),
            });
            arm.push(Stmt::Let {
                name: "SalDeclRead".into(),
                mutable: false,
                expr: call(
                    format!("{nested}DecodeJsonAt"),
                    vec![var("input"), start, var("SalDeclSpan")],
                ),
            });
            arm.push(Stmt::ExprStmt(call("borrow_end", vec![var("SalDeclSpan")])));
            arm.push(read_status_check(
                entity,
                entities,
                result_name,
                "SalDeclRead",
            ));
            arm.push(Stmt::Assign {
                name: format!("SalDeclVal{}", f.name),
                expr: field(var("SalDeclRead"), "value"),
            });
            arm.push(Stmt::Assign {
                name: "SalDeclEnd".into(),
                expr: Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(var("SalDeclEnd")),
                    right: Box::new(field(var("SalDeclRead"), "written")),
                },
            });
            arm.push(Stmt::Assign {
                name: "SalDeclCursor".into(),
                expr: call(
                    "JsonModelCursor",
                    vec![field(var("SalDeclRead"), "read_end"), Expr::Bool(false)],
                ),
            });
        }
    }
    arm.push(Stmt::Assign {
        name: format!("SalDeclSeen{}", f.name),
        expr: Expr::Bool(true),
    });
    // Mark handled so the outer cursor-advance keeps the field's read_end.
    arm.push(Stmt::Assign {
        name: "SalDeclHandled".into(),
        expr: Expr::Bool(true),
    });
    arm
}

enum ReaderKind {
    I64,
    U64,
    Bool,
    Text,
    TextList {
        upper: Option<i64>,
        item_upper: Option<i64>,
    },
    Nested(String),
}

fn field_reader(f: &JsonField) -> ReaderKind {
    if let Some(nested) = &f.nested {
        return ReaderKind::Nested(nested.clone());
    }
    match &f.ty {
        TypeRef::Named(n) if n == "i64" => ReaderKind::I64,
        TypeRef::Named(n) if n == "u64" => ReaderKind::U64,
        TypeRef::Named(n) if n == "bool" => ReaderKind::Bool,
        TypeRef::Named(n) if n == "Text" => ReaderKind::Text,
        TypeRef::Named(n) if n == "TextList" => ReaderKind::TextList {
            upper: f.upper,
            item_upper: f.item_upper,
        },
        _ => ReaderKind::I64,
    }
}

fn read_status_check(
    entity: &EntityDecl,
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
    read: &str,
) -> Stmt {
    Stmt::If {
        cond: Expr::BinOp {
            op: BinOp::Ne,
            left: Box::new(field(var(read), "status")),
            right: Box::new(int(0)),
        },
        then: vec![Stmt::Return(call(
            result_name,
            vec![
                field(var(read), "status"),
                call(&entity.name, default_args_for(entity, entities)),
                call("usize", vec![int(0)]),
                field(var(read), "read_end"),
            ],
        ))],
        else_: Vec::new(),
    }
}

fn advance_cursor_from(read: &str) -> Stmt {
    Stmt::Assign {
        name: "SalDeclCursor".into(),
        expr: call(
            "JsonModelCursor",
            vec![field(var(read), "read_end"), Expr::Bool(false)],
        ),
    }
}

fn real_loop_stmt(
    entity: &EntityDecl,
    fields: &[JsonField],
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
) -> Stmt {
    Stmt::While {
        cond: Expr::Not(Box::new(var("SalDeclDone"))),
        body: member_iteration(entity, fields, entities, result_name),
    }
}

fn real_decode_tail(
    entity: &EntityDecl,
    fields: &[JsonField],
    entities: &HashMap<&str, &EntityDecl>,
    result_name: &str,
    at: bool,
) -> Vec<Stmt> {
    let mut out = Vec::new();
    // Required-field presence: missing required fields fail -22.
    for f in fields {
        if f.required {
            out.push(Stmt::If {
                cond: Expr::Not(Box::new(var(format!("SalDeclSeen{}", f.name)))),
                then: vec![Stmt::Return(call(
                    result_name,
                    vec![
                        int(-22),
                        call(&entity.name, default_args_for(entity, entities)),
                        call("usize", vec![int(0)]),
                        field(var("SalDeclCursor"), "offset"),
                    ],
                ))],
                else_: Vec::new(),
            });
        }
    }
    // Assemble the value from holders/defaults; borrow provenance stays
    // storage-rooted because Text/TextList holders borrow the payload.
    let mut args: Vec<Expr> = Vec::new();
    for f in &entity.fields {
        let holder = format!("SalDeclVal{}", f.name);
        if fields.iter().any(|cf| cf.name == f.name) {
            args.push(var(holder));
        } else {
            args.push(int(0));
        }
    }
    out.push(Stmt::Let {
        name: "SalDeclValue".into(),
        mutable: false,
        expr: call(&entity.name, args),
    });
    // Schema requires evaluate on the decoded value; schema otherwise must
    // yield i64 status (negative). Omitted otherwise is -22.
    for clause in &entity.json.requires {
        let cond = substitute_field_refs(&clause.condition, entity);
        let status = clause.otherwise.as_ref().map_or_else(
            || int(-22),
            |otherwise| substitute_field_refs(otherwise, entity),
        );
        out.push(Stmt::If {
            cond: Expr::Not(Box::new(cond)),
            then: vec![Stmt::Return(call(
                result_name,
                vec![
                    status,
                    call(&entity.name, default_args_for(entity, entities)),
                    call("usize", vec![int(0)]),
                    field(var("SalDeclCursor"), "offset"),
                ],
            ))],
            else_: Vec::new(),
        });
    }
    if at {
        out.push(Stmt::Return(call(
            result_name,
            vec![
                int(0),
                var("SalDeclValue"),
                var("SalDeclEnd"),
                field(var("SalDeclCursor"), "offset"),
            ],
        )));
    } else {
        // Top-level Decode verifies whole input incl trailing bytes.
        out.push(Stmt::Let {
            name: "SalDeclTail".into(),
            mutable: false,
            expr: call(
                "JsonWhitespaceEnd",
                vec![var("input"), field(var("SalDeclCursor"), "offset")],
            ),
        });
        out.push(Stmt::If {
            cond: Expr::BinOp {
                op: BinOp::Or,
                left: Box::new(Expr::BinOp {
                    op: BinOp::Lt,
                    left: Box::new(var("SalDeclTail")),
                    right: Box::new(int(0)),
                }),
                right: Box::new(Expr::BinOp {
                    op: BinOp::Ne,
                    left: Box::new(call("usize", vec![var("SalDeclTail")])),
                    right: Box::new(call("len", vec![var("input")])),
                }),
            },
            then: vec![Stmt::Return(call(
                result_name,
                vec![
                    int(-22),
                    call(&entity.name, default_args_for(entity, entities)),
                    call("usize", vec![int(0)]),
                    call("usize", vec![var("SalDeclTail")]),
                ],
            ))],
            else_: Vec::new(),
        });
        out.push(Stmt::Return(call(
            result_name,
            vec![
                int(0),
                var("SalDeclValue"),
                var("SalDeclEnd"),
                call("usize", vec![var("SalDeclTail")]),
            ],
        )));
    }
    // Schema clauses may say `len(list)`: resolve TextList holders through
    // `TextListLen` exactly like operation bodies do.
    let env: HashMap<String, LocalTy> = fields
        .iter()
        .map(|f| (format!("SalDeclVal{}", f.name), LocalTy::from_ref(&f.ty)))
        .collect();
    rewrite_len_textlist(&out, &env)
}

/// Replace bare field references in schema clauses with value-holder reads.
/// Fields decode into `SalDeclVal<field>`; the assembled record is not yet
/// bound when requires evaluate, so conditions read the holders directly.
fn substitute_field_refs(expr: &Expr, entity: &EntityDecl) -> Expr {
    let known: std::collections::HashSet<&str> =
        entity.fields.iter().map(|f| f.name.as_str()).collect();
    fn go(e: &Expr, known: &std::collections::HashSet<&str>) -> Expr {
        match e {
            Expr::Var(v) if known.contains(v.as_str()) => var(format!("SalDeclVal{v}")),
            Expr::Call { name, args } => call(name, args.iter().map(|a| go(a, known)).collect()),
            Expr::Field { base, field } => Expr::Field {
                base: Box::new(go(base, known)),
                field: field.clone(),
            },
            Expr::Index { base, index } => Expr::Index {
                base: Box::new(go(base, known)),
                index: Box::new(go(index, known)),
            },
            Expr::BinOp { op, left, right } => Expr::BinOp {
                op: *op,
                left: Box::new(go(left, known)),
                right: Box::new(go(right, known)),
            },
            Expr::Not(inner) => Expr::Not(Box::new(go(inner, known))),
            other => other.clone(),
        }
    }
    go(expr, &known)
}

/// Derived encoder: `TypeEncodeJson(value, target) -> i64` bytes written or
/// negative. Writes `{`, then each field via `JsonModelWriteField` +
/// `JsonModelWrite*` (nested entities encode into a checked target subspan),
/// then `}`. Scalar-only DTO encoding is also applied to the warehouse
/// path per contract. Never truncated success: each step returns the
/// negative status on overflow.
fn real_derive_encode(entity: &EntityDecl, fields: &[JsonField], op_name: &str) -> Item {
    let span = entity.span.clone();
    let mut body: Vec<Stmt> = Vec::new();
    body.push(Stmt::Let {
        name: "SalDeclOff".into(),
        mutable: true,
        expr: call("usize", vec![int(0)]),
    });
    // One step register for every writer result: `next offset` for scalar
    // writers, `bytes written` for nested encoders, negative on failure.
    body.push(Stmt::Let {
        name: "SalDeclStep".into(),
        mutable: true,
        expr: call(
            "JsonModelWriteLiteral",
            vec![
                call("bytes", vec![Expr::Lit("{".into())]),
                var("target"),
                var("SalDeclOff"),
            ],
        ),
    });
    body.extend(step_or_return(false));
    for (index, f) in fields.iter().enumerate() {
        body.extend(encode_field(f, index == 0));
    }
    body.push(Stmt::Assign {
        name: "SalDeclStep".into(),
        expr: call(
            "JsonModelWriteLiteral",
            vec![
                call("bytes", vec![Expr::Lit("}".into())]),
                var("target"),
                var("SalDeclOff"),
            ],
        ),
    });
    body.push(Stmt::If {
        cond: Expr::BinOp {
            op: BinOp::Lt,
            left: Box::new(var("SalDeclStep")),
            right: Box::new(int(0)),
        },
        then: vec![Stmt::Return(var("SalDeclStep"))],
        else_: Vec::new(),
    });
    body.push(Stmt::Return(var("SalDeclStep")));
    Item::Operation(OperationDecl {
        name: op_name.into(),
        span,
        accepts: vec![
            sal_syntax::ParamDecl {
                name: "value".into(),
                ty: TypeRef::Named(entity.name.clone()),
            },
            sal_syntax::ParamDecl {
                name: "target".into(),
                ty: TypeRef::Named("MutBytes".into()),
            },
        ],
        returns: Some(TypeRef::Named("i64".into())),
        effects: Vec::new(),
        requires: Vec::new(),
        ensures: Vec::new(),
        ownership: sal_syntax::OwnershipDecl {
            lowered: true,
            ..Default::default()
        },
        generated: true,
        responds_literal: None,
        c_export: None,
        c_import: None,
        body,
    })
}

/// `if SalDeclStep < 0: return SalDeclStep.` then advance `SalDeclOff`:
/// scalar writers report the next absolute offset, nested encoders report
/// bytes written into their subspan (relative to `SalDeclOff`).
fn step_or_return(relative: bool) -> Vec<Stmt> {
    let advanced = if relative {
        Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(var("SalDeclOff")),
            right: Box::new(call("usize", vec![var("SalDeclStep")])),
        }
    } else {
        call("usize", vec![var("SalDeclStep")])
    };
    vec![
        Stmt::If {
            cond: Expr::BinOp {
                op: BinOp::Lt,
                left: Box::new(var("SalDeclStep")),
                right: Box::new(int(0)),
            },
            then: vec![Stmt::Return(var("SalDeclStep"))],
            else_: Vec::new(),
        },
        Stmt::Assign {
            name: "SalDeclOff".into(),
            expr: advanced,
        },
    ]
}

fn encode_field(f: &JsonField, first: bool) -> Vec<Stmt> {
    let mut out = Vec::new();
    let base = Expr::Field {
        base: Box::new(var("value")),
        field: f.name.clone(),
    };
    out.push(Stmt::Assign {
        name: "SalDeclStep".into(),
        expr: call(
            "JsonModelWriteField",
            vec![
                Expr::Lit(f.name.clone()),
                Expr::Bool(first),
                var("target"),
                var("SalDeclOff"),
            ],
        ),
    });
    out.extend(step_or_return(false));
    let scalar = |writer: &str| call(writer, vec![base.clone(), var("target"), var("SalDeclOff")]);
    let writer = match field_reader(f) {
        ReaderKind::I64 => scalar("JsonModelWriteI64"),
        ReaderKind::U64 => scalar("JsonModelWriteU64"),
        ReaderKind::Bool => scalar("JsonModelWriteBool"),
        ReaderKind::Text => scalar("JsonModelWriteText"),
        ReaderKind::TextList { .. } => scalar("JsonModelWriteTextList"),
        ReaderKind::Nested(nested) => {
            // Nested entity encoder writes into a checked target subspan.
            let sub = format!("SalDeclSub{}", f.name);
            out.push(Stmt::Let {
                name: sub.clone(),
                mutable: false,
                expr: call(
                    "slice_mut",
                    vec![
                        var("target"),
                        var("SalDeclOff"),
                        Expr::BinOp {
                            op: BinOp::Sub,
                            left: Box::new(call("len", vec![var("target")])),
                            right: Box::new(var("SalDeclOff")),
                        },
                    ],
                ),
            });
            out.push(Stmt::Assign {
                name: "SalDeclStep".into(),
                expr: call(format!("{nested}EncodeJson"), vec![base, var(sub.clone())]),
            });
            out.push(Stmt::ExprStmt(call("borrow_end", vec![var(sub)])));
            out.extend(step_or_return(true));
            return out;
        }
    };
    out.push(Stmt::Assign {
        name: "SalDeclStep".into(),
        expr: writer,
    });
    out.extend(step_or_return(false));
    out
}
