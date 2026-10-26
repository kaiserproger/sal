//! Pre-erasure type and affine ownership checks. No runtime policy lives here.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    channel_payload, checked_payload, err, is_canonical_call, mentions_concurrency, thread_payload,
    Payload, Registry, MAX_ARMS, MAX_DEPTH,
};
use sal_syntax::{BinOp, Diagnostic, Expr, Item, OperationDecl, Stmt, TypeRef};

type Ty = Option<TypeRef>;

pub(super) fn preflight(file: &sal_syntax::SalFile) -> Option<Diagnostic> {
    enum Node<'a> {
        Statement(&'a Stmt),
        Expression(&'a Expr),
        Type(&'a TypeRef),
    }
    let mut pending = Vec::new();
    for item in &file.items {
        match item {
            Item::Entity(entity) => {
                for field in &entity.fields {
                    pending.push((Node::Type(&field.ty), 0, &field.span));
                }
            }
            Item::Operation(operation) => {
                for param in &operation.accepts {
                    pending.push((Node::Type(&param.ty), 0, &operation.span));
                }
                if let Some(ty) = &operation.returns {
                    pending.push((Node::Type(ty), 0, &operation.span));
                }
                pending.extend(
                    operation
                        .body
                        .iter()
                        .map(|stmt| (Node::Statement(stmt), 0, &operation.span)),
                );
            }
            _ => {}
        }
    }
    while let Some((node, depth, span)) = pending.pop() {
        if depth > MAX_DEPTH {
            return Some(err(
                "CON208",
                "concurrent program exceeds supported nesting depth".into(),
                span,
            ));
        }
        match node {
            Node::Type(TypeRef::Generic { args, .. }) => {
                pending.extend(args.iter().map(|ty| (Node::Type(ty), depth + 1, span)))
            }
            Node::Type(TypeRef::Named(_)) => {}
            Node::Statement(stmt) => match stmt {
                Stmt::Let { expr, .. }
                | Stmt::Assign { expr, .. }
                | Stmt::Return(expr)
                | Stmt::ExprStmt(expr) => pending.push((Node::Expression(expr), depth + 1, span)),
                Stmt::If { cond, then, else_ } => {
                    pending.push((Node::Expression(cond), depth + 1, span));
                    pending.extend(
                        then.iter()
                            .chain(else_)
                            .map(|stmt| (Node::Statement(stmt), depth + 1, span)),
                    );
                }
                Stmt::While { cond, body }
                | Stmt::For {
                    iter: cond, body, ..
                } => {
                    pending.push((Node::Expression(cond), depth + 1, span));
                    pending.extend(
                        body.iter()
                            .map(|stmt| (Node::Statement(stmt), depth + 1, span)),
                    );
                }
                Stmt::Unsafe { body } => {
                    pending.extend(
                        body.iter()
                            .map(|stmt| (Node::Statement(stmt), depth + 1, span)),
                    );
                }
                Stmt::Break | Stmt::Continue => {}
            },
            Node::Expression(expr) => match expr {
                Expr::Call { args, .. } => pending.extend(
                    args.iter()
                        .map(|expr| (Node::Expression(expr), depth + 1, span)),
                ),
                Expr::Field { base, .. } | Expr::Not(base) => {
                    pending.push((Node::Expression(base), depth + 1, span))
                }
                Expr::Index { base, index } => {
                    pending.push((Node::Expression(base), depth + 1, span));
                    pending.push((Node::Expression(index), depth + 1, span));
                }
                Expr::BinOp { left, right, .. } => {
                    pending.push((Node::Expression(left), depth + 1, span));
                    pending.push((Node::Expression(right), depth + 1, span));
                }
                Expr::Var(_) | Expr::Int(_) | Expr::Lit(_) | Expr::Bool(_) | Expr::Float(_) => {}
            },
        }
    }
    None
}

fn named(name: &str) -> TypeRef {
    TypeRef::Named(name.into())
}
fn generic(name: &str, args: Vec<TypeRef>) -> TypeRef {
    TypeRef::Generic {
        name: name.into(),
        args,
    }
}
fn owned(ty: &TypeRef) -> bool {
    channel_payload(ty).is_some() || thread_payload(ty).is_some()
}

#[derive(Clone)]
struct Binding {
    ty: TypeRef,
    resource: Option<usize>,
}
#[derive(Clone)]
struct Resource {
    name: String,
    live: bool,
    depth: usize,
}
#[derive(Clone, Default)]
struct State {
    scopes: Vec<BTreeMap<String, Binding>>,
    resources: BTreeMap<usize, Resource>,
    next: usize,
}
impl State {
    fn lookup(&self, name: &str) -> Option<&Binding> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name))
    }
    fn live(&self) -> BTreeSet<usize> {
        self.resources
            .iter()
            .filter_map(|(id, resource)| resource.live.then_some(*id))
            .collect()
    }
}

pub(super) fn validate(file: &sal_syntax::SalFile, registry: &Registry) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for item in &file.items {
        let Item::Operation(operation) = item else {
            continue;
        };
        for param in &operation.accepts {
            validate_decl(&param.ty, operation, registry, &mut diagnostics);
        }
        if let Some(ty) = &operation.returns {
            validate_decl(ty, operation, registry, &mut diagnostics);
        }
        if operation.body.is_empty() {
            continue;
        }
        let mut checker = Checker {
            registry,
            operation,
            state: State::default(),
            diagnostics: &mut diagnostics,
            borrowed: BTreeSet::new(),
            loops: Vec::new(),
        };
        checker.state.scopes.push(BTreeMap::new());
        for param in &operation.accepts {
            checker.bind(&param.name, param.ty.clone());
        }
        if checker.block(&operation.body, 0, false, None) {
            checker.exit();
        }
    }
    diagnostics
}

fn validate_decl(
    ty: &TypeRef,
    operation: &OperationDecl,
    registry: &Registry,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if let TypeRef::Generic { name, args } = ty {
        let valid = match name.as_str() {
            "Channel" => {
                args.len() == 1
                    && checked_payload(&args[0], &registry.entities)
                        .is_some_and(|p| !matches!(p, Payload::Channel(_)))
            }
            "Thread" => args == &[named("i64")],
            "SendResult" | "ReceiveResult" | "WaitArm" => {
                args.len() == 1
                    && checked_payload(&args[0], &registry.entities)
                        .is_some_and(|p| !matches!(p, Payload::Channel(_)))
            }
            "WaitResult" => {
                !args.is_empty()
                    && args.len() <= MAX_ARMS
                    && args.iter().all(|arg| {
                        checked_payload(arg, &registry.entities)
                            .is_some_and(|p| !matches!(p, Payload::Channel(_)))
                    })
            }
            _ => !mentions_concurrency(ty),
        };
        if !valid {
            diagnostics.push(err("CON201", format!("unsupported concurrency type {ty:?}; payloads must be scalars or plain C records, and threads return i64"), &operation.span));
        }
    }
}

struct Checker<'a, 'd> {
    registry: &'a Registry,
    operation: &'a OperationDecl,
    state: State,
    diagnostics: &'d mut Vec<Diagnostic>,
    borrowed: BTreeSet<usize>,
    loops: Vec<BTreeSet<usize>>,
}
impl Checker<'_, '_> {
    fn report(&mut self, code: &'static str, message: impl Into<String>) {
        self.diagnostics
            .push(err(code, message.into(), &self.operation.span));
    }
    fn bind(&mut self, name: &str, ty: TypeRef) {
        if name.starts_with(super::GEN_PREFIX) {
            self.report(
                "CON208",
                "binding collides with compiler concurrency namespace",
            );
        }
        let resource = if owned(&ty) {
            let id = self.state.next;
            self.state.next += 1;
            self.state.resources.insert(
                id,
                Resource {
                    name: name.into(),
                    live: true,
                    depth: self.state.scopes.len(),
                },
            );
            Some(id)
        } else {
            None
        };
        self.state
            .scopes
            .last_mut()
            .expect("lexical scope")
            .insert(name.into(), Binding { ty, resource });
    }
    fn exit(&mut self) {
        let leaked: Vec<_> = self
            .state
            .resources
            .values()
            .filter(|r| r.live)
            .map(|r| r.name.clone())
            .collect();
        for name in leaked {
            self.report(
                "CON205",
                format!(
                    "owned handle `{name}` must be dropped, joined, or transferred on every exit"
                ),
            );
        }
    }
    fn require(&mut self, actual: &Ty, expected: &TypeRef) {
        if actual.as_ref().is_some_and(|actual| {
            actual != expected
                && !matches!(actual, TypeRef::Named(name) if name == "?")
                && !matches!(expected, TypeRef::Named(name) if name == "?")
        }) {
            self.report("CON202", format!("expected {expected:?}, found {actual:?}"));
        } else if actual.is_none() {
            self.report("CON202", format!("expected {expected:?}, found Void"));
        }
    }
    fn resource(&mut self, name: &str) -> Option<usize> {
        let binding = self.state.lookup(name).cloned()?;
        if let Some(id) = binding.resource {
            if !self.state.resources[&id].live {
                self.report(
                    "CON204",
                    format!("handle `{name}` was already moved, dropped, or joined"),
                );
            }
            Some(id)
        } else {
            None
        }
    }
    fn consume(&mut self, expr: &Expr) {
        if let Expr::Var(name) = expr {
            if let Some(id) = self.resource(name) {
                if self.borrowed.contains(&id) {
                    self.report(
                        "CON203",
                        format!("cannot consume `{name}` while a channel operation borrows it"),
                    );
                }
                self.state.resources.get_mut(&id).expect("resource").live = false;
            }
        }
    }
    fn channel(&mut self, expr: &Expr) -> Option<TypeRef> {
        let Expr::Var(name) = expr else {
            self.report("CON202", "channel operands must be bound channel variables");
            return None;
        };
        let binding = self.state.lookup(name).cloned();
        match binding {
            Some(binding) if channel_payload(&binding.ty).is_some() => {
                self.resource(name);
                Some(binding.ty)
            }
            _ => {
                self.report("CON202", format!("`{name}` is not a Channel<T>"));
                None
            }
        }
    }
    fn protect(&mut self, expr: &Expr) {
        if let Expr::Var(name) = expr {
            if let Some(id) = self.resource(name) {
                self.borrowed.insert(id);
            }
        }
    }
    fn block(
        &mut self,
        body: &[Stmt],
        depth: usize,
        nested: bool,
        induction: Option<(&str, TypeRef)>,
    ) -> bool {
        if depth > MAX_DEPTH {
            self.report("CON208", "concurrency body exceeds maximum nesting depth");
            return false;
        }
        if nested {
            self.state.scopes.push(BTreeMap::new());
        }
        if let Some((name, ty)) = induction {
            self.bind(name, ty);
        }
        let scope_depth = self.state.scopes.len();
        let mut continuing = true;
        for stmt in body {
            if !continuing {
                // Never manufacture an ownership proof for unreachable calls:
                // the ordinary compiler still checks/lower all source nodes.
                if super::body_mentions_canonical(std::slice::from_ref(stmt)) {
                    self.report(
                        "CON202",
                        "unreachable concurrency operation must be removed",
                    );
                }
                continue;
            }
            continuing = self.statement(stmt, depth + 1);
        }
        if nested {
            let leaked: Vec<_> = self
                .state
                .resources
                .values()
                .filter(|r| r.live && r.depth == scope_depth)
                .map(|r| r.name.clone())
                .collect();
            for name in leaked {
                self.report(
                    "CON205",
                    format!("handle `{name}` escapes its lexical scope without drop or join"),
                );
            }
            self.state.resources.retain(|_, r| r.depth != scope_depth);
            self.state.scopes.pop();
        }
        continuing
    }
    fn statement(&mut self, stmt: &Stmt, depth: usize) -> bool {
        match stmt {
            Stmt::Let { name, expr, .. } => {
                if self
                    .state
                    .scopes
                    .last()
                    .is_some_and(|scope| scope.contains_key(name))
                {
                    self.report("CON203", format!("duplicate binding `{name}`"));
                }
                let ty = self.expression(expr, None, depth, true);
                if let Some(ty) = ty {
                    if owned(&ty) && matches!(expr, Expr::Var(_)) {
                        self.report(
                            "CON203",
                            "implicit handle alias is forbidden; use channel_clone",
                        );
                    }
                    self.bind(name, ty);
                }
                true
            }
            Stmt::Assign { name, expr } => {
                let expected = self.state.lookup(name).map(|b| b.ty.clone());
                let ty = self.expression(expr, expected.as_ref(), depth, false);
                if expected.as_ref().is_some_and(owned) || ty.as_ref().is_some_and(owned) {
                    self.report("CON203", "owned handles cannot be reassigned");
                }
                true
            }
            Stmt::Return(expr) => {
                let expected = self.operation.returns.clone();
                let actual = self.expression(expr, expected.as_ref(), depth, true);
                if let Some(expected) = &expected {
                    self.require(&actual, expected);
                }
                if actual.as_ref().is_some_and(owned) {
                    if expected.as_ref() != actual.as_ref() {
                        self.report(
                            "CON203",
                            "owned handle return must match the declared channel/thread type",
                        );
                    }
                    self.consume(expr);
                }
                self.exit();
                false
            }
            Stmt::ExprStmt(expr) => {
                let ty = self.expression(expr, None, depth, false);
                if ty.as_ref().is_some_and(owned) {
                    self.report(
                        "CON205",
                        "discarding an owned handle leaks it; bind and consume it",
                    );
                }
                true
            }
            Stmt::Unsafe { body } => self.block(body, depth, false, None),
            Stmt::If { cond, then, else_ } => {
                self.expression(cond, Some(&named("bool")), depth, false);
                let before = self.state.clone();
                let left_cont = self.block(then, depth, true, None);
                let left = self.state.clone();
                self.state = before.clone();
                let right_cont = self.block(else_, depth, true, None);
                let right = self.state.clone();
                self.state = if left_cont {
                    left.clone()
                } else {
                    right.clone()
                };
                self.state.next = left.next.max(right.next);
                if left_cont && right_cont {
                    for id in before.resources.keys() {
                        if left.resources.get(id).map(|r| r.live)
                            != right.resources.get(id).map(|r| r.live)
                        {
                            self.report(
                                "CON205",
                                "handle consumption differs between continuing branches",
                            );
                        }
                    }
                }
                left_cont || right_cont
            }
            Stmt::While { cond, body }
            | Stmt::For {
                iter: cond, body, ..
            } => {
                let before_cond = self.state.live();
                let iterable = self.expression(cond, None, depth, false);
                if before_cond != self.state.live() {
                    self.report("CON205", "loop conditions cannot consume owned handles");
                }
                let before = self.state.clone();
                self.loops.push(before.live());
                let induction = if let Stmt::For { var, .. } = stmt {
                    let element = match iterable {
                        Some(TypeRef::Generic { name, mut args })
                            if name == "Vec" && args.len() == 1 =>
                        {
                            args.pop().expect("one iterable element type")
                        }
                        _ => named("?"),
                    };
                    Some((var.as_str(), element))
                } else {
                    None
                };
                let continuing = self.block(body, depth, true, induction);
                if continuing && before.live() != self.state.live() {
                    self.report(
                        "CON205",
                        "loop iterations must preserve outer handle ownership",
                    );
                }
                self.loops.pop();
                self.state = before;
                true
            }
            Stmt::Break | Stmt::Continue => {
                if let Some(entry) = self.loops.last() {
                    if *entry != self.state.live() {
                        self.report("CON205", "break/continue must preserve loop-entry handles and consume inner handles");
                    }
                } else {
                    self.report("CON202", "break/continue requires an enclosing loop");
                }
                false
            }
        }
    }
}

impl Checker<'_, '_> {
    fn hint(&self, expr: &Expr) -> Ty {
        match expr {
            Expr::Var(name) => self.state.lookup(name).map(|b| b.ty.clone()),
            Expr::Bool(_) | Expr::Not(_) => Some(named("bool")),
            Expr::Lit(_) => Some(named("Text")),
            Expr::Float(_) => Some(named("f64")),
            Expr::Call { name, args } => {
                if let Some(operation) = self.registry.operations.get(name) {
                    return operation.returns.clone();
                }
                if self.registry.entities.contains_key(name) {
                    return Some(named(name));
                }
                if let Some((_, result)) = crate::builtin_signature(name) {
                    return match result {
                        crate::BodyType::Named(name) => Some(named(name)),
                        _ => None,
                    };
                }
                if matches!(name.as_str(), "size_of" | "align_of" | "offset_of") {
                    return Some(named("usize"));
                }
                match name.as_str() {
                    "send" | "receive" => {
                        let ty = args.first().and_then(|arg| self.hint(arg))?;
                        let payload = channel_payload(&ty)?.clone();
                        Some(generic(
                            if name == "send" {
                                "SendResult"
                            } else {
                                "ReceiveResult"
                            },
                            vec![payload],
                        ))
                    }
                    "join" => Some(named("i64")),
                    "close" => Some(named("bool")),
                    _ => None,
                }
            }
            Expr::Field { base, field } => self.hint(base).and_then(|ty| self.project(&ty, field)),
            Expr::BinOp { op, left, right } => {
                if matches!(
                    op,
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
                ) {
                    self.hint(left).or_else(|| self.hint(right))
                } else {
                    Some(named("bool"))
                }
            }
            Expr::Int(_) | Expr::Index { .. } => None,
        }
    }
    fn project(&self, ty: &TypeRef, field: &str) -> Ty {
        match ty {
            TypeRef::Named(name) => self
                .registry
                .field_types
                .get(name)?
                .iter()
                .find(|(key, _)| key == field)
                .map(|(_, ty)| ty.clone()),
            TypeRef::Generic { name, args } => match (name.as_str(), field) {
                ("SendResult", "sent")
                | ("ReceiveResult", "open")
                | ("WaitArm", "selected" | "open") => Some(named("bool")),
                ("SendResult" | "ReceiveResult" | "WaitArm", "value") => args.first().cloned(),
                ("WaitResult", "index" | "status") => Some(named("usize")),
                ("WaitResult", field) => {
                    let index = field.strip_prefix("arm")?.parse::<usize>().ok()?;
                    args.get(index)
                        .cloned()
                        .map(|arg| generic("WaitArm", vec![arg]))
                }
                _ => None,
            },
        }
    }
    fn expression(
        &mut self,
        expr: &Expr,
        expected: Option<&TypeRef>,
        depth: usize,
        producer: bool,
    ) -> Ty {
        if depth > MAX_DEPTH {
            self.report("CON208", "concurrency expression exceeds maximum depth");
            return None;
        }
        let ty = match expr {
            Expr::Var(name) => {
                let binding = self.state.lookup(name).cloned();
                if binding.as_ref().is_some_and(|binding| binding.resource.is_some()) { self.resource(name); }
                Some(binding.map(|binding| binding.ty).unwrap_or_else(|| named("?")))
            }
            Expr::Int(value) => {
                let context = expected.filter(|ty| {
                    let name = match ty {
                        TypeRef::Named(name) => name.as_str(),
                        TypeRef::Generic { name, .. } => name.as_str(),
                    };
                    super::is_integer_name(name) || crate::int_bit_width(name).is_some()
                });
                if let Some(TypeRef::Named(name)) = context {
                    if !crate::integer_literal_fits(*value, crate::BodyType::Named(name)) { self.report("CON202", "integer literal does not fit the expected payload"); }
                }
                Some(context.cloned().unwrap_or_else(|| named("i64")))
            }
            Expr::Lit(_) => Some(expected.filter(|ty| matches!(ty, TypeRef::Named(name) if name == "Word" || name == "Character")).cloned().unwrap_or_else(|| named("Text"))),
            Expr::Float(_) => Some(named("f64")),
            Expr::Bool(_) => Some(named("bool")),
            Expr::Not(inner) => { self.expression(inner, Some(&named("bool")), depth + 1, false); Some(named("bool")) }
            Expr::Field { base, field } => {
                let base = self.expression(base, None, depth + 1, false);
                if base.as_ref().is_some_and(owned) { self.report("CON203", "owned handles have no accessible fields"); }
                let result = base.as_ref().and_then(|ty| self.project(ty, field));
                if result.is_none() && base.as_ref().is_some_and(mentions_concurrency) { self.report("CON202", format!("invalid concurrency result field `{field}`")); }
                result.or_else(|| Some(named("?")))
            }
            Expr::Index { base, index } => {
                let base = self.expression(base, None, depth + 1, false);
                self.expression(index, Some(&named("usize")), depth + 1, false);
                if base.as_ref().is_some_and(owned) { self.report("CON203", "owned handles cannot be indexed"); }
                match base { Some(TypeRef::Generic { name, args }) if name == "Vec" => args.first().cloned(), _ => Some(named("?")) }
            }
            Expr::BinOp { op, left, right } => {
                let boolean = matches!(op, BinOp::And | BinOp::Or);
                let arithmetic = matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem);
                let context = if boolean { Some(named("bool")) } else { expected.filter(|_| arithmetic).cloned().or_else(|| self.hint(left)).or_else(|| self.hint(right)) };
                let left_ty = self.expression(left, context.as_ref(), depth + 1, false);
                let before_right = self.state.live();
                let right_ty = self.expression(right, context.as_ref().or(left_ty.as_ref()), depth + 1, false);
                if boolean && before_right != self.state.live() { self.report("CON205", "short-circuit operands cannot conditionally consume handles"); }
                if left_ty.as_ref().is_some_and(owned) || right_ty.as_ref().is_some_and(owned) { self.report("CON203", "owned handles cannot be compared or used as integers"); }
                if arithmetic { left_ty } else { Some(named("bool")) }
            }
            Expr::Call { name, args } => self.call(name, args, depth + 1, producer),
        };
        if let Some(expected) = expected {
            self.require(&ty, expected);
        }
        ty
    }
    fn call(&mut self, name: &str, args: &[Expr], depth: usize, producer: bool) -> Ty {
        if depth > MAX_DEPTH {
            self.report("CON208", "concurrency call exceeds maximum depth");
            return None;
        }
        if is_canonical_call(name) {
            return self.concurrent_call(name, args, depth, producer);
        }
        if matches!(
            name,
            "operation_address" | "size_of" | "align_of" | "offset_of"
        ) {
            let valid = if name == "offset_of" {
                matches!(args, [Expr::Var(_), Expr::Lit(_)])
            } else {
                matches!(args, [Expr::Var(_)])
            };
            if !valid {
                self.report("CON202", "reflection and operation-address operands must be compile-time names (offset_of also takes a literal field name)");
            }
            return Some(named("usize"));
        }
        if crate::is_numeric_intrinsic(name) {
            return self.numeric_intrinsic(name, args, depth);
        }
        let registry = self.registry;
        if let Some(operation) = registry.operations.get(name) {
            for (index, arg) in args.iter().enumerate() {
                let expected = operation.accepts.get(index).map(|param| &param.ty);
                let actual = self.expression(arg, expected, depth + 1, expected.is_some_and(owned));
                if actual.as_ref().is_some_and(owned) {
                    if expected.is_some_and(owned) && expected == actual.as_ref() {
                        self.consume(arg);
                    } else {
                        self.report(
                            "CON203",
                            format!(
                                "owned handle cannot escape through `{name}` argument {}",
                                index + 1
                            ),
                        );
                    }
                }
            }
            if operation.returns.as_ref().is_some_and(owned) && !producer {
                self.report("CON202", "bind an owned operation result before using it");
            }
            return operation.returns.clone();
        }
        if let Some(fields) = registry.field_types.get(name) {
            for (index, arg) in args.iter().enumerate() {
                let ty =
                    self.expression(arg, fields.get(index).map(|(_, ty)| ty), depth + 1, false);
                if ty.as_ref().is_some_and(owned) {
                    self.report("CON203", "owned handles cannot be packed into records");
                }
            }
            return Some(named(name));
        }
        let signature = crate::builtin_signature(name);
        for (index, arg) in args.iter().enumerate() {
            let expected = signature
                .and_then(|(rules, _)| rules.get(index))
                .and_then(|rule| match rule {
                    crate::BuiltinArg::Exact(name) => Some(named(name)),
                    _ => None,
                });
            let actual = self.expression(arg, expected.as_ref(), depth + 1, false);
            if actual.as_ref().is_some_and(owned) {
                self.report(
                    "CON203",
                    format!("`{name}` cannot accept an owned handle as a raw value"),
                );
            }
        }
        match signature.map(|(_, result)| result) {
            Some(crate::BodyType::Named(name)) => Some(named(name)),
            Some(crate::BodyType::Void) => None,
            _ => Some(named("?")),
        }
    }
}

impl Checker<'_, '_> {
    fn arity(&mut self, name: &str, args: &[Expr], count: usize) -> bool {
        if args.len() != count {
            self.report("CON202", format!("`{name}` requires {count} operands"));
            false
        } else {
            true
        }
    }
    fn integer_type(&mut self, expr: &Expr, expected: Option<&TypeRef>, depth: usize) -> Ty {
        let actual = self.expression(expr, expected, depth + 1, false);
        if let Some(inner) = actual.as_ref() {
            if super::is_integer_name(&Self::type_name(inner)) {
                return Some(inner.clone());
            }
            if !matches!(inner, TypeRef::Named(name) if name == "?") {
                self.report("CON202", "numeric intrinsic requires integer types");
                return None;
            }
        }
        actual
    }
    fn type_name(ty: &TypeRef) -> String {
        match ty {
            TypeRef::Named(name) => name.clone(),
            TypeRef::Generic { name, .. } => name.clone(),
        }
    }
    fn numeric_intrinsic(&mut self, name: &str, args: &[Expr], depth: usize) -> Ty {
        if name == "bits_as" {
            if !self.arity(name, args, 2) {
                return None;
            }
            let target = match &args[0] {
                Expr::Var(target) if crate::int_bit_width(target).is_some() => target.clone(),
                _ => {
                    self.report(
                        "CON202",
                        "`bits_as` target must be a compile-time integer type name",
                    );
                    return None;
                }
            };
            let width = crate::int_bit_width(&target).expect("checked target");
            let expected = self
                .hint(&args[1])
                .filter(|ty| super::is_integer_name(&Self::type_name(ty)))
                .unwrap_or_else(|| named(&target));
            let value = self.expression(&args[1], Some(&expected), depth + 1, false);
            if let Some(value) = value.as_ref() {
                let same = match value {
                    TypeRef::Named(name) if name == "?" => true,
                    TypeRef::Named(found) => crate::int_bit_width(found) == Some(width),
                    _ => false,
                };
                if !same {
                    self.report(
                        "CON202",
                        format!("`bits_as` requires the same bit width as `{target}`"),
                    );
                    return None;
                }
                if super::mentions_memory_owner(value) {
                    self.report(
                        "CON203",
                        format!("`{name}` cannot accept an owned handle or span"),
                    );
                    return None;
                }
            }
            return Some(named(&target));
        }
        if name == "bit_not" {
            if !self.arity(name, args, 1) {
                return None;
            }
            let hinted = self
                .hint(&args[0])
                .filter(|ty| super::is_integer_name(&Self::type_name(ty)));
            let value = self.integer_type(&args[0], hinted.as_ref(), depth);
            if value.as_ref().is_some_and(super::mentions_memory_owner) {
                self.report(
                    "CON203",
                    format!("`{name}` cannot accept an owned handle or span"),
                );
                return None;
            }
            return value;
        }
        if name == "shift_left" || name == "shift_right" {
            if !self.arity(name, args, 2) {
                return None;
            }
            let hinted = self
                .hint(&args[0])
                .filter(|ty| super::is_integer_name(&Self::type_name(ty)));
            let value = self.integer_type(&args[0], hinted.as_ref(), depth);
            let count = self.expression(&args[1], Some(&named("usize")), depth + 1, false);
            if count.as_ref().is_some_and(|ty| ty != &named("usize")) {
                self.report(
                    "CON202",
                    format!("call `{name}` shift count requires usize"),
                );
                return None;
            }
            if value.as_ref().is_some_and(super::mentions_memory_owner) {
                self.report(
                    "CON203",
                    format!("`{name}` cannot accept an owned handle or span"),
                );
                return None;
            }
            return value;
        }
        if !self.arity(name, args, 2) {
            return None;
        }
        let hinted = self
            .hint(&args[0])
            .filter(|ty| super::is_integer_name(&Self::type_name(ty)))
            .or_else(|| {
                self.hint(&args[1])
                    .filter(|ty| super::is_integer_name(&Self::type_name(ty)))
            });
        let left = self.integer_type(&args[0], hinted.as_ref(), depth);
        let Some(left) = left else {
            self.expression(&args[1], None, depth + 1, false);
            return None;
        };
        let right = self.integer_type(&args[1], Some(&left), depth);
        if right.as_ref().is_some_and(|ty| ty != &left) {
            self.report("CON202", format!("`{name}` requires equal integer types"));
            return None;
        }
        if super::mentions_memory_owner(&left) {
            self.report(
                "CON203",
                format!("`{name}` cannot accept an owned handle or span"),
            );
            return None;
        }
        Some(left)
    }
    fn concurrent_call(&mut self, name: &str, args: &[Expr], depth: usize, producer: bool) -> Ty {
        if !self.operation.effects.iter().any(|own| own == "SystemCall") {
            self.report(
                "EFF203",
                format!(
                    "operation `{}` must declare `SystemCall` for concurrency",
                    self.operation.name
                ),
            );
        }
        if matches!(name, "channel" | "channel_clone" | "spawn") && !producer {
            self.report(
                "CON202",
                format!("`{name}` requires a binding, owned return, or consuming argument"),
            );
        }
        match name {
            "channel" => {
                if !self.arity(name, args, 2) {
                    return None;
                }
                let Expr::Var(payload) = &args[0] else {
                    self.report("CON202", "channel requires a payload type name");
                    return None;
                };
                let payload = named(payload);
                if !checked_payload(&payload, &self.registry.entities)
                    .is_some_and(|p| !matches!(p, Payload::Channel(_)))
                {
                    self.report(
                        "CON201",
                        "channel payload must be a native scalar or plain C record",
                    );
                }
                self.expression(&args[1], Some(&named("usize")), depth + 1, false);
                Some(generic("Channel", vec![payload]))
            }
            "channel_clone" | "channel_drop" | "close" | "receive" => {
                if !self.arity(name, args, 1) {
                    return None;
                }
                let channel = self.channel(&args[0])?;
                match name {
                    "channel_clone" => Some(channel),
                    "channel_drop" => {
                        self.consume(&args[0]);
                        None
                    }
                    "close" => Some(named("bool")),
                    "receive" => Some(generic(
                        "ReceiveResult",
                        vec![channel_payload(&channel)?.clone()],
                    )),
                    _ => unreachable!(),
                }
            }
            "send" => {
                if !self.arity(name, args, 2) {
                    return None;
                }
                let channel = self.channel(&args[0])?;
                let payload = channel_payload(&channel)?.clone();
                let borrowed = self.borrowed.clone();
                self.protect(&args[0]);
                self.expression(&args[1], Some(&payload), depth + 1, false);
                self.borrowed = borrowed;
                Some(generic("SendResult", vec![payload]))
            }
            "join" => {
                if !self.arity(name, args, 1) {
                    return None;
                }
                let ty = self.expression(
                    &args[0],
                    Some(&generic("Thread", vec![named("i64")])),
                    depth + 1,
                    true,
                );
                if ty.as_ref().is_some_and(|ty| thread_payload(ty).is_some()) {
                    self.consume(&args[0]);
                }
                Some(named("i64"))
            }
            "spawn" => {
                if !self.arity(name, args, 2) {
                    return None;
                }
                let Expr::Var(worker) = &args[0] else {
                    self.report("CON207", "spawn requires a worker operation name");
                    return None;
                };
                let registry = self.registry;
                let Some(operation) = registry.operations.get(worker) else {
                    self.report("CON207", "unknown spawn worker");
                    return None;
                };
                if operation.c_import.is_some()
                    || operation.body.is_empty()
                    || operation.accepts.len() != 1
                    || operation.returns != Some(named("i64"))
                {
                    self.report(
                        "CON207",
                        "worker must be a SAL operation accepting one Send value and returning i64",
                    );
                    return None;
                }
                let expected = &operation.accepts[0].ty;
                if !checked_payload(expected, &self.registry.entities).is_some_and(|p| match p {
                    Payload::Channel(inner) => !matches!(*inner, Payload::Channel(_)),
                    _ => true,
                }) {
                    self.report("CON201", "spawn worker argument is not Send");
                }
                let actual = self.expression(&args[1], Some(expected), depth + 1, owned(expected));
                if actual.as_ref().is_some_and(owned) {
                    if channel_payload(expected).is_some() && actual.as_ref() == Some(expected) {
                        self.consume(&args[1]);
                    } else {
                        self.report("CON207", "spawn may move only a matching Channel argument");
                    }
                }
                Some(generic("Thread", vec![named("i64")]))
            }
            "wait_for" => self.wait(args, depth),
            "timeout" | "otherwise" => {
                self.report(
                    "CON206",
                    "fallbacks are only valid as the last wait_for operand",
                );
                None
            }
            _ => unreachable!(),
        }
    }
    fn wait(&mut self, args: &[Expr], depth: usize) -> Ty {
        let mut arm_count = args.len();
        let fallback = if let Some(Expr::Call { name, args }) = args.last() {
            if name == "timeout" || name == "otherwise" {
                arm_count -= 1;
                Some((name, args))
            } else {
                None
            }
        } else {
            None
        };
        if arm_count == 0 || arm_count > MAX_ARMS {
            self.report(
                "CON206",
                format!("wait_for needs 1..={MAX_ARMS} send/receive arms"),
            );
            return None;
        }
        let borrowed = self.borrowed.clone();
        let mut payloads = Vec::new();
        for arm in &args[..arm_count] {
            let Expr::Call { name, args } = arm else {
                self.report("CON206", "wait_for arms must be send/receive calls");
                self.borrowed = borrowed;
                return None;
            };
            if !matches!(name.as_str(), "send" | "receive")
                || args.len() != if name == "send" { 2 } else { 1 }
            {
                self.report(
                    "CON206",
                    "wait_for arms must be receive(channel) or send(channel,value)",
                );
                self.borrowed = borrowed;
                return None;
            }
            let Some(channel) = self.channel(&args[0]) else {
                self.borrowed = borrowed;
                return None;
            };
            self.protect(&args[0]);
            payloads.push(channel_payload(&channel)?.clone());
        }
        for (index, arm) in args[..arm_count].iter().enumerate() {
            if let Expr::Call { name, args } = arm {
                if name == "send" {
                    self.expression(&args[1], Some(&payloads[index]), depth + 1, false);
                }
            }
        }
        if let Some((name, args)) = fallback {
            if name == "otherwise" {
                if !args.is_empty() {
                    self.report("CON206", "otherwise takes no operands");
                }
            } else if args.len() == 1 {
                self.expression(&args[0], Some(&named("usize")), depth + 1, false);
            } else {
                self.report("CON206", "timeout takes one millisecond count");
            }
        }
        self.borrowed = borrowed;
        Some(generic("WaitResult", payloads))
    }
}
