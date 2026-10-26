//! Typed concurrency wrappers; synchronization policy remains SAL source.
use super::{
    arm_name, box_name, chan_new_name, checked_payload, classify_typed, is_canonical_call,
    is_integer_name, nodes_name, payload_tag, recv_name, recv_op_name, send_name, send_op_name,
    tramp_name, wait_names, zero_name, ArmDir, DeclaredTy, Payload, PayloadDef, Registry,
    EXIT_GROUP, GEN_PREFIX,
};
use sal_syntax::{BinOp, EntityDecl, Expr, Item, OperationDecl, Span, Stmt, TypeRef};
use std::collections::{BTreeSet, HashMap};

type WaitShape = (Vec<(ArmDir, Payload)>, bool);

pub(super) fn rewrite(file: &sal_syntax::SalFile, registry: &Registry) -> sal_syntax::SalFile {
    Rewriter::new(registry).rewrite(file)
}

fn spawn_name(worker: &str, tag: &str) -> String {
    format!("{}Spawn", tramp_name(worker, tag))
}
struct Rewriter<'a> {
    registry: &'a Registry,
    payloads: Vec<PayloadDef>,
    seen_payload: BTreeSet<String>,
    temp_seq: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HandleKind {
    Channel,
    Thread,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ValTy {
    Handle(HandleKind, Payload),
    Value,
}

// ---------------------------------------------------------------------------
// Rewriter: erase handles to usize and emit generated wrappers.
// ---------------------------------------------------------------------------

impl<'a> Rewriter<'a> {
    fn new(registry: &'a Registry) -> Self {
        Rewriter {
            registry,
            payloads: Vec::new(),
            seen_payload: BTreeSet::new(),
            temp_seq: 0,
        }
    }
    fn fresh(&mut self, stem: &str) -> String {
        let seq = self.temp_seq;
        self.temp_seq += 1;
        format!("{GEN_PREFIX}{stem}{seq}")
    }
}

// ---------------------------------------------------------------------------
// Rewrite collection: payloads, tags, and generated item emission.
// ---------------------------------------------------------------------------

impl<'a> Rewriter<'a> {
    fn intern(&mut self, payload: &Payload) -> String {
        let ty = payload.type_ref();
        let tag = payload_tag(&ty).expect("checked payload has a tag");
        if self.seen_payload.insert(tag.clone()) {
            self.payloads.push(PayloadDef {
                tag: tag.clone(),
                payload: payload.clone(),
            });
        }
        tag
    }
}

// ---------------------------------------------------------------------------
// Rewriter: handle-type erasure plus generated wrapper emission.
// ---------------------------------------------------------------------------

impl<'a> Rewriter<'a> {
    fn erase_ty(&self, ty: &TypeRef) -> TypeRef {
        match ty {
            TypeRef::Named(_) => ty.clone(),
            TypeRef::Generic { name, args } => {
                if matches!(name.as_str(), "Channel" | "Thread") {
                    return TypeRef::Named("usize".into());
                }
                match classify_typed(ty, &self.registry.entities) {
                    DeclaredTy::SendRes(payload) => {
                        TypeRef::Named(send_name(&self.tag_of(&payload)))
                    }
                    DeclaredTy::RecvRes(payload) => {
                        TypeRef::Named(recv_name(&self.tag_of(&payload)))
                    }
                    DeclaredTy::WaitRes(payloads) => {
                        let tags: Vec<(ArmDir, String)> = payloads
                            .iter()
                            .map(|payload| (ArmDir::Recv, self.tag_of(payload)))
                            .collect();
                        let (_, res_name) = wait_names(&tags);
                        TypeRef::Named(res_name)
                    }
                    DeclaredTy::Chan(_) | DeclaredTy::Thread(_) => TypeRef::Named("usize".into()),
                    DeclaredTy::Plain | DeclaredTy::OtherGeneric => {
                        if name == "WaitArm" && args.len() == 1 {
                            if let Some(payload) =
                                checked_payload(&args[0], &self.registry.entities)
                            {
                                return TypeRef::Named(arm_name(&self.tag_of(&payload)));
                            }
                        }
                        TypeRef::Generic {
                            name: name.clone(),
                            args: args.clone(),
                        }
                    }
                }
            }
        }
    }
    fn intern_result_payloads(&mut self, ty: &TypeRef) {
        match classify_typed(ty, &self.registry.entities) {
            DeclaredTy::Chan(payload) | DeclaredTy::Thread(payload) => {
                self.intern(&payload);
            }
            DeclaredTy::SendRes(payload) | DeclaredTy::RecvRes(payload) => {
                self.intern(&payload);
            }
            DeclaredTy::WaitRes(payloads) => {
                for payload in &payloads {
                    self.intern(payload);
                }
            }
            DeclaredTy::Plain | DeclaredTy::OtherGeneric => {
                if let TypeRef::Generic { name, args } = ty {
                    if name == "WaitArm" && args.len() == 1 {
                        if let Some(payload) = checked_payload(&args[0], &self.registry.entities) {
                            self.intern(&payload);
                        }
                    }
                }
            }
        }
    }
    fn collect_payloads(&mut self, file: &sal_syntax::SalFile) {
        let mut handle_tys: HashMap<String, HashMap<String, Payload>> = HashMap::new();
        for item in &file.items {
            if let Item::Operation(operation) = item {
                let table = self
                    .registry
                    .param_payload
                    .get(&operation.name)
                    .cloned()
                    .unwrap_or_default();
                let mut params: Vec<(String, Option<Payload>)> = table.into_iter().collect();
                params.sort_by(|left, right| left.0.cmp(&right.0));
                let mut decls: HashMap<String, Payload> = HashMap::new();
                for (param, slot) in &params {
                    if let Some(payload) = slot {
                        decls.insert(param.clone(), payload.clone());
                        self.intern(payload);
                    }
                }
                if let Some(declared) = self.registry.operations.get(&operation.name) {
                    for param in &declared.accepts {
                        self.intern_result_payloads(&param.ty);
                    }
                    if let Some(returns) = &declared.returns {
                        self.intern_result_payloads(returns);
                    }
                } else if let Some(returns) = &operation.returns {
                    self.intern_result_payloads(returns);
                }
                handle_tys.insert(operation.name.clone(), decls);
            }
        }
        for item in &file.items {
            let Item::Operation(operation) = item else {
                continue;
            };
            if operation.body.is_empty() {
                continue;
            }
            let decls = handle_tys.get(&operation.name).cloned().unwrap_or_default();
            let mut locals: HashMap<String, Payload> = decls;
            self.collect_block_payloads(&operation.body, &mut locals);
        }
    }
    fn collect_block_payloads(&mut self, body: &[Stmt], locals: &mut HashMap<String, Payload>) {
        for stmt in body {
            match stmt {
                Stmt::Let { name, expr, .. } => {
                    let payload = self.shape_expr_payload(expr, locals);
                    self.collect_expr_payloads(expr, locals);
                    if let Some(payload) = payload {
                        locals.insert(name.clone(), payload.clone());
                        self.intern(&payload);
                    } else {
                        locals.remove(name);
                    }
                }
                Stmt::Assign { expr, .. } | Stmt::Return(expr) | Stmt::ExprStmt(expr) => {
                    self.collect_expr_payloads(expr, locals);
                }
                Stmt::If { cond, then, else_ } => {
                    self.collect_expr_payloads(cond, locals);
                    let mut then_locals = locals.clone();
                    self.collect_block_payloads(then, &mut then_locals);
                    let mut else_locals = locals.clone();
                    self.collect_block_payloads(else_, &mut else_locals);
                }
                Stmt::While { cond, body } => {
                    self.collect_expr_payloads(cond, locals);
                    let mut inner = locals.clone();
                    self.collect_block_payloads(body, &mut inner);
                }
                Stmt::For { var, iter, body } => {
                    self.collect_expr_payloads(iter, locals);
                    let mut inner = locals.clone();
                    inner.remove(var);
                    self.collect_block_payloads(body, &mut inner);
                }
                Stmt::Unsafe { body } => {
                    self.collect_block_payloads(body, locals);
                }
                Stmt::Break | Stmt::Continue => {}
            }
        }
    }
    fn collect_expr_payloads(&mut self, expr: &Expr, locals: &HashMap<String, Payload>) {
        self.intern_expr_payloads(expr, locals);
    }
    fn intern_expr_payloads(&mut self, expr: &Expr, locals: &HashMap<String, Payload>) {
        let mut queue: Vec<&Expr> = vec![expr];
        while let Some(expr) = queue.pop() {
            match expr {
                Expr::Call { name, args } if name == "send" && args.len() == 2 => {
                    if let Expr::Var(ch) = &args[0] {
                        if let Some(payload) = locals.get(ch).cloned() {
                            self.intern(&payload);
                        }
                    }
                    queue.extend(args.iter());
                }
                Expr::Call { name, args } if name == "receive" && args.len() == 1 => {
                    if let Expr::Var(ch) = &args[0] {
                        if let Some(payload) = locals.get(ch).cloned() {
                            self.intern(&payload);
                        }
                    }
                    queue.extend(args.iter());
                }
                Expr::Call { name, args } if name == "wait_for" => {
                    for arg in args {
                        if let Expr::Call {
                            name: arm,
                            args: arm_args,
                        } = arg
                        {
                            if arm == "receive" && arm_args.len() == 1 {
                                if let Expr::Var(ch) = &arm_args[0] {
                                    if let Some(payload) = locals.get(ch).cloned() {
                                        self.intern(&payload);
                                    }
                                }
                            } else if arm == "send" && arm_args.len() == 2 {
                                if let Expr::Var(ch) = &arm_args[0] {
                                    if let Some(payload) = locals.get(ch).cloned() {
                                        self.intern(&payload);
                                    }
                                }
                                queue.push(&arm_args[1]);
                            }
                        } else {
                            queue.push(arg);
                        }
                    }
                }
                Expr::Call { name, args } => {
                    if let Some(operation) = self.registry.operations.get(name) {
                        for param in &operation.accepts {
                            self.intern_result_payloads(&param.ty);
                        }
                        if let Some(returns) = &operation.returns {
                            self.intern_result_payloads(returns);
                        }
                    }
                    queue.extend(args.iter());
                }
                Expr::Field { base, .. } | Expr::Not(base) => queue.push(base),
                Expr::Index { base, index } => {
                    queue.push(base);
                    queue.push(index);
                }
                Expr::BinOp { left, right, .. } => {
                    queue.push(left);
                    queue.push(right);
                }
                Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
            }
        }
    }
}

impl<'a> Rewriter<'a> {
    fn emit_record(
        &self,
        out: &mut Vec<Item>,
        name: String,
        fields: Vec<(String, TypeRef)>,
        span: &Span,
    ) {
        out.push(Item::Entity(EntityDecl {
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
    fn emit_op(
        &self,
        out: &mut Vec<Item>,
        name: String,
        params: Vec<(String, TypeRef)>,
        returns: Option<TypeRef>,
        span: &Span,
        body: Vec<Stmt>,
    ) {
        out.push(Item::Operation(OperationDecl {
            name,
            span: span.clone(),
            accepts: params
                .into_iter()
                .map(|(name, ty)| sal_syntax::ParamDecl { name, ty })
                .collect(),
            returns,
            effects: vec!["SystemCall".into()],
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
    // These runtime entries accept erased addresses, so they must remain unsafe
    // to call directly. Only checked, affine source operations reach these
    // reserved wrappers; their unsafe blocks do not grant effects to callers.
    fn emit_handle_ops(&self, out: &mut Vec<Item>, span: &Span) {
        for (name, runtime, returns) in [
            ("SalConcChannelClone", "SalChannelClone", Some("usize")),
            ("SalConcChannelDrop", "SalChannelDrop", None),
            ("SalConcChannelClose", "SalChannelClose", Some("bool")),
            ("SalConcThreadJoin", "SalThreadJoin", Some("i64")),
        ] {
            let call = Expr::Call {
                name: runtime.into(),
                args: vec![Expr::Var("handle".into())],
            };
            let body = match returns {
                Some(_) => vec![Stmt::Return(call)],
                None => vec![Stmt::ExprStmt(call)],
            };
            self.emit_op(
                out,
                name.into(),
                vec![("handle".into(), TypeRef::Named("usize".into()))],
                returns.map(|name| TypeRef::Named(name.into())),
                span,
                body,
            );
        }
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
    fn emit_payload_items(&self, out: &mut Vec<Item>, span: &Span) {
        for def in &self.payloads {
            if matches!(def.payload, Payload::Channel(_)) {
                continue;
            }
            let payload_ty = def.payload.type_ref();
            self.emit_record(
                out,
                box_name(&def.tag),
                vec![("value".into(), payload_ty.clone())],
                span,
            );
            self.emit_record(
                out,
                send_name(&def.tag),
                vec![
                    ("sent".into(), TypeRef::Named("bool".into())),
                    ("value".into(), payload_ty.clone()),
                ],
                span,
            );
            self.emit_record(
                out,
                recv_name(&def.tag),
                vec![
                    ("open".into(), TypeRef::Named("bool".into())),
                    ("value".into(), payload_ty.clone()),
                ],
                span,
            );
            self.emit_record(
                out,
                arm_name(&def.tag),
                vec![
                    ("selected".into(), TypeRef::Named("bool".into())),
                    ("open".into(), TypeRef::Named("bool".into())),
                    ("value".into(), payload_ty.clone()),
                ],
                span,
            );
            self.emit_op(
                out,
                zero_name(&def.tag),
                vec![],
                Some(payload_ty.clone()),
                span,
                self.zero_body(&payload_ty),
            );
            // Channel constructor: capacity validation + SalChannelNew + exit(231) on null.
            self.emit_op(
                out,
                chan_new_name(&def.tag),
                vec![("capacity".into(), TypeRef::Named("usize".into()))],
                Some(TypeRef::Named("usize".into())),
                span,
                vec![
                    Stmt::Let {
                        name: "width".into(),
                        mutable: false,
                        expr: Expr::Call {
                            name: "size_of".into(),
                            args: vec![Expr::Var(box_name(&def.tag))],
                        },
                    },
                    Stmt::Let {
                        name: "handle".into(),
                        mutable: false,
                        expr: Expr::Call {
                            name: "SalChannelNew".into(),
                            args: vec![Expr::Var("capacity".into()), Expr::Var("width".into())],
                        },
                    },
                    Stmt::If {
                        cond: Expr::BinOp {
                            op: BinOp::Eq,
                            left: Box::new(Expr::Var("handle".into())),
                            right: Box::new(Expr::Call {
                                name: "usize".into(),
                                args: vec![Expr::Int(0)],
                            }),
                        },
                        then: vec![self.exit_group(231)],
                        else_: vec![],
                    },
                    Stmt::Return(Expr::Var("handle".into())),
                ],
            );
            // Blocking send primitive via SalSelect single-node frames.
            self.emit_op(
                out,
                send_op_name(&def.tag),
                vec![
                    ("channel".into(), TypeRef::Named("usize".into())),
                    ("input".into(), payload_ty.clone()),
                ],
                Some(TypeRef::Named(send_name(&def.tag))),
                span,
                self.send_body(&def.tag, span),
            );
            self.emit_op(
                out,
                recv_op_name(&def.tag),
                vec![("channel".into(), TypeRef::Named("usize".into()))],
                Some(TypeRef::Named(recv_name(&def.tag))),
                span,
                self.recv_body(&def.tag, span),
            );
        }
    }
}

impl<'a> Rewriter<'a> {
    fn send_body(&self, tag: &str, span: &Span) -> Vec<Stmt> {
        let box_ty = box_name(tag);
        let send_ty = send_name(tag);
        let _ = span;
        vec![
            Stmt::Let {
                name: "slot".into(),
                mutable: false,
                expr: Expr::Call {
                    name: box_ty.clone(),
                    args: vec![Expr::Var("input".into())],
                },
            },
            Stmt::Let {
                name: "nodes".into(),
                mutable: false,
                expr: Expr::Call {
                    name: nodes_name(1),
                    args: self.node_args(
                        Expr::Var("channel".into()),
                        1,
                        Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("slot".into())],
                        },
                    ),
                },
            },
            Stmt::Let {
                name: "won".into(),
                mutable: false,
                expr: Expr::Call {
                    name: "SalSelect".into(),
                    args: vec![
                        Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("nodes".into())],
                        },
                        Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(1)],
                        },
                        Expr::Int(-1),
                    ],
                },
            },
            Stmt::Let {
                name: "status".into(),
                mutable: false,
                expr: Expr::Call {
                    name: "load64".into(),
                    args: vec![Expr::BinOp {
                        op: BinOp::Add,
                        left: Box::new(Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("nodes".into())],
                        }),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(40)],
                        }),
                    }],
                },
            },
            Stmt::If {
                cond: Expr::BinOp {
                    op: BinOp::And,
                    left: Box::new(Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var("won".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    }),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var("status".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    }),
                },
                then: vec![Stmt::Return(Expr::Call {
                    name: send_ty.clone(),
                    args: vec![Expr::Bool(true), Expr::Var("input".into())],
                })],
                else_: vec![Stmt::Return(Expr::Call {
                    name: send_ty,
                    args: vec![Expr::Bool(false), Expr::Var("input".into())],
                })],
            },
        ]
    }
    fn recv_body(&self, tag: &str, span: &Span) -> Vec<Stmt> {
        let box_ty = box_name(tag);
        let recv_ty = recv_name(tag);
        let _ = span;
        vec![
            Stmt::Let {
                name: "empty".into(),
                mutable: false,
                expr: Expr::Call {
                    name: zero_name(tag),
                    args: vec![],
                },
            },
            Stmt::Let {
                name: "slot".into(),
                mutable: false,
                expr: Expr::Call {
                    name: box_ty.clone(),
                    args: vec![Expr::Var("empty".into())],
                },
            },
            Stmt::Let {
                name: "nodes".into(),
                mutable: false,
                expr: Expr::Call {
                    name: nodes_name(1),
                    args: self.node_args(
                        Expr::Var("channel".into()),
                        0,
                        Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("slot".into())],
                        },
                    ),
                },
            },
            Stmt::Let {
                name: "won".into(),
                mutable: false,
                expr: Expr::Call {
                    name: "SalSelect".into(),
                    args: vec![
                        Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("nodes".into())],
                        },
                        Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(1)],
                        },
                        Expr::Int(-1),
                    ],
                },
            },
            Stmt::Let {
                name: "status".into(),
                mutable: false,
                expr: Expr::Call {
                    name: "load64".into(),
                    args: vec![Expr::BinOp {
                        op: BinOp::Add,
                        left: Box::new(Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var("nodes".into())],
                        }),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(40)],
                        }),
                    }],
                },
            },
            Stmt::If {
                cond: Expr::BinOp {
                    op: BinOp::And,
                    left: Box::new(Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var("won".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    }),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var("status".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    }),
                },
                then: vec![Stmt::Return(Expr::Call {
                    name: recv_ty.clone(),
                    args: vec![
                        Expr::Bool(true),
                        Expr::Field {
                            base: Box::new(Expr::Var("slot".into())),
                            field: "value".into(),
                        },
                    ],
                })],
                else_: vec![Stmt::Return(Expr::Call {
                    name: recv_ty,
                    args: vec![Expr::Bool(false), Expr::Var("empty".into())],
                })],
            },
        ]
    }
    fn zero_expr(&self, payload_ty: &TypeRef) -> Expr {
        match payload_ty {
            TypeRef::Named(name) if name == "bool" => Expr::Bool(false),
            TypeRef::Named(name) if is_integer_name(name) => Expr::Int(0),
            TypeRef::Named(name) => {
                let fields = self
                    .registry
                    .entities
                    .get(name.as_str())
                    .cloned()
                    .unwrap_or_default();
                let args: Vec<Expr> = fields
                    .iter()
                    .map(|(_, field_ty)| {
                        let nested = match field_ty {
                            Payload::Scalar(scalar) => TypeRef::Named(scalar.clone()),
                            Payload::Record(record) => TypeRef::Named(record.clone()),
                            Payload::Channel(_) => TypeRef::Named("usize".into()),
                        };
                        self.zero_expr(&nested)
                    })
                    .collect();
                Expr::Call {
                    name: name.clone(),
                    args,
                }
            }
            TypeRef::Generic { .. } => Expr::Int(0),
        }
    }
    fn zero_body(&self, payload_ty: &TypeRef) -> Vec<Stmt> {
        match payload_ty {
            TypeRef::Named(name) if name == "bool" => vec![Stmt::Return(Expr::Bool(false))],
            TypeRef::Named(name) if is_integer_name(name) => vec![Stmt::Return(Expr::Int(0))],
            TypeRef::Named(_) => {
                vec![Stmt::Return(self.zero_expr(payload_ty))]
            }
            TypeRef::Generic { .. } => vec![Stmt::Return(Expr::Int(0))],
        }
    }
}

impl<'a> Rewriter<'a> {
    fn emit_nodes(&self, out: &mut Vec<Item>, span: &Span, counts: &BTreeSet<usize>) {
        for count in counts {
            let mut fields: Vec<(String, TypeRef)> = Vec::with_capacity(8 * count);
            for index in 0..*count {
                fields.push((format!("n{index}channel"), TypeRef::Named("usize".into())));
                fields.push((format!("n{index}direction"), TypeRef::Named("usize".into())));
                fields.push((format!("n{index}payload"), TypeRef::Named("usize".into())));
                fields.push((
                    format!("n{index}completion"),
                    TypeRef::Named("usize".into()),
                ));
                fields.push((format!("n{index}next"), TypeRef::Named("usize".into())));
                fields.push((format!("n{index}status"), TypeRef::Named("usize".into())));
                fields.push((format!("n{index}arm"), TypeRef::Named("usize".into())));
                fields.push((format!("n{index}linked"), TypeRef::Named("usize".into())));
            }
            self.emit_record(out, nodes_name(*count), fields, span);
        }
    }
    fn node_args(&self, channel: Expr, direction: i64, payload_addr: Expr) -> Vec<Expr> {
        vec![
            channel,
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(direction)],
            },
            payload_addr,
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(0)],
            },
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(0)],
            },
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(0)],
            },
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(0)],
            },
            Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(0)],
            },
        ]
    }
    fn wait_shapes(&mut self, file: &sal_syntax::SalFile) -> (Vec<WaitShape>, BTreeSet<usize>) {
        let mut shapes: Vec<(Vec<(ArmDir, Payload)>, bool)> = Vec::new();
        let mut counts: BTreeSet<usize> = BTreeSet::new();
        let mut handle_tys: HashMap<String, HashMap<String, Payload>> = HashMap::new();
        for item in &file.items {
            if let Item::Operation(operation) = item {
                let table = self
                    .registry
                    .param_payload
                    .get(&operation.name)
                    .cloned()
                    .unwrap_or_default();
                let mut params: Vec<(String, Option<Payload>)> = table.into_iter().collect();
                params.sort_by(|left, right| left.0.cmp(&right.0));
                let mut decls: HashMap<String, Payload> = HashMap::new();
                for (param, slot) in &params {
                    if let Some(payload) = slot {
                        decls.insert(param.clone(), payload.clone());
                    }
                }
                handle_tys.insert(operation.name.clone(), decls);
            }
        }
        for item in &file.items {
            let Item::Operation(operation) = item else {
                continue;
            };
            if operation.body.is_empty() {
                continue;
            }
            let decls = handle_tys.get(&operation.name).cloned().unwrap_or_default();
            let mut locals = decls;
            self.walk_stmts_shapes(&operation.body, &mut locals, &mut shapes, &mut counts);
        }
        (shapes, counts)
    }
    fn walk_stmts_shapes(
        &mut self,
        body: &[Stmt],
        locals: &mut HashMap<String, Payload>,
        shapes: &mut Vec<(Vec<(ArmDir, Payload)>, bool)>,
        counts: &mut BTreeSet<usize>,
    ) {
        for stmt in body {
            match stmt {
                Stmt::Let { name, expr, .. } => {
                    let payload = self.shape_expr_payload(expr, locals);
                    self.walk_expr_shapes(expr, locals, shapes, counts);
                    if let Some(payload) = payload {
                        locals.insert(name.clone(), payload);
                    } else {
                        locals.remove(name);
                    }
                }
                Stmt::Assign { expr, .. } | Stmt::Return(expr) | Stmt::ExprStmt(expr) => {
                    self.walk_expr_shapes(expr, locals, shapes, counts);
                }
                Stmt::If { cond, then, else_ } => {
                    self.walk_expr_shapes(cond, locals, shapes, counts);
                    let mut then_locals = locals.clone();
                    self.walk_stmts_shapes(then, &mut then_locals, shapes, counts);
                    let mut else_locals = locals.clone();
                    self.walk_stmts_shapes(else_, &mut else_locals, shapes, counts);
                }
                Stmt::While { cond, body } => {
                    self.walk_expr_shapes(cond, locals, shapes, counts);
                    let mut inner = locals.clone();
                    self.walk_stmts_shapes(body, &mut inner, shapes, counts);
                }
                Stmt::For { var, iter, body } => {
                    self.walk_expr_shapes(iter, locals, shapes, counts);
                    let mut inner = locals.clone();
                    inner.remove(var);
                    self.walk_stmts_shapes(body, &mut inner, shapes, counts);
                }
                Stmt::Unsafe { body } => {
                    self.walk_stmts_shapes(body, locals, shapes, counts);
                }
                Stmt::Break | Stmt::Continue => {}
            }
        }
    }
    fn shape_expr_payload(
        &self,
        expr: &Expr,
        locals: &HashMap<String, Payload>,
    ) -> Option<Payload> {
        match expr {
            Expr::Call { name, args } if name == "channel_clone" && args.len() == 1 => {
                if let Expr::Var(ch) = &args[0] {
                    return locals.get(ch).cloned();
                }
                None
            }
            Expr::Call { name, args } if name == "channel" && args.len() == 2 => {
                if let Expr::Var(type_name) = &args[0] {
                    return checked_payload(
                        &TypeRef::Named(type_name.clone()),
                        &self.registry.entities,
                    );
                }
                None
            }
            Expr::Call { name, args } => {
                if let Some(operation) = self.registry.operations.get(name) {
                    if let Some(returns) = &operation.returns {
                        if let DeclaredTy::Chan(payload) =
                            classify_typed(returns, &self.registry.entities)
                        {
                            let _ = args;
                            return Some(payload);
                        }
                    }
                }
                None
            }
            Expr::Var(alias) => locals.get(alias).cloned(),
            _ => None,
        }
    }
    fn walk_expr_shapes(
        &mut self,
        expr: &Expr,
        locals: &HashMap<String, Payload>,
        shapes: &mut Vec<(Vec<(ArmDir, Payload)>, bool)>,
        counts: &mut BTreeSet<usize>,
    ) {
        let mut queue: Vec<&Expr> = vec![expr];
        while let Some(expr) = queue.pop() {
            match expr {
                Expr::Call { name, args } if name == "wait_for" => {
                    let mut arms: Vec<(ArmDir, Payload)> = Vec::new();
                    let mut arm_end = args.len();
                    if let Some(Expr::Call { name: last, .. }) = args.last() {
                        if last == "timeout" || last == "otherwise" {
                            arm_end -= 1;
                        }
                    }
                    let has_fallback = arm_end < args.len();
                    for arg in &args[..arm_end] {
                        if let Expr::Call {
                            name: arm,
                            args: arm_args,
                        } = arg
                        {
                            if arm == "receive" && arm_args.len() == 1 {
                                if let Expr::Var(ch) = &arm_args[0] {
                                    if let Some(payload) = locals.get(ch).cloned() {
                                        arms.push((ArmDir::Recv, payload));
                                    }
                                }
                            } else if arm == "send" && arm_args.len() == 2 {
                                if let Expr::Var(ch) = &arm_args[0] {
                                    if let Some(payload) = locals.get(ch).cloned() {
                                        arms.push((ArmDir::Send, payload));
                                    }
                                }
                            }
                        }
                    }
                    if !arms.is_empty() {
                        counts.insert(arms.len());
                        for (_, payload) in &arms {
                            self.intern(payload);
                        }
                        let key = (arms, has_fallback);
                        if !shapes.contains(&key) {
                            shapes.push(key);
                        }
                    }
                    queue.extend(args.iter());
                }
                Expr::Call { name, args } => {
                    if let Some(operation) = self.registry.operations.get(name) {
                        for param in &operation.accepts {
                            self.intern_result_payloads(&param.ty);
                        }
                        if let Some(returns) = &operation.returns {
                            self.intern_result_payloads(returns);
                        }
                    }
                    queue.extend(args.iter());
                }
                Expr::Field { base, .. } | Expr::Not(base) => queue.push(base),
                Expr::Index { base, index } => {
                    queue.push(base);
                    queue.push(index);
                }
                Expr::BinOp { left, right, .. } => {
                    queue.push(left);
                    queue.push(right);
                }
                Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
            }
        }
    }
}

impl<'a> Rewriter<'a> {
    fn emit_wait_items(
        &self,
        out: &mut Vec<Item>,
        span: &Span,
        shapes: &[(Vec<(ArmDir, Payload)>, bool)],
    ) {
        let mut emitted = BTreeSet::new();
        for (arms, _) in shapes {
            self.emit_wait_result(
                out,
                span,
                arms.iter().map(|(_, payload)| payload),
                &mut emitted,
            );
        }
        for operation in self.registry.operations.values() {
            for ty in operation
                .accepts
                .iter()
                .map(|param| &param.ty)
                .chain(operation.returns.iter())
            {
                if let DeclaredTy::WaitRes(payloads) = classify_typed(ty, &self.registry.entities) {
                    self.emit_wait_result(out, span, payloads.iter(), &mut emitted);
                }
            }
        }
    }
    fn emit_wait_result<'p>(
        &self,
        out: &mut Vec<Item>,
        span: &Span,
        payloads: impl Iterator<Item = &'p Payload>,
        emitted: &mut BTreeSet<String>,
    ) {
        let tags: Vec<_> = payloads
            .map(|payload| (ArmDir::Recv, self.tag_of(payload)))
            .collect();
        let (_, name) = wait_names(&tags);
        if !emitted.insert(name.clone()) {
            return;
        }
        let mut fields = vec![
            ("index".into(), TypeRef::Named("usize".into())),
            ("status".into(), TypeRef::Named("usize".into())),
        ];
        for (index, (_, tag)) in tags.iter().enumerate() {
            fields.push((format!("arm{index}"), TypeRef::Named(arm_name(tag))));
        }
        self.emit_record(out, name, fields, span);
    }
    fn tag_of(&self, payload: &Payload) -> String {
        payload_tag(&payload.type_ref()).expect("interned payload has a tag")
    }
}

impl<'a> Rewriter<'a> {
    fn wait_op_body(
        &self,
        arms: &[(ArmDir, Payload)],
        has_timeout: bool,
        _span: &Span,
    ) -> Vec<Stmt> {
        let count = arms.len();
        let mut body: Vec<Stmt> = Vec::new();
        for (index, (dir, payload)) in arms.iter().enumerate() {
            let tag = self.tag_of(payload);
            let slot = format!("slot{index}");
            let init = match dir {
                ArmDir::Recv => Expr::Call {
                    name: zero_name(&tag),
                    args: vec![],
                },
                ArmDir::Send => Expr::Var(format!("value{index}")),
            };
            body.push(Stmt::Let {
                name: slot.clone(),
                mutable: false,
                expr: Expr::Call {
                    name: box_name(&tag),
                    args: vec![init],
                },
            });
        }
        let mut node_args: Vec<Expr> = Vec::new();
        for (index, (dir, _)) in arms.iter().enumerate() {
            let direction = match dir {
                ArmDir::Recv => 0,
                ArmDir::Send => 1,
            };
            node_args.extend(self.node_args(
                Expr::Var(format!("channel{index}")),
                direction,
                Expr::Call {
                    name: "address".into(),
                    args: vec![Expr::Var(format!("slot{index}"))],
                },
            ));
        }
        body.push(Stmt::Let {
            name: "nodes".into(),
            mutable: false,
            expr: Expr::Call {
                name: nodes_name(count),
                args: node_args,
            },
        });
        let timeout_expr = if has_timeout {
            Expr::Call {
                name: "isize".into(),
                args: vec![Expr::Var("timeout_value".into())],
            }
        } else {
            Expr::Int(-1)
        };
        body.push(Stmt::Let {
            name: "won".into(),
            mutable: false,
            expr: Expr::Call {
                name: "SalSelect".into(),
                args: vec![
                    Expr::Call {
                        name: "address".into(),
                        args: vec![Expr::Var("nodes".into())],
                    },
                    Expr::Call {
                        name: "usize".into(),
                        args: vec![Expr::Int(count as i64)],
                    },
                    timeout_expr,
                ],
            },
        });
        body.push(Stmt::Let {
            name: "nodes_ptr".into(),
            mutable: false,
            expr: Expr::Call {
                name: "address".into(),
                args: vec![Expr::Var("nodes".into())],
            },
        });
        body.push(self.wait_result_dispatch(arms, has_timeout));
        body
    }
    fn wait_result_dispatch(&self, arms: &[(ArmDir, Payload)], _has_timeout: bool) -> Stmt {
        let count = arms.len();
        // if won == count: fallback record (status 2, all selected false).
        let fallback = self.wait_result_expr(arms, None);
        // else: per-arm selected index dispatch.
        let mut selected: Stmt = Stmt::Return(fallback);
        for index in (0..count).rev() {
            let arm_expr = self.wait_result_expr(arms, Some(index));
            selected = Stmt::If {
                cond: Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(Expr::Var("won".into())),
                    right: Box::new(Expr::Call {
                        name: "usize".into(),
                        args: vec![Expr::Int(index as i64)],
                    }),
                },
                then: vec![Stmt::Return(arm_expr)],
                else_: vec![selected],
            };
        }
        selected
    }
    fn wait_result_expr(&self, arms: &[(ArmDir, Payload)], winner: Option<usize>) -> Expr {
        let tags: Vec<(ArmDir, String)> = arms
            .iter()
            .map(|(dir, payload)| (*dir, self.tag_of(payload)))
            .collect();
        let (_op, res_name) = wait_names(
            &tags
                .iter()
                .map(|(dir, tag)| (*dir, tag.clone()))
                .collect::<Vec<_>>(),
        );
        let mut args: Vec<Expr> = match winner {
            Some(_) => vec![Expr::Var("won".into())],
            None => vec![Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(arms.len() as i64)],
            }],
        };
        match winner {
            None => args.push(Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(2)],
            }),
            Some(index) => {
                // status_addr = nodes_ptr + won*64 + 40; status = load64(...).
                let node_base = Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(Expr::Var("nodes_ptr".into())),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Mul,
                        left: Box::new(Expr::Var("won".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(64)],
                        }),
                    }),
                };
                let status_word = Expr::Call {
                    name: "load64".into(),
                    args: vec![Expr::BinOp {
                        op: BinOp::Add,
                        left: Box::new(node_base),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(40)],
                        }),
                    }],
                };
                let _ = index;
                args.push(status_word);
            }
        }
        for (index, (dir, payload)) in arms.iter().enumerate() {
            let tag = self.tag_of(payload);
            let selected = winner == Some(index);
            let sel_expr = Expr::Bool(selected);
            let open_expr = if !selected {
                Expr::Bool(false)
            } else {
                let node_base = Expr::BinOp {
                    op: BinOp::Add,
                    left: Box::new(Expr::Var("nodes_ptr".into())),
                    right: Box::new(Expr::BinOp {
                        op: BinOp::Mul,
                        left: Box::new(Expr::Var("won".into())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(64)],
                        }),
                    }),
                };
                let status_word = Expr::Call {
                    name: "load64".into(),
                    args: vec![Expr::BinOp {
                        op: BinOp::Add,
                        left: Box::new(node_base),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(40)],
                        }),
                    }],
                };
                Expr::BinOp {
                    op: BinOp::Eq,
                    left: Box::new(status_word),
                    right: Box::new(Expr::Call {
                        name: "usize".into(),
                        args: vec![Expr::Int(0)],
                    }),
                }
            };
            let value_expr = match (dir, selected) {
                (ArmDir::Recv, true) => Expr::Field {
                    base: Box::new(Expr::Var(format!("slot{index}"))),
                    field: "value".into(),
                },
                (ArmDir::Send, _) => Expr::Var(format!("value{index}")),
                (ArmDir::Recv, false) => Expr::Call {
                    name: zero_name(&tag),
                    args: vec![],
                },
            };
            args.push(Expr::Call {
                name: arm_name(&tag),
                args: vec![sel_expr, open_expr, value_expr],
            });
        }
        Expr::Call {
            name: res_name,
            args,
        }
    }
}

impl<'a> Rewriter<'a> {
    fn emit_spawn_items(&mut self, out: &mut Vec<Item>, span: &Span, spawns: &[(String, Payload)]) {
        for (worker, payload) in spawns {
            let tag = self.tag_of(payload);
            let tramp = tramp_name(worker, &tag);
            // Trampoline: Worker wrapper accepting usize context, loads/copies
            // the typed payload then calls Worker; context is a SalAlloc block
            // freed here after the copy. Channel args arrive as the raw
            // pointer stored in the context (ownership transferred).
            let load: Stmt = match payload {
                Payload::Channel(_) => Stmt::Let {
                    name: "arg".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: "load64".into(),
                        args: vec![Expr::Var("context".into())],
                    },
                },
                _ => Stmt::Let {
                    name: "box".into(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_name(&tag),
                        args: vec![Expr::Call {
                            name: zero_name(&tag),
                            args: vec![],
                        }],
                    },
                },
            };
            let mut tramp_body: Vec<Stmt> = Vec::new();
            tramp_body.push(load);
            match payload {
                Payload::Channel(_) => {
                    tramp_body.push(Stmt::ExprStmt(Expr::Call {
                        name: "SalFree".into(),
                        args: vec![
                            Expr::Var("context".into()),
                            Expr::Call {
                                name: "usize".into(),
                                args: vec![Expr::Int(8)],
                            },
                        ],
                    }));
                    tramp_body.push(Stmt::Return(Expr::Call {
                        name: worker.clone(),
                        args: vec![Expr::Var("arg".into())],
                    }));
                }
                _ => {
                    tramp_body.push(Stmt::ExprStmt(Expr::Call {
                        name: "ConcurrencyCopy".into(),
                        args: vec![
                            Expr::Call {
                                name: "address".into(),
                                args: vec![Expr::Var("box".into())],
                            },
                            Expr::Var("context".into()),
                            Expr::Call {
                                name: "size_of".into(),
                                args: vec![Expr::Var(box_name(&tag))],
                            },
                        ],
                    }));
                    tramp_body.push(Stmt::ExprStmt(Expr::Call {
                        name: "SalFree".into(),
                        args: vec![
                            Expr::Var("context".into()),
                            Expr::Call {
                                name: "size_of".into(),
                                args: vec![Expr::Var(box_name(&tag))],
                            },
                        ],
                    }));
                    tramp_body.push(Stmt::Return(Expr::Call {
                        name: worker.clone(),
                        args: vec![Expr::Field {
                            base: Box::new(Expr::Var("box".into())),
                            field: "value".into(),
                        }],
                    }));
                }
            }
            self.emit_op(
                out,
                tramp,
                vec![("context".into(), TypeRef::Named("usize".into()))],
                Some(TypeRef::Named("i64".into())),
                span,
                tramp_body,
            );
            let mut scope = Scope {
                kinds: HashMap::new(),
            };
            if let Payload::Channel(inner) = payload {
                scope.kinds.insert(
                    "input".into(),
                    ValTy::Handle(HandleKind::Channel, (**inner).clone()),
                );
            }
            let (mut body, _) = self.rewrite_let_spawn(
                "thread",
                worker,
                &Expr::Var("input".into()),
                &mut scope,
                span,
            );
            body.push(Stmt::Return(Expr::Var("thread".into())));
            self.emit_op(
                out,
                spawn_name(worker, &tag),
                vec![("input".into(), self.erase_ty(&payload.type_ref()))],
                Some(TypeRef::Named("usize".into())),
                span,
                body,
            );
        }
    }
    fn collect_spawns(&mut self, file: &sal_syntax::SalFile) -> Vec<(String, Payload)> {
        let mut spawns: Vec<(String, Payload)> = Vec::new();
        let mut seen: BTreeSet<(String, String)> = BTreeSet::new();
        for item in &file.items {
            let Item::Operation(operation) = item else {
                continue;
            };
            if operation.body.is_empty() {
                continue;
            }
            let mut stmts: Vec<&Stmt> = operation.body.iter().collect();
            let mut queue: Vec<&Expr> = Vec::new();
            while let Some(stmt) = stmts.pop() {
                match stmt {
                    Stmt::Let { expr, .. }
                    | Stmt::Assign { expr, .. }
                    | Stmt::Return(expr)
                    | Stmt::ExprStmt(expr) => queue.push(expr),
                    Stmt::If { cond, then, else_ } => {
                        queue.push(cond);
                        stmts.extend(then.iter());
                        stmts.extend(else_.iter());
                    }
                    Stmt::While { cond, body } => {
                        queue.push(cond);
                        stmts.extend(body.iter());
                    }
                    Stmt::For { iter, body, .. } => {
                        queue.push(iter);
                        stmts.extend(body.iter());
                    }
                    Stmt::Unsafe { body } => {
                        stmts.extend(body.iter());
                    }
                    Stmt::Break | Stmt::Continue => {}
                }
            }
            while let Some(expr) = queue.pop() {
                match expr {
                    Expr::Call { name, args } if name == "spawn" && args.len() == 2 => {
                        if let Expr::Var(worker) = &args[0] {
                            if let Some((payload, _)) = self.registry.workers.get(worker).cloned() {
                                self.intern(&payload);
                                if seen.insert((worker.clone(), self.tag_of(&payload))) {
                                    spawns.push((worker.clone(), payload));
                                }
                            }
                        }
                        queue.extend(args.iter());
                    }
                    Expr::Call { name: _, args } => queue.extend(args.iter()),
                    Expr::Field { base, .. } | Expr::Not(base) => queue.push(base),
                    Expr::Index { base, index } => {
                        queue.push(base);
                        queue.push(index);
                    }
                    Expr::BinOp { left, right, .. } => {
                        queue.push(left);
                        queue.push(right);
                    }
                    Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {
                    }
                }
            }
        }
        spawns.sort_by_key(|spawn| (spawn.0.clone(), spawn.1.spell()));
        spawns
    }
}

// ---------------------------------------------------------------------------
// Main erase-and-emit: statement/expression rewriter.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct Scope {
    kinds: HashMap<String, ValTy>,
}

impl<'a> Rewriter<'a> {
    fn rewrite(&mut self, file: &sal_syntax::SalFile) -> sal_syntax::SalFile {
        let span = file
            .items
            .first()
            .map(|item| match item {
                Item::Application { span, .. } => span.clone(),
                Item::Use { span, .. } => span.clone(),
                Item::Entity(value) => value.span.clone(),
                Item::Enum(value) => value.span.clone(),
                Item::Layer(value) => value.span.clone(),
                Item::Service(value) => value.span.clone(),
                Item::Operation(value) => value.span.clone(),
                Item::Module(value) => value.span.clone(),
                Item::Server(value) => value.span.clone(),
                Item::Route(value) => value.span.clone(),
            })
            .unwrap_or(sal_syntax::Span::single(1, 1));
        self.collect_payloads(file);
        let (shapes, counts) = self.wait_shapes(file);
        let spawns = self.collect_spawns(file);
        let mut out: Vec<Item> = Vec::new();
        self.emit_handle_ops(&mut out, &span);
        // Emit generated records/constructors first (deterministic tag order).
        self.payloads
            .sort_by(|left, right| left.tag.cmp(&right.tag));
        self.emit_payload_items(&mut out, &span);
        // Single-node frames back send/receive.
        let mut counts = counts;
        if !self.payloads.is_empty() {
            counts.insert(1);
        }
        self.emit_nodes(&mut out, &span, &counts);
        self.emit_wait_items(&mut out, &span, &shapes);
        self.emit_spawn_items(&mut out, &span, &spawns);
        // Separate timed wrappers retain usize operand context without sentinels.
        let mut emitted_ops: BTreeSet<String> = BTreeSet::new();
        for (arms, has_fallback) in &shapes {
            let tags: Vec<(ArmDir, String)> = arms
                .iter()
                .map(|(dir, payload)| (*dir, self.tag_of(payload)))
                .collect();
            let (mut op_name, res_name) = wait_names(&tags);
            op_name.push_str(if *has_fallback { "_Timed" } else { "_Blocking" });
            if !emitted_ops.insert(op_name.clone()) {
                continue;
            }
            let mut params: Vec<(String, TypeRef)> = Vec::new();
            for (index, (dir, payload)) in arms.iter().enumerate() {
                params.push((format!("channel{index}"), TypeRef::Named("usize".into())));
                if *dir == ArmDir::Send {
                    params.push((format!("value{index}"), payload.type_ref()));
                }
            }
            if *has_fallback {
                params.push(("timeout_value".into(), TypeRef::Named("usize".into())));
            }
            let returns = TypeRef::Named(res_name);
            let body = self.wait_op_body(arms, *has_fallback, &span);
            self.emit_op(&mut out, op_name, params, Some(returns), &span, body);
        }
        for item in &file.items {
            match item {
                Item::Operation(operation) => {
                    let mut rewritten = operation.clone();
                    rewritten.returns = rewritten.returns.as_ref().map(|ty| self.erase_ty(ty));
                    for param in &mut rewritten.accepts {
                        param.ty = self.erase_ty(&param.ty);
                    }
                    let mut scope = Scope {
                        kinds: HashMap::new(),
                    };
                    self.seed_scope(&mut scope, operation);
                    rewritten.body = self.rewrite_block(&operation.body, &mut scope, &span);
                    out.push(Item::Operation(rewritten));
                }
                Item::Entity(_) => {
                    out.push(item.clone());
                }
                _ => out.push(item.clone()),
            }
        }
        sal_syntax::SalFile { items: out }
    }
    fn seed_scope(&self, scope: &mut Scope, operation: &OperationDecl) {
        let table = self
            .registry
            .param_payload
            .get(&operation.name)
            .cloned()
            .unwrap_or_default();
        for param in &operation.accepts {
            if let Some(Some(payload)) = table.get(&param.name) {
                scope.kinds.insert(
                    param.name.clone(),
                    ValTy::Handle(HandleKind::Channel, payload.clone()),
                );
            }
        }
    }
}

impl<'a> Rewriter<'a> {
    fn rewrite_block(&mut self, body: &[Stmt], scope: &mut Scope, span: &Span) -> Vec<Stmt> {
        let mut out: Vec<Stmt> = Vec::with_capacity(body.len());
        for stmt in body {
            match stmt {
                Stmt::Let {
                    name,
                    mutable,
                    expr,
                } => {
                    if let Expr::Call { name: callee, .. } = expr {
                        if callee == "channel" || callee == "wait_for" {
                            let expr_clone = expr.clone();
                            let (pre, ty) =
                                self.rewrite_let_special(name, *mutable, &expr_clone, scope, span);
                            scope.kinds.insert(name.clone(), ty);
                            out.extend(pre);
                            continue;
                        }
                    }
                    let (expr, ty) = self.rewrite_expr(expr, scope, span);
                    scope.kinds.insert(name.clone(), ty);
                    out.push(Stmt::Let {
                        name: name.clone(),
                        mutable: *mutable,
                        expr,
                    });
                }
                Stmt::Assign { name, expr } => {
                    let (expr, _) = self.rewrite_expr(expr, scope, span);
                    out.push(Stmt::Assign {
                        name: name.clone(),
                        expr,
                    });
                }
                Stmt::Return(expr) => {
                    if let Expr::Call { name: callee, .. } = expr {
                        if callee == "channel" || callee == "wait_for" {
                            let tmp = self.fresh("ret");
                            let expr_clone = expr.clone();
                            let (mut pre, _) =
                                self.rewrite_let_special(&tmp, false, &expr_clone, scope, span);
                            let last = pre.pop().expect("special emits binding");
                            let Stmt::Let {
                                name: handle,
                                mutable: _,
                                expr: handle_expr,
                            } = last
                            else {
                                unreachable!("special binding")
                            };
                            pre.push(Stmt::Let {
                                name: handle.clone(),
                                mutable: false,
                                expr: handle_expr,
                            });
                            out.extend(pre);
                            out.push(Stmt::Return(Expr::Var(handle)));
                            continue;
                        }
                    }
                    let (expr, _) = self.rewrite_expr(expr, scope, span);
                    out.push(Stmt::Return(expr));
                }
                Stmt::ExprStmt(expr) => {
                    let (expr, _) = self.rewrite_expr(expr, scope, span);
                    out.push(Stmt::ExprStmt(expr));
                }
                Stmt::If { cond, then, else_ } => {
                    let (cond, _) = self.rewrite_expr(cond, scope, span);
                    let mut then_scope = scope.clone();
                    let then = self.rewrite_block(then, &mut then_scope, span);
                    let mut else_scope = scope.clone();
                    let else_ = self.rewrite_block(else_, &mut else_scope, span);
                    out.push(Stmt::If { cond, then, else_ });
                }
                Stmt::While { cond, body } => {
                    let (cond, _) = self.rewrite_expr(cond, scope, span);
                    let mut inner = scope.clone();
                    let body = self.rewrite_block(body, &mut inner, span);
                    out.push(Stmt::While { cond, body });
                }
                Stmt::For { var, iter, body } => {
                    let (iter, _) = self.rewrite_expr(iter, scope, span);
                    let mut inner = scope.clone();
                    inner.kinds.insert(var.clone(), ValTy::Value);
                    let body = self.rewrite_block(body, &mut inner, span);
                    out.push(Stmt::For {
                        var: var.clone(),
                        iter,
                        body,
                    });
                }
                Stmt::Unsafe { body } => {
                    let body = self.rewrite_block(body, scope, span);
                    out.push(Stmt::Unsafe { body });
                }
                Stmt::Break | Stmt::Continue => out.push(stmt.clone()),
            }
        }
        out
    }
    fn call_result_ty(&self, name: &str) -> ValTy {
        if let Some(operation) = self.registry.operations.get(name) {
            if let Some(returns) = &operation.returns {
                match classify_typed(returns, &self.registry.entities) {
                    DeclaredTy::Chan(payload) => {
                        return ValTy::Handle(HandleKind::Channel, payload);
                    }
                    DeclaredTy::Thread(_) => {
                        return ValTy::Handle(HandleKind::Thread, Payload::Scalar("i64".into()));
                    }
                    _ => {}
                }
            }
        }
        ValTy::Value
    }
    fn handle_payload(&self, scope: &Scope, name: &str) -> Option<Payload> {
        match scope.kinds.get(name) {
            Some(ValTy::Handle(HandleKind::Channel, payload)) => Some(payload.clone()),
            _ => None,
        }
    }
    fn rewrite_expr(&mut self, expr: &Expr, scope: &mut Scope, span: &Span) -> (Expr, ValTy) {
        match expr {
            Expr::Call { name, args } if is_canonical_call(name) => {
                self.rewrite_canonical(name, args, scope, span)
            }
            Expr::Call { name, args } => {
                let mut rewritten: Vec<Expr> = Vec::with_capacity(args.len());
                for arg in args {
                    let (expr, _) = self.rewrite_expr(arg, scope, span);
                    rewritten.push(expr);
                }
                let ty = self.call_result_ty(name);
                (
                    Expr::Call {
                        name: name.clone(),
                        args: rewritten,
                    },
                    ty,
                )
            }
            Expr::Field { base, field } => {
                let (base, _) = self.rewrite_expr(base, scope, span);
                (
                    Expr::Field {
                        base: Box::new(base),
                        field: field.clone(),
                    },
                    ValTy::Value,
                )
            }
            Expr::Index { base, index } => {
                let (base, _) = self.rewrite_expr(base, scope, span);
                let (index, _) = self.rewrite_expr(index, scope, span);
                (
                    Expr::Index {
                        base: Box::new(base),
                        index: Box::new(index),
                    },
                    ValTy::Value,
                )
            }
            Expr::BinOp { op, left, right } => {
                let (left, _) = self.rewrite_expr(left, scope, span);
                let (right, _) = self.rewrite_expr(right, scope, span);
                (
                    Expr::BinOp {
                        op: *op,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    ValTy::Value,
                )
            }
            Expr::Not(inner) => {
                let (inner, _) = self.rewrite_expr(inner, scope, span);
                (Expr::Not(Box::new(inner)), ValTy::Value)
            }
            Expr::Var(name) => {
                let ty = scope.kinds.get(name).cloned().unwrap_or(ValTy::Value);
                (Expr::Var(name.clone()), ty)
            }
            Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) => {
                (expr.clone(), ValTy::Value)
            }
        }
    }
    fn lower_wait_expr(&mut self, args: &[Expr], scope: &mut Scope, span: &Span) -> (Expr, ValTy) {
        let mut arm_end = args.len();
        let mut timeout: Option<Expr> = None;
        let mut is_otherwise = false;
        if let Some(Expr::Call {
            name: last,
            args: fargs,
        }) = args.last()
        {
            if last == "timeout" && fargs.len() == 1 {
                let (rewritten, _) = self.rewrite_expr(&fargs[0], scope, span);
                timeout = Some(rewritten);
                arm_end -= 1;
            } else if last == "otherwise" {
                is_otherwise = true;
                arm_end -= 1;
            }
        }
        let mut arms: Vec<(ArmDir, Payload)> = Vec::new();
        for arg in &args[..arm_end] {
            if let Some(arm) = self.wait_arm_payload(arg, scope) {
                arms.push(arm);
            } else {
                unreachable!("checked wait arm");
            }
        }
        let tags: Vec<(ArmDir, String)> = arms
            .iter()
            .map(|(dir, payload)| (*dir, self.tag_of(payload)))
            .collect();
        let has_fallback = is_otherwise || timeout.is_some();
        let (mut op_name, _res) = wait_names(&tags);
        op_name.push_str(if has_fallback { "_Timed" } else { "_Blocking" });
        let mut call_args: Vec<Expr> = Vec::new();
        for (index, arg) in args[..arm_end].iter().enumerate() {
            if let Expr::Call {
                name: _,
                args: arm_args,
            } = arg
            {
                let (ch_expr, _) = self.rewrite_expr(&arm_args[0], scope, span);
                call_args.push(ch_expr);
                if arms[index].0 == ArmDir::Send {
                    let (val_expr, _) = self.rewrite_expr(&arm_args[1], scope, span);
                    call_args.push(val_expr);
                }
            }
        }
        if is_otherwise {
            call_args.push(Expr::Int(0));
        } else if let Some(timeout) = timeout {
            call_args.push(timeout);
        }
        (
            Expr::Call {
                name: op_name,
                args: call_args,
            },
            ValTy::Value,
        )
    }
    fn wait_arm_payload(&self, expr: &Expr, scope: &Scope) -> Option<(ArmDir, Payload)> {
        if let Expr::Call {
            name: arm,
            args: arm_args,
        } = expr
        {
            if arm == "receive" && arm_args.len() == 1 {
                if let Expr::Var(ch) = &arm_args[0] {
                    return self
                        .handle_payload(scope, ch)
                        .map(|payload| (ArmDir::Recv, payload));
                }
            } else if arm == "send" && arm_args.len() == 2 {
                if let Expr::Var(ch) = &arm_args[0] {
                    return self
                        .handle_payload(scope, ch)
                        .map(|payload| (ArmDir::Send, payload));
                }
            }
        }
        None
    }
}

impl<'a> Rewriter<'a> {
    fn rewrite_canonical(
        &mut self,
        name: &str,
        args: &[Expr],
        scope: &mut Scope,
        span: &Span,
    ) -> (Expr, ValTy) {
        let _ = span;
        match name {
            "channel" => {
                let payload = match &args[0] {
                    Expr::Var(type_name) => {
                        checked_payload(&TypeRef::Named(type_name.clone()), &self.registry.entities)
                            .expect("checked payload")
                    }
                    _ => unreachable!("checked channel form"),
                };
                let tag = self.tag_of(&payload);
                let (cap_expr, _) = self.rewrite_expr(&args[1], scope, span);
                let call = Expr::Call {
                    name: chan_new_name(&tag),
                    args: vec![cap_expr],
                };
                (call, ValTy::Handle(HandleKind::Channel, payload))
            }
            "channel_clone" => {
                let (ch, _) = self.rewrite_expr(&args[0], scope, span);
                let payload = match &args[0] {
                    Expr::Var(var) => self.handle_payload(scope, var).expect("checked handle"),
                    _ => unreachable!("checked clone form"),
                };
                (
                    Expr::Call {
                        name: "SalConcChannelClone".into(),
                        args: vec![ch],
                    },
                    ValTy::Handle(HandleKind::Channel, payload),
                )
            }
            "channel_drop" => {
                let (ch, _) = self.rewrite_expr(&args[0], scope, span);
                (
                    Expr::Call {
                        name: "SalConcChannelDrop".into(),
                        args: vec![ch],
                    },
                    ValTy::Value,
                )
            }
            "close" => {
                let (ch, _) = self.rewrite_expr(&args[0], scope, span);
                (
                    Expr::Call {
                        name: "SalConcChannelClose".into(),
                        args: vec![ch],
                    },
                    ValTy::Value,
                )
            }
            "send" => {
                let payload = match &args[0] {
                    Expr::Var(var) => self.handle_payload(scope, var).expect("checked handle"),
                    _ => unreachable!("checked send form"),
                };
                let tag = self.tag_of(&payload);
                let (ch, _) = self.rewrite_expr(&args[0], scope, span);
                let (value, _) = self.rewrite_expr(&args[1], scope, span);
                (
                    Expr::Call {
                        name: send_op_name(&tag),
                        args: vec![ch, value],
                    },
                    ValTy::Value,
                )
            }
            "receive" => {
                let payload = match &args[0] {
                    Expr::Var(var) => self.handle_payload(scope, var).expect("checked handle"),
                    _ => unreachable!("checked receive form"),
                };
                let tag = self.tag_of(&payload);
                let (ch, _) = self.rewrite_expr(&args[0], scope, span);
                (
                    Expr::Call {
                        name: recv_op_name(&tag),
                        args: vec![ch],
                    },
                    ValTy::Value,
                )
            }
            "spawn" => {
                let Expr::Var(worker) = &args[0] else {
                    unreachable!("checked worker name")
                };
                let (payload, _) = self.registry.workers.get(worker).expect("checked worker");
                let tag = self.tag_of(payload);
                let (value, _) = self.rewrite_expr(&args[1], scope, span);
                (
                    Expr::Call {
                        name: spawn_name(worker, &tag),
                        args: vec![value],
                    },
                    ValTy::Handle(HandleKind::Thread, Payload::Scalar("i64".into())),
                )
            }
            "join" => {
                let (thread, _) = self.rewrite_expr(&args[0], scope, span);
                (
                    Expr::Call {
                        name: "SalConcThreadJoin".into(),
                        args: vec![thread],
                    },
                    ValTy::Value,
                )
            }
            "wait_for" => self.lower_wait_expr(args, scope, span),
            _ => {
                let mut rewritten: Vec<Expr> = Vec::with_capacity(args.len());
                for arg in args {
                    let (expr, _) = self.rewrite_expr(arg, scope, span);
                    rewritten.push(expr);
                }
                (
                    Expr::Call {
                        name: name.into(),
                        args: rewritten,
                    },
                    ValTy::Value,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Statement-level spawn/wait lowering (once-only evaluation + alloc checks).
// ---------------------------------------------------------------------------

impl<'a> Rewriter<'a> {
    fn rewrite_let_spawn(
        &mut self,
        name: &str,
        worker: &str,
        value: &Expr,
        scope: &mut Scope,
        span: &Span,
    ) -> (Vec<Stmt>, ValTy) {
        let (expected, _) = self
            .registry
            .workers
            .get(worker)
            .cloned()
            .expect("checked worker");
        let tag = self.tag_of(&expected);
        let tramp = tramp_name(worker, &tag);
        let mut pre: Vec<Stmt> = Vec::new();
        let ctx_tmp = self.fresh("ctx");
        let box_tmp = self.fresh("box");
        let entry_tmp = self.fresh("entry");
        let handle_tmp = self.fresh("handle");
        match &expected {
            Payload::Channel(_) => {
                let (moved_expr, _) = self.rewrite_expr(value, scope, span);
                pre.push(Stmt::Let {
                    name: ctx_tmp.clone(),
                    mutable: false,
                    expr: Expr::Call {
                        name: "SalAlloc".into(),
                        args: vec![Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(8)],
                        }],
                    },
                });
                pre.push(Stmt::If {
                    cond: Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var(ctx_tmp.clone())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    },
                    then: vec![self.exit_group(231)],
                    else_: vec![],
                });
                pre.push(Stmt::ExprStmt(Expr::Call {
                    name: "store64".into(),
                    args: vec![Expr::Var(ctx_tmp.clone()), moved_expr],
                }));
            }
            _ => {
                let (val_expr, _) = self.rewrite_expr(value, scope, span);
                pre.push(Stmt::Let {
                    name: ctx_tmp.clone(),
                    mutable: false,
                    expr: Expr::Call {
                        name: "SalAlloc".into(),
                        args: vec![Expr::Call {
                            name: "size_of".into(),
                            args: vec![Expr::Var(box_name(&tag))],
                        }],
                    },
                });
                pre.push(Stmt::If {
                    cond: Expr::BinOp {
                        op: BinOp::Eq,
                        left: Box::new(Expr::Var(ctx_tmp.clone())),
                        right: Box::new(Expr::Call {
                            name: "usize".into(),
                            args: vec![Expr::Int(0)],
                        }),
                    },
                    then: vec![self.exit_group(231)],
                    else_: vec![],
                });
                pre.push(Stmt::Let {
                    name: box_tmp.clone(),
                    mutable: false,
                    expr: Expr::Call {
                        name: box_name(&tag),
                        args: vec![val_expr],
                    },
                });
                pre.push(Stmt::ExprStmt(Expr::Call {
                    name: "ConcurrencyCopy".into(),
                    args: vec![
                        Expr::Var(ctx_tmp.clone()),
                        Expr::Call {
                            name: "address".into(),
                            args: vec![Expr::Var(box_tmp)],
                        },
                        Expr::Call {
                            name: "size_of".into(),
                            args: vec![Expr::Var(box_name(&tag))],
                        },
                    ],
                }));
            }
        }
        pre.push(Stmt::Let {
            name: entry_tmp.clone(),
            mutable: false,
            expr: Expr::Call {
                name: "operation_address".into(),
                args: vec![Expr::Var(tramp)],
            },
        });
        pre.push(Stmt::Let {
            name: handle_tmp.clone(),
            mutable: false,
            expr: Expr::Call {
                name: "SalThreadSpawn".into(),
                args: vec![Expr::Var(entry_tmp), Expr::Var(ctx_tmp.clone())],
            },
        });
        // a single word; scalar/record contexts are box-sized.
        let free_size: Expr = match &expected {
            Payload::Channel(_) => Expr::Call {
                name: "usize".into(),
                args: vec![Expr::Int(8)],
            },
            _ => Expr::Call {
                name: "size_of".into(),
                args: vec![Expr::Var(box_name(&tag))],
            },
        };
        pre.push(Stmt::If {
            cond: Expr::BinOp {
                op: BinOp::Eq,
                left: Box::new(Expr::Var(handle_tmp.clone())),
                right: Box::new(Expr::Call {
                    name: "usize".into(),
                    args: vec![Expr::Int(0)],
                }),
            },
            then: vec![
                Stmt::ExprStmt(Expr::Call {
                    name: "SalFree".into(),
                    args: vec![Expr::Var(ctx_tmp), free_size],
                }),
                self.exit_group(231),
            ],
            else_: vec![],
        });
        pre.push(Stmt::Let {
            name: name.into(),
            mutable: false,
            expr: Expr::Var(handle_tmp),
        });
        (
            pre,
            ValTy::Handle(HandleKind::Thread, Payload::Scalar("i64".into())),
        )
    }
}

impl<'a> Rewriter<'a> {
    fn rewrite_let_special(
        &mut self,
        name: &str,
        mutable: bool,
        expr: &Expr,
        scope: &mut Scope,
        span: &Span,
    ) -> (Vec<Stmt>, ValTy) {
        match expr {
            Expr::Call { name: callee, args } if callee == "channel" => {
                let payload = match &args[0] {
                    Expr::Var(type_name) => {
                        checked_payload(&TypeRef::Named(type_name.clone()), &self.registry.entities)
                            .expect("checked payload")
                    }
                    _ => unreachable!("checked channel form"),
                };
                let tag = self.tag_of(&payload);
                let (cap_expr, _) = self.rewrite_expr(&args[1], scope, span);
                let call = Expr::Call {
                    name: chan_new_name(&tag),
                    args: vec![cap_expr],
                };
                (
                    vec![Stmt::Let {
                        name: name.into(),
                        mutable,
                        expr: call,
                    }],
                    ValTy::Handle(HandleKind::Channel, payload),
                )
            }
            Expr::Call { name: callee, args } if callee == "wait_for" => {
                self.rewrite_let_wait(name, mutable, args, scope, span)
            }
            _ => {
                let (expr, ty) = self.rewrite_expr(expr, scope, span);
                (
                    vec![Stmt::Let {
                        name: name.into(),
                        mutable,
                        expr,
                    }],
                    ty,
                )
            }
        }
    }
    fn rewrite_let_wait(
        &mut self,
        name: &str,
        mutable: bool,
        args: &[Expr],
        scope: &mut Scope,
        span: &Span,
    ) -> (Vec<Stmt>, ValTy) {
        let (expr, ty) = self.lower_wait_expr(args, scope, span);
        (
            vec![Stmt::Let {
                name: name.into(),
                mutable,
                expr,
            }],
            ty,
        )
    }
}
