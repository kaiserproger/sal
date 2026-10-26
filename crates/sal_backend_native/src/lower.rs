use std::collections::BTreeMap;
use std::fmt::Write;

use sal_ir::CRecordLayout;
use sal_syntax::{BinOp, Diagnostic, Expr, OperationDecl, Stmt};

use super::{error, Signature, Ty};

mod abi;
mod builtins;
mod concurrency;
mod memory;
mod numeric;
mod numeric_intrinsics;
mod records;

pub(super) use memory::InternalLayout;
pub(super) use memory::{internal_layouts, memory_builtin_name};
const REGS: [&str; 6] = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];
use abi::Place;

/// Check borrowed trees before the semantic pipeline clones or recursively
/// inspects them. Deep invalid reflection operands must fail, not exhaust the
/// host stack. This bound also covers recursive statement lowering.
pub(super) fn preflight(ir: &sal_ir::Ir) -> Result<(), Diagnostic> {
    enum Node<'a> {
        Statement(&'a Stmt),
        Expression(&'a Expr),
    }
    let source_operations = ir.file.items.iter().filter_map(|item| match item {
        sal_syntax::Item::Operation(operation) => Some(operation),
        _ => None,
    });
    let mut operations: Vec<_> = source_operations.chain(ir.operations.values()).collect();
    operations.sort_by(|left, right| {
        (&left.name, left.span.line, left.span.col).cmp(&(
            &right.name,
            right.span.line,
            right.span.col,
        ))
    });
    for operation in operations {
        let mut pending: Vec<_> = operation
            .body
            .iter()
            .map(|statement| (Node::Statement(statement), 0usize))
            .collect();
        while let Some((node, depth)) = pending.pop() {
            if depth >= 256 {
                return Err(error(
                    "N109",
                    "native expression or statement nesting exceeds supported depth",
                    &operation.span,
                ));
            }
            let next = depth + 1;
            match node {
                Node::Statement(statement) => match statement {
                    Stmt::Let { expr, .. }
                    | Stmt::Assign { expr, .. }
                    | Stmt::Return(expr)
                    | Stmt::ExprStmt(expr) => pending.push((Node::Expression(expr), next)),
                    Stmt::If { cond, then, else_ } => {
                        pending.push((Node::Expression(cond), next));
                        pending.extend(
                            then.iter()
                                .chain(else_)
                                .map(|statement| (Node::Statement(statement), next)),
                        );
                    }
                    Stmt::While { cond, body }
                    | Stmt::For {
                        iter: cond, body, ..
                    } => {
                        pending.push((Node::Expression(cond), next));
                        pending.extend(
                            body.iter()
                                .map(|statement| (Node::Statement(statement), next)),
                        );
                    }
                    Stmt::Unsafe { body } => {
                        pending.extend(
                            body.iter()
                                .map(|statement| (Node::Statement(statement), next)),
                        );
                    }
                    Stmt::Break | Stmt::Continue => {}
                },
                Node::Expression(expression) => match expression {
                    Expr::Call { args, .. } => {
                        pending.extend(args.iter().map(|arg| (Node::Expression(arg), next)))
                    }
                    Expr::Field { base, .. } | Expr::Not(base) => {
                        pending.push((Node::Expression(base), next))
                    }
                    Expr::Index { base, index }
                    | Expr::BinOp {
                        left: base,
                        right: index,
                        ..
                    } => {
                        pending.push((Node::Expression(base), next));
                        pending.push((Node::Expression(index), next));
                    }
                    Expr::Lit(_) | Expr::Int(_) | Expr::Bool(_) | Expr::Float(_) | Expr::Var(_) => {
                    }
                },
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct Local {
    ty: Ty,
    slot: usize,
    mutable: bool,
}

struct Function<'a> {
    operation: &'a OperationDecl,
    signatures: &'a BTreeMap<String, Signature>,
    layouts: &'a BTreeMap<String, CRecordLayout>,
    internal: &'a BTreeMap<String, InternalLayout>,
    literals: &'a mut Vec<String>,
    scopes: Vec<BTreeMap<String, Local>>,
    code: String,
    next_slot: usize,
    frame_size: usize,
    label: usize,
    index: usize,
    result: Ty,
    hidden_result: Option<usize>,
    invalid_frame: bool,
    loops: Vec<(String, String)>,
    unsafe_depth: usize,
}

pub(super) fn function(
    operation: &OperationDecl,
    signatures: &BTreeMap<String, Signature>,
    layouts: &BTreeMap<String, CRecordLayout>,
    internal: &BTreeMap<String, InternalLayout>,
    literals: &mut Vec<String>,
) -> Result<String, Diagnostic> {
    let signature = &signatures[&operation.name];
    let mut function = Function {
        operation,
        signatures,
        layouts,
        internal,
        literals,
        scopes: vec![BTreeMap::new()],
        code: String::new(),
        next_slot: 0,
        frame_size: 0,
        label: 0,
        index: signature.index,
        result: signature.result,
        hidden_result: None,
        invalid_frame: false,
        loops: Vec::new(),
        unsafe_depth: 0,
    };
    // No instruction may use an unencodable frame/field displacement.
    if layouts
        .values()
        .any(|layout| layout.size > i32::MAX as usize - 32)
        || internal
            .values()
            .any(|layout| layout.size > i32::MAX as usize - 32)
    {
        return Err(function.error("N109", "C record exceeds native frame addressing limits"));
    }
    let (places, _) = abi::arguments(layouts, internal, &signature.params, signature.result)
        .ok_or_else(|| function.error("N109", "native argument frame exceeds addressing limits"))?;
    // Preserve incoming registers before copies/normalization use scratch
    // registers. The same classifier is used at every call site.
    let mut raw = [0; 6];
    let mut used = [false; 6];
    let hidden_result = abi::memory_result(layouts, internal, signature.result);
    used[0] = hidden_result;
    for place in &places {
        if let Place::Registers { first, words } = *place {
            used[first..first + words].fill(true);
        }
    }
    for (index, reg) in REGS.iter().enumerate().filter(|(index, _)| used[*index]) {
        let slot = function.allocate(Ty::U64);
        let _ = writeln!(function.code, "    movq {reg}, -{slot}(%rbp)");
        raw[index] = slot;
    }
    if hidden_result {
        function.hidden_result = Some(raw[0]);
    }
    for ((parameter, &ty), place) in operation.accepts.iter().zip(&signature.params).zip(places) {
        let slot = match place {
            Place::Registers { first, .. } if !matches!(ty, Ty::Record(_) | Ty::Internal(_)) => {
                raw[first]
            }
            _ => function.allocate(ty),
        };
        let local = Local {
            ty,
            slot,
            mutable: false,
        };
        match place {
            Place::Registers { first, words } if matches!(ty, Ty::Record(_) | Ty::Internal(_)) => {
                for word in 0..words {
                    let _ = writeln!(
                        function.code,
                        "    movq -{}(%rbp), %rax\n    movq %rax, {}(%rbp)",
                        raw[first + word],
                        -(local.slot as i64) + (word * 8) as i64
                    );
                }
            }
            Place::Registers { first, .. } if ty.bits() < 64 => {
                let _ = writeln!(function.code, "    movq -{}(%rbp), %rax", raw[first]);
                function.normalize(ty);
                function.store(local);
            }
            // Raw register spills already are the wide scalar/span locals.
            Place::Registers { .. } => {}
            Place::Stack { offset } if matches!(ty, Ty::Record(_) | Ty::Internal(_)) => {
                let _ = writeln!(function.code, "    leaq {}(%rbp), %rax", offset + 16);
                function.store(local);
            }
            Place::Stack { offset } => {
                let _ = writeln!(function.code, "    movq {}(%rbp), %rax", offset + 16);
                if ty.pair() {
                    let _ = writeln!(function.code, "    movq {}(%rbp), %rdx", offset + 24);
                } else {
                    function.normalize(ty);
                }
                function.store(local);
            }
        }
        if function.scopes[0]
            .insert(parameter.name.clone(), local)
            .is_some()
        {
            return Err(function.error("B104", format!("duplicate parameter `{}`", parameter.name)));
        }
    }
    let returns = function.block(&operation.body, false)?;
    if !returns && function.result != Ty::Void {
        return Err(function.error(
            "B106",
            format!(
                "operation `{}` does not return on all paths",
                operation.name
            ),
        ));
    }
    if function.result == Ty::Void {
        let _ = writeln!(function.code, "    jmp .Lsal_return_{}", signature.index);
    }
    if function.invalid_frame || function.frame_size > i32::MAX as usize - 16 {
        return Err(function.error("N109", "native fixed frame exceeds addressing limits"));
    }
    let index = signature.index;
    let mut output = format!(".p2align 4\n.type .Lsal_fn_{index},@function\n");
    if let Some(symbol) = &operation.c_export {
        let _ = writeln!(
            output,
            ".globl {symbol}\n.type {symbol},@function\n{symbol}:"
        );
    }
    let _ = writeln!(
        output,
        ".Lsal_fn_{index}:\n    pushq %rbp\n    movq %rsp, %rbp"
    );
    let frame_size = function.frame_size.div_ceil(16) * 16;
    if frame_size != 0 {
        let _ = writeln!(output, "    subq ${frame_size}, %rsp");
    }
    output.push_str(&function.code);
    // Only Void may fall through; value-returning paths must return explicitly.
    let _ = writeln!(output, "    ud2\n.Lsal_return_{index}:\n    leave\n    ret\n.Lsal_trap_{index}:\n    ud2\n.size .Lsal_fn_{index}, .-.Lsal_fn_{index}");
    if let Some(symbol) = &operation.c_export {
        let _ = writeln!(output, ".size {symbol}, .-{symbol}");
    }
    Ok(output)
}

impl Function<'_> {
    fn error(&self, code: &'static str, message: impl Into<String>) -> Diagnostic {
        error(code, message, &self.operation.span)
    }

    fn unsafe_context(&self) -> bool {
        self.unsafe_depth > 0
    }

    fn allocate(&mut self, ty: Ty) -> usize {
        let size = abi::bytes(self.layouts, self.internal, ty);
        let Some(end) = self
            .next_slot
            .checked_add(size)
            .filter(|end| *end <= i32::MAX as usize - 16)
        else {
            self.invalid_frame = true;
            return 8;
        };
        let slot = if matches!(ty, Ty::Record(_) | Ty::Internal(_)) {
            end
        } else {
            self.next_slot + 8
        };
        self.next_slot = end;
        self.frame_size = self.frame_size.max(end);
        slot
    }

    fn label(&mut self) -> String {
        let result = format!(".Lsal_branch_{}_{}", self.index, self.label);
        self.label += 1;
        result
    }

    fn lookup(&self, name: &str) -> Option<Local> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn store(&mut self, local: Local) {
        if matches!(local.ty, Ty::Record(_) | Ty::Internal(_)) {
            self.copy_record_to(local.ty, &format!("-{}(%rbp)", local.slot));
            return;
        }
        let _ = writeln!(self.code, "    movq %rax, -{}(%rbp)", local.slot);
        if local.ty.pair() {
            let _ = writeln!(self.code, "    movq %rdx, -{}(%rbp)", local.slot + 8);
        }
    }

    fn load(&mut self, local: Local) {
        if matches!(local.ty, Ty::Record(_) | Ty::Internal(_)) {
            let _ = writeln!(self.code, "    leaq -{}(%rbp), %rax", local.slot);
            return;
        }
        if local.ty == Ty::Borrow {
            // A Borrow is the address of the original owner slot: every use
            // re-aliases the original metadata, never a by-value copy.
            let _ = writeln!(self.code, "    movq -{}(%rbp), %rax", local.slot);
            return;
        }
        let _ = writeln!(self.code, "    movq -{}(%rbp), %rax", local.slot);
        if local.ty.pair() {
            let _ = writeln!(self.code, "    movq -{}(%rbp), %rdx", local.slot + 8);
        }
    }

    fn require(&self, actual: Ty, expected: Ty, context: &'static str) -> Result<(), Diagnostic> {
        if actual == expected {
            Ok(())
        } else {
            Err(self.error("N100", format!("{context}: expected {expected:?}, found {actual:?}; native lowering does not cast values")))
        }
    }

    fn block(&mut self, body: &[Stmt], nested: bool) -> Result<bool, Diagnostic> {
        if nested {
            self.scopes.push(BTreeMap::new());
        }
        let mut returns = false;
        for statement in body {
            let statement_returns = match statement {
                Stmt::Let {
                    name,
                    expr,
                    mutable,
                } => {
                    let ty = self.expression(expr, None)?;
                    if ty == Ty::Void {
                        return Err(self.error("N100", "cannot bind a Void expression"));
                    }
                    let local = Local {
                        ty,
                        slot: self.allocate(ty),
                        mutable: *mutable,
                    };
                    self.store(local);
                    let scope = self.scopes.last_mut().expect("function has a root scope");
                    if scope.insert(name.clone(), local).is_some() {
                        return Err(self.error("B104", format!("duplicate binding `{name}`")));
                    }
                    false
                }
                Stmt::Assign { name, expr } => {
                    let local = self.lookup(name).ok_or_else(|| {
                        self.error("B100", format!("undefined native variable `{name}`"))
                    })?;
                    if !local.mutable {
                        return Err(self.error("B110", format!("binding `{name}` is immutable")));
                    }
                    let ty = self.expression(expr, Some(local.ty))?;
                    self.require(ty, local.ty, "assignment")?;
                    self.store(local);
                    false
                }
                Stmt::Return(expr) => {
                    let ty = self.expression(expr, Some(self.result))?;
                    self.require(ty, self.result, "return")?;
                    if ty == Ty::Bool {
                        self.code.push_str(
                            "    testq %rax, %rax\n    setne %al\n    movzbl %al, %eax\n",
                        );
                    } else if matches!(ty, Ty::Record(_) | Ty::Internal(_)) {
                        self.return_record(ty);
                    }
                    let _ = writeln!(self.code, "    jmp .Lsal_return_{}", self.index);
                    true
                }
                Stmt::If { cond, then, else_ } => {
                    let ty = self.expression(cond, Some(Ty::Bool))?;
                    self.require(ty, Ty::Bool, "if condition")?;
                    let otherwise = self.label();
                    let end = self.label();
                    let _ = writeln!(self.code, "    testq %rax, %rax\n    je {otherwise}");
                    let then_returns = self.block(then, true)?;
                    let _ = writeln!(self.code, "    jmp {end}\n{otherwise}:");
                    let else_returns = self.block(else_, true)?;
                    let _ = writeln!(self.code, "{end}:");
                    then_returns && else_returns
                }
                Stmt::ExprStmt(expr) => {
                    self.expression(expr, None)?;
                    false
                }
                Stmt::Unsafe { body } => {
                    self.unsafe_depth += 1;
                    let returns = self.block(body, true)?;
                    self.unsafe_depth -= 1;
                    returns
                }
                Stmt::While { cond, body } => {
                    let head = self.label();
                    let end = self.label();
                    let _ = writeln!(self.code, "{head}:");
                    let ty = self.expression(cond, Some(Ty::Bool))?;
                    self.require(ty, Ty::Bool, "while condition")?;
                    let _ = writeln!(self.code, "    testq %rax, %rax\n    je {end}");
                    self.loops.push((head.clone(), end.clone()));
                    self.block(body, true)?;
                    self.loops.pop();
                    let _ = writeln!(self.code, "    jmp {head}\n{end}:");
                    // A break-free `while true` never falls through, so it
                    // diverges for return-path analysis (same rule as sal_ir).
                    *cond == Expr::Bool(true) && !breaks_out(body)
                }
                Stmt::Break | Stmt::Continue => {
                    let Some((head, end)) = self.loops.last() else {
                        return Err(
                            self.error("B111", "break and continue require an enclosing loop")
                        );
                    };
                    let target = if matches!(statement, Stmt::Break) {
                        end
                    } else {
                        head
                    };
                    let _ = writeln!(self.code, "    jmp {target}");
                    false
                }
                Stmt::For { .. } => {
                    return Err(self.error("N108", "native for iteration is not implemented"));
                }
            };
            returns |= statement_returns;
        }
        if nested {
            self.scopes.pop();
        }
        Ok(returns)
    }

    // A nonliteral peer supplies the context for integer literals; literals do
    // not silently convert the type of a variable or a function's result.
    fn hint(&self, expression: &Expr) -> Option<Ty> {
        match expression {
            Expr::Lit(_) => Some(Ty::Text),
            Expr::Bool(_) | Expr::Not(_) => Some(Ty::Bool),
            Expr::Int(_) | Expr::Float(_) | Expr::Index { .. } => None,
            Expr::Field { base, field } => {
                let base_ty = self.hint(base)?;
                if let Some(layout) = self.record_layout(base_ty) {
                    if let Some(found) = layout.fields.iter().find(|f| f.name == *field) {
                        return self.resolve(&found.ty);
                    }
                }
                if let Some(layout) = self.internal_layout(base_ty) {
                    if let Some(found) = layout.fields.iter().find(|f| f.name == *field) {
                        return self.resolve(&found.ty);
                    }
                }
                None
            }
            Expr::Var(name) => self.lookup(name).map(|local| local.ty),
            Expr::Call { name, args } if Self::numeric_intrinsic_name(name) => {
                self.numeric_intrinsic_hint(name, args)
            }
            Expr::Call { name, args } if memory_builtin_name(name) => self.memory_hint(name, args),
            Expr::Call { name, .. } if Self::builtin_result(name).is_some() => {
                Self::builtin_result(name)
            }
            Expr::Call { name, .. } if self.layouts.contains_key(name) => self
                .layouts
                .keys()
                .position(|record| record == name)
                .map(Ty::Record),
            Expr::Call { name, .. } if self.internal.contains_key(name) => self
                .internal
                .keys()
                .position(|record| record == name)
                .map(Ty::Internal),
            Expr::Call { name, .. } => self.signatures.get(name).map(|sig| sig.result),
            Expr::BinOp {
                op:
                    BinOp::Eq
                    | BinOp::Ne
                    | BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::And
                    | BinOp::Or,
                ..
            } => Some(Ty::Bool),
            Expr::BinOp { left, right, .. } => self.hint(left).or_else(|| self.hint(right)),
        }
    }

    fn expression(&mut self, expression: &Expr, expected: Option<Ty>) -> Result<Ty, Diagnostic> {
        // Every expression site owns fixed storage until function return.
        // In particular address(record) must not dangle when scalar scratch
        // or a later constructor is evaluated. Loop iterations reuse offsets.
        self.expression_inner(expression, expected)
    }

    fn expression_inner(
        &mut self,
        expression: &Expr,
        expected: Option<Ty>,
    ) -> Result<Ty, Diagnostic> {
        match expression {
            Expr::Lit(text) => {
                let index = self
                    .literals
                    .iter()
                    .position(|literal| literal == text)
                    .unwrap_or_else(|| {
                        self.literals.push(text.clone());
                        self.literals.len() - 1
                    });
                let _ = writeln!(
                    self.code,
                    "    leaq .Lsal_text_{index}(%rip), %rax\n    movq ${}, %rdx",
                    text.len()
                );
                Ok(Ty::Text)
            }
            Expr::Int(value) => {
                let ty = expected.filter(|ty| ty.integer()).unwrap_or(Ty::I64);
                if !ty.fits_literal(*value) {
                    return Err(self.error("N100", "integer literal exceeds native type range"));
                }
                let _ = writeln!(self.code, "    movabsq ${value}, %rax");
                Ok(ty)
            }
            Expr::Bool(value) => {
                let _ = writeln!(self.code, "    movl ${}, %eax", u8::from(*value));
                Ok(Ty::Bool)
            }
            Expr::Var(name) => {
                let local = self.lookup(name).ok_or_else(|| {
                    self.error("B100", format!("undefined native variable `{name}`"))
                })?;
                self.load(local);
                Ok(local.ty)
            }
            Expr::Call { name, args }
                if matches!(name.as_str(), "size_of" | "align_of" | "offset_of") =>
            {
                self.reflection(name, args)
            }
            Expr::Call { name, args } if self.layouts.contains_key(name) => {
                self.construct(name, args)
            }
            Expr::Call { name, args } if self.internal.contains_key(name) => {
                self.construct_internal(name, args)
            }
            Expr::Call { name, args } if Self::numeric_intrinsic_name(name) => {
                self.numeric_intrinsic(name, args, expected)
            }
            Expr::Call { name, args } if memory_builtin_name(name) => {
                self.memory_builtin(name, args)
            }
            Expr::Call { name, args } if Self::builtin_result(name).is_some() => {
                self.builtin(name, args)
            }
            Expr::Call { name, args } => self.call(name, args),
            Expr::BinOp { op, left, right } => self.binary(*op, left, right, expected),
            Expr::Not(value) => {
                let ty = self.expression(value, Some(Ty::Bool))?;
                self.require(ty, Ty::Bool, "boolean negation")?;
                self.code
                    .push_str("    testq %rax, %rax\n    sete %al\n    movzbl %al, %eax\n");
                Ok(Ty::Bool)
            }
            Expr::Field { base, field } => self.field(base, field),
            Expr::Float(_) | Expr::Index { .. } => Err(self.error(
                "N100",
                "native float and index expressions are not implemented",
            )),
        }
    }

    fn call(&mut self, name: &str, args: &[Expr]) -> Result<Ty, Diagnostic> {
        let signatures = self.signatures;
        let signature = signatures.get(name).ok_or_else(|| {
            self.error(
                "N100",
                format!("native call `{name}` has no supported implementation"),
            )
        })?;
        if args.len() != signature.params.len() {
            return Err(self.error("B101", format!("wrong argument count for `{name}`")));
        }
        if signature.params.contains(&Ty::Void) {
            return Err(self.error("N100", "Void cannot be a native call parameter"));
        }
        let mut spills = Vec::with_capacity(args.len());
        for (arg, expected) in args.iter().zip(&signature.params) {
            let ty = self.expression(arg, Some(*expected))?;
            self.require(ty, *expected, "call argument")?;
            let local = Local {
                ty,
                slot: self.allocate(ty),
                mutable: false,
            };
            self.store(local);
            spills.push(local);
        }
        let result_slot = if matches!(signature.result, Ty::Record(_) | Ty::Internal(_)) {
            Some(self.allocate(signature.result))
        } else {
            None
        };
        let (places, stack) = abi::arguments(
            self.layouts,
            self.internal,
            &signature.params,
            signature.result,
        )
        .ok_or_else(|| {
            self.error(
                "N109",
                "native call argument area exceeds addressing limits",
            )
        })?;
        if stack != 0 {
            let _ = writeln!(self.code, "    subq ${stack}, %rsp");
        }
        // All operands were evaluated exactly once, in source order, before
        // changing rsp or populating argument registers.
        for (local, place) in spills.iter().zip(&places) {
            if let Place::Stack { offset } = place {
                self.copy_argument_to_stack(*local, *offset);
            }
        }
        for (local, place) in spills.iter().zip(&places) {
            if let Place::Registers { first, words } = *place {
                if local.ty == Ty::Borrow {
                    // Borrows ride as one address word; the callee slot
                    // aliases the original owner metadata, never a copy.
                    let _ = writeln!(self.code, "    movq -{}(%rbp), {}", local.slot, REGS[first]);
                    continue;
                }
                for word in 0..words {
                    let displacement = if matches!(local.ty, Ty::Record(_) | Ty::Internal(_)) {
                        -(local.slot as i64) + (word * 8) as i64
                    } else {
                        -((local.slot + word * 8) as i64)
                    };
                    let _ = writeln!(
                        self.code,
                        "    movq {displacement}(%rbp), {}",
                        REGS[first + word]
                    );
                }
            }
        }
        if abi::memory_result(self.layouts, self.internal, signature.result) {
            let _ = writeln!(
                self.code,
                "    leaq -{}(%rbp), %rdi",
                result_slot.expect("record result")
            );
        }
        if let Some(symbol) = &signature.foreign {
            let _ = writeln!(self.code, "    call {symbol}");
        } else {
            let _ = writeln!(self.code, "    call .Lsal_fn_{}", signature.index);
        }
        if stack != 0 {
            let _ = writeln!(self.code, "    addq ${stack}, %rsp");
        }
        if let Some(slot) = result_slot {
            if !abi::memory_result(self.layouts, self.internal, signature.result) {
                let _ = writeln!(self.code, "    movq %rax, -{slot}(%rbp)");
                let second = self
                    .record_layout(signature.result)
                    .map(|layout| layout.size)
                    .or_else(|| {
                        self.internal_layout(signature.result)
                            .map(|layout| layout.size)
                    })
                    .unwrap_or(8);
                if second > 8 || signature.result.pair() {
                    let _ = writeln!(self.code, "    movq %rdx, {}(%rbp)", -(slot as i64) + 8);
                }
            }
            let _ = writeln!(self.code, "    leaq -{slot}(%rbp), %rax");
        } else if !signature.result.pair() {
            self.normalize(signature.result);
        }
        Ok(signature.result)
    }

    fn text_equal(&mut self, saved: Local) {
        let mismatch = self.label();
        let equal = self.label();
        let loop_ = self.label();
        let done = self.label();
        let _ = writeln!(self.code, "    cmpq -{}(%rbp), %rdx\n    jne {mismatch}\n    testq %rdx, %rdx\n    je {equal}\n    movq -{}(%rbp), %r8\n    xorq %rcx, %rcx\n{loop_}:\n    movzbl (%r8,%rcx), %r9d\n    cmpb (%rax,%rcx), %r9b\n    jne {mismatch}\n    incq %rcx\n    cmpq %rdx, %rcx\n    jne {loop_}\n{equal}:\n    movl $1, %eax\n    jmp {done}\n{mismatch}:\n    xorl %eax, %eax\n{done}:", saved.slot + 8, saved.slot);
    }
}

/// Whether a `break` in `body` exits the loop that directly owns `body`;
/// breaks inside nested loops target those loops instead.
fn breaks_out(body: &[Stmt]) -> bool {
    body.iter().any(|statement| match statement {
        Stmt::Break => true,
        Stmt::If { then, else_, .. } => breaks_out(then) || breaks_out(else_),
        Stmt::Unsafe { body } => breaks_out(body),
        _ => false,
    })
}
