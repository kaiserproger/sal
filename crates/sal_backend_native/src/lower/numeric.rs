use std::fmt::Write;

use sal_syntax::{BinOp, Diagnostic, Expr};

use super::{Function, Local, Ty};

impl Function<'_> {
    pub(super) fn binary(
        &mut self,
        op: BinOp,
        left: &Expr,
        right: &Expr,
        expected: Option<Ty>,
    ) -> Result<Ty, Diagnostic> {
        if matches!(op, BinOp::And | BinOp::Or) {
            let left_ty = self.expression(left, Some(Ty::Bool))?;
            self.require(left_ty, Ty::Bool, "short-circuit left operand")?;
            let done = self.label();
            let branch = if op == BinOp::And { "je" } else { "jne" };
            let _ = writeln!(self.code, "    testq %rax, %rax\n    {branch} {done}");
            let right_ty = self.expression(right, Some(Ty::Bool))?;
            self.require(right_ty, Ty::Bool, "short-circuit right operand")?;
            let _ = writeln!(self.code, "{done}:");
            self.normalize(Ty::Bool);
            return Ok(Ty::Bool);
        }
        let arithmetic = matches!(
            op,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
        );
        let context = if arithmetic {
            expected.filter(|ty| ty.integer())
        } else {
            None
        }
        .or_else(|| self.hint(left))
        .or_else(|| self.hint(right));
        let left_ty = self.expression(left, context)?;
        if left_ty == Ty::Void {
            return Err(self.error("N100", "Void has no binary operations"));
        }
        let saved = Local {
            ty: left_ty,
            slot: self.allocate(left_ty),
            mutable: false,
        };
        self.store(saved);
        if left_ty == Ty::Borrow {
            // Slot arithmetic: `borrow(slot) + offset` is the generated
            // wrapper address idiom. The Borrow word is the ORIGINAL owner
            // slot address; an integer offset rides in the second operand.
            // Anything else with a Borrow operand is a type error. The left
            // side is spilled before the offset evaluates so nested calls
            // cannot clobber the slot address.
            if op != BinOp::Add {
                return Err(self.error(
                    "N100",
                    "native borrows support no operators except borrow + usize offset",
                ));
            }
            let right_ty = self.expression(right, Some(Ty::Usize))?;
            self.require(right_ty, Ty::Usize, "binary operands")?;
            self.code.push_str("    movq %rax, %rcx\n");
            self.load(saved);
            self.code.push_str("    addq %rcx, %rax\n");
            let _ = writeln!(self.code, "    jc .Lsal_trap_{}", self.index);
            return Ok(Ty::Usize);
        }
        let right_ty = self.expression(right, Some(left_ty))?;
        self.require(right_ty, left_ty, "binary operands")?;
        if arithmetic {
            return self.arithmetic(op, left_ty, saved);
        }
        if matches!(
            left_ty,
            Ty::Record(_) | Ty::Internal(_) | Ty::Buffer | Ty::MutBytes | Ty::Borrow
        ) {
            return Err(self.error(
                "N100",
                "native owners, borrows and records support no comparison operators",
            ));
        }
        if left_ty.span() {
            if !matches!(op, BinOp::Eq | BinOp::Ne) {
                return Err(self.error("N100", "native spans support only equality comparisons"));
            }
            self.text_equal(saved);
            if op == BinOp::Ne {
                self.code.push_str("    xorq $1, %rax\n");
            }
            return Ok(Ty::Bool);
        }
        if !matches!(op, BinOp::Eq | BinOp::Ne) && !left_ty.integer() {
            return Err(self.error("N100", "native ordering requires equal integer types"));
        }
        self.code.push_str("    movq %rax, %rcx\n");
        self.load(saved);
        self.code.push_str("    cmpq %rcx, %rax\n");
        let instruction = match (op, left_ty.signed()) {
            (BinOp::Eq, _) => "sete",
            (BinOp::Ne, _) => "setne",
            (BinOp::Lt, true) => "setl",
            (BinOp::Le, true) => "setle",
            (BinOp::Gt, true) => "setg",
            (BinOp::Ge, true) => "setge",
            (BinOp::Lt, false) => "setb",
            (BinOp::Le, false) => "setbe",
            (BinOp::Gt, false) => "seta",
            (BinOp::Ge, false) => "setae",
            _ => unreachable!("arithmetic handled above"),
        };
        let _ = writeln!(self.code, "    {instruction} %al\n    movzbl %al, %eax");
        Ok(Ty::Bool)
    }

    fn arithmetic(&mut self, op: BinOp, left_ty: Ty, saved: Local) -> Result<Ty, Diagnostic> {
        if !left_ty.integer() {
            return Err(self.error("N100", "native arithmetic requires equal integer types"));
        }
        self.code.push_str("    movq %rax, %rcx\n");
        self.load(saved);
        match op {
            BinOp::Add | BinOp::Sub => {
                let instruction = if op == BinOp::Add { "addq" } else { "subq" };
                let _ = writeln!(self.code, "    {instruction} %rcx, %rax");
                let overflow = if left_ty.signed() { "jo" } else { "jc" };
                let _ = writeln!(self.code, "    {overflow} .Lsal_trap_{}", self.index);
            }
            BinOp::Mul => {
                if left_ty.signed() {
                    let _ = writeln!(
                        self.code,
                        "    imulq %rcx, %rax\n    jo .Lsal_trap_{}",
                        self.index
                    );
                } else {
                    let _ = writeln!(self.code, "    mulq %rcx\n    jc .Lsal_trap_{}", self.index);
                }
            }
            BinOp::Div | BinOp::Rem => {
                let _ = writeln!(
                    self.code,
                    "    testq %rcx, %rcx\n    je .Lsal_trap_{}",
                    self.index
                );
                if !left_ty.signed() {
                    self.code.push_str("    xorl %edx, %edx\n    divq %rcx\n");
                } else if left_ty.bits() == 64 {
                    // x86 idiv raises SIGFPE for MIN/-1. SAL consistently
                    // uses its checked-arithmetic trap, including remainder.
                    let divide = self.label();
                    let _ = writeln!(self.code, "    cmpq $-1, %rcx\n    jne {divide}\n    movabsq $-9223372036854775808, %rdx\n    cmpq %rdx, %rax\n    je .Lsal_trap_{}\n{divide}:\n    cqto\n    idivq %rcx", self.index);
                } else {
                    // Narrow widths trap on their own MIN/-1 as well.
                    let min: i64 = match left_ty {
                        Ty::I8 => -128,
                        Ty::I16 => -32768,
                        Ty::I32 => -2147483648,
                        _ => unreachable!("signed narrow dividend classified above"),
                    };
                    let divide = self.label();
                    let _ = writeln!(self.code, "    cmpq $-1, %rcx\n    jne {divide}\n    cmpq ${min}, %rax\n    je .Lsal_trap_{}\n{divide}:\n    cqto\n    idivq %rcx", self.index);
                }
                if op == BinOp::Rem {
                    self.code.push_str("    movq %rdx, %rax\n");
                }
            }
            _ => unreachable!("arithmetic operator classified above"),
        }
        // Division/remainder stay in range after the explicit MIN/-1 guard.
        if matches!(op, BinOp::Div | BinOp::Rem) {
            return Ok(left_ty);
        }
        // Narrow results use the same 64-bit operation on canonical
        // sign/zero-extended operands; a 64-bit overflow already trapped
        // above, and a narrow overflow that fits in 64 bits traps here.
        match left_ty {
            Ty::I8 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $-128, %rax\n    jl .Lsal_trap_{}\n    cmpq $127, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::I16 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $-32768, %rax\n    jl .Lsal_trap_{}\n    cmpq $32767, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::I32 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $-2147483648, %rax\n    jl .Lsal_trap_{}\n    cmpq $2147483647, %rax\n    jg .Lsal_trap_{}",
                    self.index, self.index
                );
            }
            Ty::U8 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $255, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U16 => {
                let _ = writeln!(
                    self.code,
                    "    cmpq $65535, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            Ty::U32 => {
                // 4294967295 does not fit a sign-extended imm32; compare
                // against a full 64-bit constant instead.
                let _ = writeln!(
                    self.code,
                    "    movabsq $4294967295, %rcx\n    cmpq %rcx, %rax\n    ja .Lsal_trap_{}",
                    self.index
                );
            }
            _ => {}
        }
        Ok(left_ty)
    }
}
