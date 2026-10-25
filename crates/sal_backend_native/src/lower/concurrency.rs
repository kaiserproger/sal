//! Machine/OS boundaries only. Channel arbitration and thread ownership live in SAL.
use std::fmt::Write;

use sal_syntax::{Diagnostic, Expr};

use super::{Function, Ty};

impl Function<'_> {
    pub(super) fn concurrency_builtin(
        &mut self,
        name: &str,
        args: &[Expr],
    ) -> Result<Ty, Diagnostic> {
        if name == "operation_address" {
            let [Expr::Var(operation)] = args else {
                return Err(self.error("B108", "operation_address requires one operation name"));
            };
            let signature = self.signatures.get(operation).ok_or_else(|| {
                self.error("B108", "operation_address requires a defined SAL operation")
            })?;
            if signature.params != [Ty::Usize]
                || signature.result != Ty::I64
                || signature.foreign.is_some()
            {
                return Err(self.error("B108", "operation_address requires SAL (usize) -> i64"));
            }
            let _ = writeln!(
                self.code,
                "    leaq .Lsal_fn_{}(%rip), %rax",
                signature.index
            );
            return Ok(Ty::Usize);
        }
        let expected: &[Option<Ty>] = match name {
            "atomic_load" | "load64" => &[Some(Ty::Usize)],
            "atomic_store" => &[Some(Ty::Usize), Some(Ty::U32)],
            "atomic_cas" => &[Some(Ty::Usize), Some(Ty::U32), Some(Ty::U32)],
            "store64" => &[Some(Ty::Usize), Some(Ty::Usize)],
            "thread_launch" => &[Some(Ty::Usize); 4],
            "concurrency_state" => &[],
            _ => return Err(self.error("N100", "unknown concurrency machine boundary")),
        };
        let values = self.builtin_args(name, args, expected)?;
        if name.starts_with("atomic_") {
            self.load(values[0]);
            let _ = writeln!(
                self.code,
                "    testq $3, %rax\n    jnz .Lsal_trap_{}\n    movq %rax, %rcx",
                self.index
            );
        }
        match name {
            "atomic_load" => self.code.push_str("    movl (%rcx), %eax\n"),
            "atomic_store" => {
                self.load(values[1]);
                self.code.push_str("    xchgl %eax, (%rcx)\n");
            }
            "atomic_cas" => {
                self.load(values[2]);
                self.code.push_str("    movl %eax, %edx\n");
                self.load(values[1]);
                self.code.push_str("    lock cmpxchgl %edx, (%rcx)\n");
            }
            "load64" => {
                self.load(values[0]);
                self.code.push_str("    movq (%rax), %rax\n");
            }
            "store64" => {
                self.load(values[0]);
                self.code.push_str("    movq %rax, %rcx\n");
                self.load(values[1]);
                self.code.push_str("    movq %rax, (%rcx)\n");
            }
            "concurrency_state" => self
                .code
                .push_str("    leaq .Lsal_concurrency_state(%rip), %rax\n"),
            "thread_launch" => {
                let parent = self.label();
                // clone is not an ordinary function call: the child has an
                // entirely different stack and must never return through the
                // parent's SAL frame. Copy only its entry, argument and clear-
                // tid/result address onto the supplied 16-aligned stack.
                // 0x1350f00 = VM | FS | FILES | SIGHAND | THREAD | SYSVSEM |
                // PARENT_SETTID | CHILD_SETTID | CHILD_CLEARTID. No TLS runtime
                // is installed or required by native SAL code.
                let _ = writeln!(self.code,
                    "    movq -{}(%rbp), %rsi\n    testq $15, %rsi\n    jnz .Lsal_trap_{}\n    subq $32, %rsi\n    movq -{}(%rbp), %rax\n    movq %rax, (%rsi)\n    movq -{}(%rbp), %rax\n    movq %rax, 8(%rsi)\n    movq -{}(%rbp), %rdx\n    testq $3, %rdx\n    jnz .Lsal_trap_{}\n    movq %rdx, 16(%rsi)\n    movq %rdx, %r10\n    xorl %r8d, %r8d\n    movl $20254464, %edi\n    movl $56, %eax\n    syscall\n    testq %rax, %rax\n    jne {parent}\n    movq (%rsp), %rax\n    movq 8(%rsp), %rdi\n    movq 16(%rsp), %r12\n    call *%rax\n    movq %rax, 8(%r12)\n    xorl %edi, %edi\n    movl $60, %eax\n    syscall\n    ud2\n{parent}:",
                    values[2].slot, self.index, values[0].slot,
                    values[1].slot, values[3].slot, self.index);
            }
            _ => unreachable!("validated concurrency machine boundary"),
        }
        Ok(Self::builtin_result(name).expect("registered concurrency builtin"))
    }
}
