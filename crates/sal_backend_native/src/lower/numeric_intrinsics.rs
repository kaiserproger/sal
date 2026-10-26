//! Pure machine integer boundaries only. All arithmetic/bit/shift
//! algorithms stay in SAL; this file emits single x86-64 instructions.
//!
//! Contract (sal-safe-stdlib-contract.md, checked bit/word boundaries):
//! `wrapping_add(T,T)`, `wrapping_sub`, `wrapping_mul`, `bit_and`, `bit_or`,
//! `bit_xor`, `bit_not(T)`, `shift_left(T,usize)`, `shift_right(T,usize)` for
//! same-width integer T in {i8,i16,i32,i64,isize,u8,u16,u32,u64,usize}.
//! Results retain T. Wrapping ops wrap low bits with no trap; shifts trap
//! when count >= bit width; signed right shift is arithmetic, unsigned is
//! logical; left shift truncates shifted-out bits. Arguments evaluate once
//! in source order; no accidental upper-bit contamination; no heap
//! allocation. Uses existing `Function::expression/store/load` typed slots
//! and the per-function native trap label `.Lsal_trap_{index}`.
//!
//! Plus one explicit reinterpretation boundary (VarInt/VarLong codecs):
//! `bits_as(Target, value)` where `Target` is a compile-time integer type
//! name and `value` is an integer of the SAME bit width. Bits preserved
//! exactly; result normalized per target signedness. No checked-cast range
//! logic changed: `bits_as` is a distinct explicit semantic. Only the value
//! operand is evaluated (once); the target name is compile-time.
//!
//! Wiring is complete: dispatch, hints, IR reservation/typing, concurrency
//! ownership checks and legacy B201 rejection are all landed and preserved
//! by existing tests. Effects stay pure with no C ABI exposure.

use std::fmt::Write;

use sal_syntax::{Diagnostic, Expr};

use super::{Function, Local, Ty};

impl Function<'_> {
    /// True for the ten exact boundary spellings (nine contract intrinsics
    /// plus `bits_as`). The compiler owner calls this from
    /// `expression_inner` dispatch; `builtin_result` intentionally stays
    /// `None` so the result type is resolved here from the operands.
    pub(super) fn numeric_intrinsic_name(name: &str) -> bool {
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

    /// Integer type named by a `bits_as` target operand. The target is a
    /// compile-time type name only, never a runtime value.
    fn bits_as_target(name: &str) -> Option<Ty> {
        match name {
            "i8" => Some(Ty::I8),
            "i16" => Some(Ty::I16),
            "i32" => Some(Ty::I32),
            "i64" => Some(Ty::I64),
            "isize" => Some(Ty::Isize),
            "u8" => Some(Ty::U8),
            "u16" => Some(Ty::U16),
            "u32" => Some(Ty::U32),
            "u64" => Some(Ty::U64),
            "usize" => Some(Ty::Usize),
            _ => None,
        }
    }

    /// Lower one intrinsic call. `expected` is the call-site result context
    /// from `expression_inner` (e.g. a `returns u8` binding): an integer
    /// expectation acts as a last-resort literal context only. Explicitly
    /// typed operands never silently convert; a non-literal operand whose
    /// type differs from its peer still fails N100. Each argument evaluates
    /// exactly once in source order into typed frame slots, then only
    /// machine instructions run on the canonical sign/zero-extended words.
    /// Narrow results are re-canonicalized so upper bits never leak.
    pub(super) fn numeric_intrinsic(
        &mut self,
        name: &str,
        args: &[Expr],
        expected: Option<Ty>,
    ) -> Result<Ty, Diagnostic> {
        debug_assert!(Self::numeric_intrinsic_name(name));
        let arity = if name == "bit_not" { 1 } else { 2 };
        if args.len() != arity {
            return Err(self.error(
                "B108",
                format!("native {name} requires exactly {arity} arguments"),
            ));
        }
        if name == "bits_as" {
            // Target is a compile-time type name, not a runtime expression:
            // only the value operand is evaluated (once). Bits are preserved
            // exactly; the value already sits canonical in %rax, so identity
            // plus target-signedness normalization is the whole machine step.
            if args.len() != 2 {
                return Err(self.error(
                    "B108",
                    format!("native {name} requires exactly 2 arguments"),
                ));
            }
            let target = match &args[0] {
                Expr::Var(target) => Self::bits_as_target(target).ok_or_else(|| {
                    self.error(
                        "B108",
                        format!(
                            "native bits_as target requires an integer type name, got `{target}`"
                        ),
                    )
                })?,
                _ => {
                    return Err(self.error(
                        "B108",
                        "native bits_as target must be a compile-time integer type name".to_owned(),
                    ));
                }
            };
            let value_ty = self.expression(&args[1], Some(target))?;
            if !value_ty.integer() {
                return Err(self.error(
                    "N100",
                    "native bits_as requires an integer value".to_owned(),
                ));
            }
            if value_ty.bits() != target.bits() {
                return Err(self.error(
                    "N100",
                    format!("native bits_as requires the same bit width, found {value_ty:?} and {target:?}; native lowering does not cast values"),
                ));
            }
            let value = self.spill_operand(value_ty);
            self.load(value);
            self.narrow_canonical(target);
            return Ok(target);
        }
        if name == "bit_not" {
            if args.len() != 1 {
                return Err(
                    self.error("B108", format!("native {name} requires exactly 1 argument"))
                );
            }
            let context = self.integer_context(&args[0], None, expected);
            let value_ty = self.expression(&args[0], context)?;
            if !value_ty.integer() {
                return Err(self.error("N100", format!("native {name} requires an integer type")));
            }
            let value = self.spill_operand(value_ty);
            self.load(value);
            self.code.push_str("    notq %rax\n");
            self.narrow_canonical(value_ty);
            return Ok(value_ty);
        }
        if name == "shift_left" || name == "shift_right" {
            if args.len() != 2 {
                return Err(self.error(
                    "B108",
                    format!("native {name} requires exactly 2 arguments"),
                ));
            }
            let context = self.integer_context(&args[0], None, expected);
            let value_ty = self.expression(&args[0], context)?;
            if !value_ty.integer() {
                return Err(self.error("N100", format!("native {name} requires an integer value")));
            }
            let value = self.spill_operand(value_ty);
            let count_ty = self.expression(&args[1], Some(Ty::Usize))?;
            if count_ty != Ty::Usize {
                return Err(self.error("N100", format!("native {name} shift count requires usize")));
            }
            let count = self.spill_operand(count_ty);
            // Both operands are evaluated; load count into RCX first, then
            // the value into RAX, so neither clobbers the other.
            let _ = writeln!(self.code, "    movq -{}(%rbp), %rcx", count.slot);
            let _ = writeln!(self.code, "    movq -{}(%rbp), %rax", value.slot);
            let _ = writeln!(
                self.code,
                "    cmpq ${}, %rcx\n    jae .Lsal_trap_{}",
                value_ty.bits(),
                self.index
            );
            if name == "shift_left" {
                self.code.push_str("    shlq %cl, %rax\n");
            } else if value_ty.signed() {
                self.code.push_str("    sarq %cl, %rax\n");
            } else {
                self.code.push_str("    shrq %cl, %rax\n");
            }
            self.narrow_canonical(value_ty);
            return Ok(value_ty);
        }
        // Binary wrapping/bitwise: same-width T for both operands. Literals
        // take the peer's type first (`wrapping_add(1, byte)` and
        // `wrapping_add(byte, 1)` both resolve to the byte's width); the
        // call-site result expectation is the last resort, so a bare
        // `returns u8: wrapping_add(250, 10)` wraps to 4 instead of
        // defaulting both literals to i64. Explicitly typed operands never
        // silently convert: once the first operand has a type, the second
        // must match it exactly (N100).
        let context = self.integer_context(&args[0], Some(&args[1]), expected);
        let left_ty = self.expression(&args[0], context)?;
        if !left_ty.integer() {
            return Err(self.error("N100", format!("native {name} requires integer types")));
        }
        let left = self.spill_operand(left_ty);
        let right_ty = self.expression(&args[1], Some(left_ty))?;
        if right_ty != left_ty {
            return Err(self.error(
                "N100",
                format!("native {name} requires equal integer types, found {left_ty:?} and {right_ty:?}; native lowering does not cast values"),
            ));
        }
        let right = self.spill_operand(right_ty);
        self.load(left);
        let instruction = match name {
            "wrapping_add" => "addq",
            "wrapping_sub" => "subq",
            "wrapping_mul" => "imulq",
            "bit_and" => "andq",
            "bit_or" => "orq",
            "bit_xor" => "xorq",
            _ => unreachable!("numeric intrinsic name validated above"),
        };
        let _ = writeln!(self.code, "    {instruction} -{}(%rbp), %rax", right.slot);
        // Wrapping/bitwise never trap; truncate to the low bits. 64-bit
        // words are already canonical; narrow words are re-extended so
        // sign-extension copies (signed) or zeros (unsigned) are exact.
        self.narrow_canonical(left_ty);
        Ok(left_ty)
    }

    /// Call-site type hint for an intrinsic call, for the compiler owner's
    /// `hint` dispatch. `bits_as` hints its compile-time target; unary and
    /// shift forms hint their value operand; binary forms hint the first
    /// operand, else the peer (recursively via `hint`, so nested intrinsic
    /// calls propagate: `wrapping_add(1, wrapping_mul(u8(10), u8(2)))`
    /// infers u8 through the inner call's own hint). Never invents a type
    /// for literals: returns None unless an operand already has one.
    pub(super) fn numeric_intrinsic_hint(&self, name: &str, args: &[Expr]) -> Option<Ty> {
        debug_assert!(Self::numeric_intrinsic_name(name));
        if name == "bits_as" {
            return match args.first() {
                Some(Expr::Var(target)) => Self::bits_as_target(target),
                _ => None,
            };
        }
        if name == "bit_not" {
            return args.first().and_then(|operand| self.hint(operand));
        }
        if name == "shift_left" || name == "shift_right" {
            return args.first().and_then(|operand| self.hint(operand));
        }
        let (first, second) = match args {
            [first, second] => (first, second),
            _ => return None,
        };
        self.hint(first)
            .filter(|ty| ty.integer())
            .or_else(|| self.hint(second).filter(|ty| ty.integer()))
    }

    /// Type context for a value operand: the operand's own hint first, then
    /// the peer's hint, then the call-site integer expectation. Mirrors how
    /// checked `+`/`-` propagate contexts without ever silently converting
    /// a variable's type: `expected` only types otherwise-untyped literals.
    fn integer_context(
        &self,
        operand: &Expr,
        peer: Option<&Expr>,
        expected: Option<Ty>,
    ) -> Option<Ty> {
        self.hint(operand)
            .filter(|ty| ty.integer())
            .or_else(|| {
                peer.and_then(|peer| self.hint(peer))
                    .filter(|ty| ty.integer())
            })
            .or_else(|| expected.filter(|ty| ty.integer()))
    }

    /// Spill the `%rax` result of the just-evaluated operand into its typed
    /// frame slot. Each operand is evaluated exactly once, in source order.
    fn spill_operand(&mut self, ty: Ty) -> Local {
        let local = Local {
            ty,
            slot: self.allocate(ty),
            mutable: false,
        };
        self.store(local);
        local
    }

    /// Re-canonicalize a narrow integer result: low bits are the value,
    /// upper bits become the sign copy (signed) or zero (unsigned). 64-bit
    /// types are already canonical and emit nothing.
    fn narrow_canonical(&mut self, ty: Ty) {
        if ty.bits() < 64 {
            self.normalize(ty);
        }
    }
}

#[cfg(test)]
mod numeric_intrinsics_machine_tests {
    use super::*;
    use crate::{emit_native, NativeTarget};
    use sal_ir::Ir;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn ir(source: &str) -> Ir {
        let (file, diagnostics) = sal_syntax::parse(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let (ir, diagnostics) = sal_ir::build(&file);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        ir
    }

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "sal-numeric-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn command(tool: &str, args: &[&str], directory: &Path) -> Output {
        let output = Command::new(tool)
            .args(args)
            .current_dir(directory)
            .output()
            .unwrap_or_else(|error| panic!("{tool} unavailable: {error}"));
        assert!(
            output.status.success(),
            "{tool} {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    fn executable(source: &str) -> (Directory, PathBuf) {
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::Executable).unwrap();
        std::fs::write(directory.0.join("main.s"), program.assembly).unwrap();
        command("as", &["--64", "-o", "main.o", "main.s"], &directory.0);
        command("ld", &["-o", "main", "main.o"], &directory.0);
        let path = directory.0.join("main");
        (directory, path)
    }

    fn trap_signal(output: &std::process::Output) -> Option<i32> {
        use std::os::unix::process::ExitStatusExt;
        output.status.signal()
    }

    #[test]
    fn intrinsic_names_are_exact_boundary_spellings() {
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
            assert!(
                Function::numeric_intrinsic_name(name),
                "{name} must be a registered intrinsic"
            );
        }
        for name in [
            "wrappingadd",
            "shiftleft",
            "shiftright",
            "bitsas",
            "add",
            "shl",
            "wrapping_add_u8",
            "Wrapping_Add",
        ] {
            assert!(
                !Function::numeric_intrinsic_name(name),
                "{name} must not be accepted"
            );
        }
    }

    #[test]
    fn wrapping_wraps_low_bits_all_widths() {
        let source = r#"operation Main:
    returns i64.
    body:
        if wrapping_add(u8(255), u8(1)) != u8(0):
            return 1.
        if wrapping_sub(u8(0), u8(1)) != u8(255):
            return 2.
        if wrapping_mul(u8(16), u8(16)) != u8(0):
            return 3.
        if wrapping_mul(u8(200), u8(2)) != u8(144):
            return 4.
        if wrapping_add(i8(127), i8(1)) != i8(0 - 128):
            return 5.
        if wrapping_sub(i8(0 - 128), i8(1)) != i8(127):
            return 6.
        if wrapping_mul(i16(32767), i16(2)) != i16(0 - 2):
            return 7.
        if wrapping_add(u16(65535), u16(1)) != u16(0):
            return 8.
        if wrapping_add(i32(2147483647), i32(1)) != i32(0 - 2147483648):
            return 9.
        if wrapping_sub(u32(0), u32(1)) != u32(4294967295):
            return 10.
        if wrapping_mul(u32(70000), u32(70000)) != u32(605032704):
            return 11.
        if wrapping_add(i64(-9223372036854775808), i64(0 - 1)) != 9223372036854775807:
            return 12.
        if wrapping_add(wrapping_sub(usize(0), usize(1)), usize(1)) != usize(0):
            return 13.
        if wrapping_mul(isize(3037000500), isize(3037000500)) != isize(0 - 9223372036709301616):
            return 14.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn return_context_types_bare_literal_intrinsics() {
        // Call-site result expectation is the last-resort literal context:
        // bare literals in a `returns u8` body wrap as u8 instead of
        // defaulting to i64. Typed operands still never silently convert.
        let source = r#"operation WrapU8:
    returns u8.
    body:
        return wrapping_add(250, 10).
operation WrapI8:
    returns i8.
    body:
        return wrapping_add(127, 1).
operation NotU8:
    returns u8.
    body:
        return bit_not(0).
operation ShiftU8:
    returns u8.
    body:
        return shift_left(1, usize(7)).
operation BitsU8:
    returns u8.
    body:
        return bits_as(u8, 255).
operation Main:
    returns i64.
    body:
        if WrapU8() != u8(4):
            return 1.
        if WrapI8() != i8(0 - 128):
            return 2.
        if NotU8() != u8(255):
            return 3.
        if ShiftU8() != u8(128):
            return 4.
        if BitsU8() != u8(255):
            return 5.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn nested_peer_literals_infer_through_hints() {
        // Inner intrinsic hints propagate outward: the u8 pair inside
        // `wrapping_mul` types the outer `wrapping_add` literal, and the
        // nested shift value inherits its u16 operand type.
        let source = r#"operation Main:
    returns i64.
    body:
        if wrapping_add(1, wrapping_mul(u8(10), u8(2))) != u8(21):
            return 1.
        if bit_or(u8(240), bit_and(u8(15), u8(255))) != u8(255):
            return 2.
        if shift_left(bit_or(u16(1), u16(2)), usize(2)) != u16(12):
            return 3.
        if bits_as(u8, wrapping_add(250, 10)) != u8(4):
            return 4.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn bitwise_ignores_upper_bits() {
        // 65280 == 0xFF00, 4080 == 0x0FF0: AND == 0x0F00, OR == 0xFFF0,
        // XOR == 0xF0F0. 170 == 0xAA, 85 == 0x55.
        let source = r#"operation Main:
    returns i64.
    body:
        if bit_and(u16(65280), u16(4080)) != u16(3840):
            return 1.
        if bit_or(u16(65280), u16(4080)) != u16(65520):
            return 2.
        if bit_xor(u16(65280), u16(4080)) != u16(61680):
            return 3.
        if bit_not(u16(0)) != u16(65535):
            return 4.
        if bit_not(u8(0)) != u8(255):
            return 5.
        if bit_xor(u8(170), u8(85)) != u8(255):
            return 6.
        if bit_and(i8(0 - 1), i8(127)) != i8(127):
            return 7.
        if bit_or(u32(4026531840), u32(16711935)) != u32(4043243775):
            return 8.
        if bit_not(u32(0)) != u32(4294967295):
            return 9.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn shifts_match_signedness_and_edge_counts() {
        let source = r#"operation Main:
    returns i64.
    body:
        if shift_left(u8(1), usize(0)) != u8(1):
            return 1.
        if shift_left(u8(1), usize(7)) != u8(128):
            return 2.
        if shift_left(u8(255), usize(1)) != u8(254):
            return 3.
        if shift_left(i64(1), usize(62)) != 4611686018427387904:
            return 4.
        if shift_left(isize(1), usize(63)) != isize(-9223372036854775808):
            return 5.
        if shift_right(u8(255), usize(1)) != u8(127):
            return 6.
        if shift_right(u8(128), usize(7)) != u8(1):
            return 7.
        if shift_right(i8(0 - 128), usize(1)) != i8(0 - 64):
            return 8.
        if shift_right(i8(0 - 128), usize(7)) != i8(0 - 1):
            return 9.
        if shift_right(i64(0 - 1), usize(63)) != i64(0 - 1):
            return 10.
        if shift_right(shift_left(u16(1), usize(15)), usize(15)) != u16(1):
            return 11.
        if shift_right(wrapping_sub(u64(0), u64(1)), usize(63)) != u64(1):
            return 12.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn shift_count_at_width_traps() {
        for (ty, value, count) in [
            ("u8", "u8(1)", "usize(8)"),
            ("u8", "u8(1)", "usize(9)"),
            ("u8", "shift_left(u8(1), usize(7))", "usize(8)"),
            ("u16", "u16(1)", "usize(16)"),
            ("u32", "u32(1)", "usize(32)"),
            ("i32", "i32(1)", "usize(32)"),
            ("u64", "u64(1)", "usize(64)"),
            ("i64", "i64(0 - 1)", "usize(64)"),
            ("usize", "usize(1)", "usize(64)"),
            ("isize", "isize(1)", "usize(64)"),
            ("i8", "i8(1)", "usize(8)"),
        ] {
            for name in ["shift_left", "shift_right"] {
                let source = format!("operation Probe:\n    returns {ty}.\n    body:\n        return {name}({value}, {count}).\noperation Main:\n    returns Text.\n    body:\n        Probe().\n        return \"must not run\".\n");
                let (_directory, path) = executable(&source);
                let output = Command::new(path).output().unwrap();
                assert_eq!(trap_signal(&output), Some(4), "{name}({value}, {count})");
                assert!(output.stdout.is_empty());
            }
        }
    }

    #[test]
    fn arguments_evaluate_once_in_source_order() {
        // Ordered bumps the marker only when it observes the expected
        // sequence number, so swapped or repeated evaluation fails the
        // follow-up marker check even when the arithmetic sum matches.
        let source = r#"operation Ordered:
    accepts marker of type usize.
    accepts expected of type u8.
    accepts value of type u8.
    returns u8.
    effects: UnsafeMemory.
    body:
        if load8(marker) == expected:
            store8(marker, expected + u8(1)).
            return value.
        else:
            return u8(255).
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let scratch = syscall(9, 0, 4096, 3, 34, -1, 0).
        if scratch < 0:
            return 90.
        else:
            let base = usize(scratch).
            store8(base, u8(0)).
            let sum = wrapping_add(Ordered(base, u8(0), u8(10)), Ordered(base, u8(1), u8(20))).
            if sum != u8(30):
                return 1.
            else:
                if load8(base) != u8(2):
                    return 2.
                else:
                    let shifted = shift_left(Ordered(base, u8(2), u8(4)), usize(1)).
                    if shifted != u8(8):
                        return 3.
                    else:
                        if load8(base) != u8(3):
                            return 4.
                        else:
                            if bit_xor(Ordered(base, u8(3), u8(15)), Ordered(base, u8(4), u8(240))) != u8(255):
                                return 5.
                            else:
                                if load8(base) != u8(5):
                                    return 6.
                                else:
                                    return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn bits_as_preserves_bits_across_signedness() {
        let source = r#"operation Main:
    returns i64.
    body:
        if bits_as(u8, i8(0 - 1)) != u8(255):
            return 1.
        if bits_as(i8, u8(255)) != i8(0 - 1):
            return 2.
        if bits_as(u16, i16(0 - 1)) != u16(65535):
            return 3.
        if bits_as(i16, u16(65535)) != i16(0 - 1):
            return 4.
        if bits_as(u32, i32(0 - 1)) != u32(4294967295):
            return 5.
        if bits_as(i32, u32(4294967295)) != i32(0 - 1):
            return 6.
        if bits_as(u64, i64(0 - 1)) != bit_not(u64(0)):
            return 7.
        if bits_as(i64, u64(9223372036854775807)) != 9223372036854775807:
            return 8.
        if bits_as(usize, isize(0 - 1)) != bit_not(usize(0)):
            return 9.
        if bits_as(isize, usize(5)) != isize(5):
            return 10.
        if bits_as(u8, u8(170)) != u8(170):
            return 11.
        let value = wrapping_add(u8(250), u8(10)).
        if bits_as(i8, value) != i8(4):
            return 12.
        return 0.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
    }

    #[test]
    fn rejects_mixed_widths_non_integer_and_bad_counts() {
        for source in [
            "operation Main:\n    returns u8.\n    body:\n        return wrapping_add(u8(1), u16(1)).\n",
            "operation Main:\n    returns i64.\n    body:\n        return wrapping_add(1, true).\n",
            "operation Main:\n    returns u8.\n    body:\n        return bit_and(u8(1), true).\n",
            "operation Main:\n    returns i64.\n    body:\n        return shift_right(1, i64(1)).\n",
            "operation Main:\n    returns Text.\n    body:\n        return bit_not(\"x\").\n",
            "operation Main:\n    returns i64.\n    body:\n        return wrapping_add(1).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bit_not(1, 2).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(u8, u16(1)).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(i32, u16(1)).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(u8, true).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(Missing, u8(1)).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(\"u8\", u8(1)).\n",
            "operation Main:\n    returns i64.\n    body:\n        return bits_as(u8, Text, u8(1)).\n",
        ] {
            assert!(
                emit_native(&ir(source), NativeTarget::Executable).is_err(),
                "{source}"
            );
        }
    }
}
