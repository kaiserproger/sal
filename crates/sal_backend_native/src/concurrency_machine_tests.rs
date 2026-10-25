use crate::{emit_native, NativeTarget};

fn errors(source: &str) -> Vec<sal_syntax::Diagnostic> {
    let (file, diagnostics) = sal_syntax::parse(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (ir, mut diagnostics) = sal_ir::build(&file);
    if let Err(errors) = emit_native(&ir, NativeTarget::Executable) {
        diagnostics.extend(errors);
    }
    diagnostics
}

#[test]
fn machine_boundaries_require_exact_operand_types() {
    for expression in [
        "atomic_load(i64(0))",
        "atomic_store(usize(0), u64(1))",
        "atomic_cas(usize(0), u32(0), u64(1))",
        "load64(i64(0))",
        "store64(usize(0), u32(1))",
        "thread_launch(usize(0), usize(0), usize(0))",
        "concurrency_state(usize(0))",
    ] {
        let source = format!("operation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        {expression}.\n        return 0.\n");
        let diagnostics = errors(&source);
        assert!(
            diagnostics
                .iter()
                .any(|d| matches!(d.code, "B101" | "B107" | "B108")),
            "{expression}: {diagnostics:?}"
        );
    }
}

#[test]
fn function_addresses_are_not_unchecked_name_or_integer_casts() {
    for operand in ["usize(0)", "Missing", "Wrong"] {
        let source = format!("operation Wrong:\n    accepts value of type i64.\n    returns i64.\n    body:\n        return value.\noperation Main:\n    returns i64.\n    effects: UnsafeMemory.\n    body:\n        operation_address({operand}).\n        return 0.\n");
        assert!(
            errors(&source).iter().any(|d| d.code == "B108"),
            "{operand}"
        );
    }
}

#[test]
fn machine_concurrency_capabilities_are_not_implicitly_pure() {
    for expression in [
        "atomic_load(usize(0))",
        "atomic_store(usize(0), u32(0))",
        "atomic_cas(usize(0), u32(0), u32(1))",
        "load64(usize(0))",
        "store64(usize(0), usize(0))",
        "concurrency_state()",
        "thread_launch(usize(0), usize(0), usize(0), usize(0))",
    ] {
        let source = format!("operation Main:\n    returns i64.\n    body:\n        {expression}.\n        return 0.\n");
        assert!(
            errors(&source).iter().any(|d| d.code == "EFF203"),
            "{expression}"
        );
    }
}
