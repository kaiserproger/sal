use super::*;

fn source_ir(source: &str) -> Ir {
    let (file, diagnostics) = sal_syntax::parse(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (ir, diagnostics) = sal_ir::build(&file);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    ir
}

#[test]
fn legacy_server_explicitly_rejects_c_features_instead_of_ignoring_them() {
    let server = "server Web:\n  listens on port 8080.\n  speaks HTTP/1.\nroute Home:\n  handles GET /.\n  responds with \"ok\".\n";
    for (feature, declaration) in [
        ("C import", "operation Foreign:\n  imports \"C\" as \"foreign\".\n  effects: SystemCall, UnsafeMemory.\n"),
        ("C record layout", "entity R:\n  layout \"C\".\n  has field of type i16.\n"),
        ("C record reflection", "operation F:\n  body:\n    size_of(R).\n"),
    ] {
        let errors = emit_exec(&source_ir(&format!("{server}{declaration}"))).unwrap_err();
        assert!(errors.iter().any(|d| d.code == "B201" && d.message.contains(feature)), "{errors:?}");
    }
    assert!(emit_exec(&source_ir(&format!(
        "{server}entity Metadata:\n  has text of type Text.\n"
    )))
    .is_ok());
}

#[test]
fn legacy_console_rejects_new_casts_and_reflection() {
    for expression in [
        "i8(1)",
        "i16(1)",
        "i32(1)",
        "u16(1)",
        "u32(1)",
        "u64(1)",
        "isize(1)",
        "size_of(R)",
        "align_of(R)",
        "offset_of(R, \"field\")",
    ] {
        let ir = source_ir(&format!(
            "operation Main:\n  returns Text.\n  body:\n    {expression}.\n    return \"hello\".\n"
        ));
        let errors = emit_exec(&ir).unwrap_err();
        assert!(
            errors.iter().any(|d| d.code == "B201"),
            "{expression}: {errors:?}"
        );
    }
}

#[test]
fn legacy_console_rejects_new_text_and_contract_assert_intrinsics() {
    for expression in ["text(bytes(\"hi\"))", "SalContractAssert(true)"] {
        let ir = source_ir(&format!(
            "operation Main:\n  returns Text.\n  body:\n    {expression}.\n    return \"hello\".\n"
        ));
        let errors = emit_exec(&ir).unwrap_err();
        assert!(
            errors.iter().any(|d| d.code == "B201"),
            "{expression}: {errors:?}"
        );
    }
}

#[test]
fn legacy_unsafe_traverses_and_reports_nested_intrinsics() {
    let ir = source_ir(
        "operation Main:\n  returns Text.\n  body:\n    unsafe:\n      usize(1).\n      return \"hello\".\n",
    );
    let errors = emit_exec(&ir).unwrap_err();
    assert!(errors.iter().any(|d| d.code == "B201"), "{errors:?}");
}
