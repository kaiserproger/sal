use super::*;

#[test]
fn canonical_c_metadata_and_defaults() {
    let (file, diagnostics) = parse(
        "entity Pair:\n  layout \"C\".\n  has x of type i16.\nentity Spec:\n  has text of type Text.\noperation Foreign:\n  imports \"C\" as \"foreign_pair\".\n  returns Pair.\n  effects: SystemCall, UnsafeMemory.\noperation SpecOp:\n  returns Text.\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let Item::Entity(record) = &file.items[0] else {
        panic!("record")
    };
    assert!(record.c_layout);
    let Item::Entity(spec) = &file.items[1] else {
        panic!("spec")
    };
    assert!(!spec.c_layout);
    let Item::Operation(import) = &file.items[2] else {
        panic!("import")
    };
    assert_eq!(import.c_import.as_deref(), Some("foreign_pair"));
    assert!(import.c_export.is_none());
    assert!(import.body.is_empty());
    let Item::Operation(spec) = &file.items[3] else {
        panic!("spec")
    };
    assert!(spec.c_import.is_none());
}

#[test]
fn malformed_and_conflicting_c_metadata_is_rejected() {
    for source in [
        "entity R:\n  layout \"Rust\".\n",
        "entity R:\n  layout \"C\".\n  layout \"C\".\n",
        "entity R:\n  layout C.\n",
        "operation F:\n  imports \"Rust\" as \"f\".\n",
        "operation F:\n  imports \"C\" as \"bad-name\".\n",
        "operation F:\n  imports \"C\" as \"f\" extra.\n",
        "operation F:\n  imports \"C\" as \"f\".\n  imports \"C\" as \"g\".\n",
        "operation F:\n  imports \"C\" as \"f\".\n  exports \"C\" as \"g\".\n",
        "operation F:\n  exports \"C\" as \"f\".\n  imports \"C\" as \"g\".\n",
    ] {
        let (_, diagnostics) = parse(source);
        assert_eq!(diagnostics.len(), 1, "{source}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code, "E0004", "{source}");
    }
}

#[test]
fn contract_metadata_defaults_to_parser_false_and_empty() {
    let (file, diagnostics) = parse(
        "entity Pair:\n  layout \"C\".\n  has x of type i16.\noperation Foreign:\n  imports \"C\" as \"foreign_pair\".\n  returns Pair.\n  effects: SystemCall, UnsafeMemory.\n",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let Item::Entity(record) = &file.items[0] else {
        panic!("record")
    };
    assert!(!record.json.enabled);
    assert!(record.json.defaults.is_empty());
    assert!(record.json.requires.is_empty());
    assert!(record.iteration.is_none());
    assert!(!record.generated);
    let Item::Operation(import) = &file.items[1] else {
        panic!("import")
    };
    assert!(import.requires.is_empty());
    assert!(import.ensures.is_empty());
    assert!(import.ownership.borrows.is_empty());
    assert!(import.ownership.consumes.is_empty());
    assert!(import.ownership.return_from.is_empty());
    assert!(!import.ownership.lowered);
    assert!(!import.generated);
}

#[test]
fn malformed_deep_reflection_operands_are_discarded_iteratively() {
    let nested = format!("{}1{}", "size_of(".repeat(20_000), ")".repeat(20_000));
    let (_, diagnostics) = parse(&format!(
        "operation F:\n  body:\n    offset_of({nested},).\n    size_of({nested} extra).\n"
    ));
    assert_eq!(diagnostics.len(), 2);
    assert!(diagnostics
        .iter()
        .all(|diagnostic| diagnostic.code == "E0004"));
}
