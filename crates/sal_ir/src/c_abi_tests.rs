use super::*;

fn ir(source: &str) -> Ir {
    let (file, diagnostics) = sal_syntax::parse(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (ir, diagnostics) = build(&file);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    ir
}

const RECORDS: &str = "entity Inner:\n  layout \"C\".\n  has small of type u8.\n  has wide of type i32.\nentity Outer:\n  layout \"C\".\n  has flag of type bool.\n  has inner of type Inner.\n  has end of type u16.\n";

#[test]
fn layouts_match_natural_c_padding_and_declaration_order() {
    let ir = ir(RECORDS);
    assert!(check_types(&ir).is_empty());
    let layouts = c_record_layouts(&ir, CAbiTarget::LinuxX86_64).unwrap();
    let inner = &layouts["Inner"];
    assert_eq!((inner.size, inner.align), (8, 4));
    assert_eq!(
        inner
            .fields
            .iter()
            .map(|f| (f.name.as_str(), f.offset))
            .collect::<Vec<_>>(),
        [("small", 0), ("wide", 4)]
    );
    let outer = &layouts["Outer"];
    assert_eq!((outer.size, outer.align), (16, 4));
    assert_eq!(
        outer.fields.iter().map(|f| f.offset).collect::<Vec<_>>(),
        [0, 4, 12]
    );
    assert_eq!(outer.fields[1].ty, TypeRef::Named("Inner".into()));
}

#[test]
fn all_native_scalar_field_widths_are_target_checked() {
    let types = [
        "i8", "u8", "bool", "i16", "u16", "i32", "u32", "i64", "u64", "usize", "isize",
    ];
    let mut source = String::new();
    for (index, ty) in types.iter().enumerate() {
        source.push_str(&format!(
            "entity R{index}:\n  layout \"C\".\n  has value of type {ty}.\n"
        ));
    }
    let layouts = c_record_layouts(&ir(&source), CAbiTarget::LinuxX86_64).unwrap();
    for (index, size) in [1, 1, 1, 2, 2, 4, 4, 8, 8, 8, 8].into_iter().enumerate() {
        let layout = &layouts[&format!("R{index}")];
        assert_eq!((layout.size, layout.align), (size, size));
    }
}

#[test]
fn invalid_layouts_fail_deterministically_without_restricting_specs() {
    for fields in [
        "",
        "  has a of type Text.\n",
        "  has a of type Bytes.\n",
        "  has a of type Word.\n",
        "  has a of type Character.\n",
        "  has a of type f32.\n",
        "  has a of type f64.\n",
        "  has a of type i128.\n",
        "  has a of type u128.\n",
        "  has a of type Vec<u8>.\n",
        "  has a of type Missing.\n",
        "  has a of type Spec.\n",
        "  has a of type u8.\n  has a of type u8.\n",
    ] {
        let ir = ir(&format!(
            "entity Spec:\n  has text of type Text.\nentity R:\n  layout \"C\".\n{fields}"
        ));
        let first = c_record_layouts(&ir, CAbiTarget::LinuxX86_64).unwrap_err();
        let second = c_record_layouts(&ir, CAbiTarget::LinuxX86_64).unwrap_err();
        assert!(first.iter().all(|d| d.code == "E2010"));
        assert_eq!(
            first.iter().map(|d| &d.message).collect::<Vec<_>>(),
            second.iter().map(|d| &d.message).collect::<Vec<_>>()
        );
        assert!(check_types(&ir).iter().any(|d| d.code == "E2010"));
    }
    let specs = ir("entity Spec:\n  has text of type Text.\n  has child of type Spec.\n  has text of type Vec<u8>.\noperation Specification:\n  returns Spec.\n");
    assert!(check_types(&specs).is_empty());
    assert!(check_bodies(&specs).is_empty());
    assert!(c_record_layouts(&specs, CAbiTarget::LinuxX86_64)
        .unwrap()
        .is_empty());
}

#[test]
fn cycles_and_exponential_size_overflow_are_rejected() {
    for source in [
        "entity A:\n  layout \"C\".\n  has next of type A.\n",
        "entity A:\n  layout \"C\".\n  has next of type B.\nentity B:\n  layout \"C\".\n  has next of type A.\n",
    ] {
        let errors = c_record_layouts(&ir(source), CAbiTarget::LinuxX86_64).unwrap_err();
        assert!(errors.iter().any(|d| d.message.contains("cyclic")));
    }
    let mut source = "entity R0:\n  layout \"C\".\n  has value of type u64.\n".to_owned();
    for index in 1..=64 {
        let previous = index - 1;
        source.push_str(&format!("entity R{index}:\n  layout \"C\".\n  has a of type R{previous}.\n  has b of type R{previous}.\n"));
    }
    let errors = c_record_layouts(&ir(&source), CAbiTarget::LinuxX86_64).unwrap_err();
    assert!(errors.iter().any(|d| d.message.contains("overflows")));
}

#[test]
fn layout_dependency_traversal_is_iterative() {
    let mut source = "entity R0:\n  layout \"C\".\n  has value of type u8.\n".to_owned();
    for index in 1..2000 {
        source.push_str(&format!(
            "entity R{index}:\n  layout \"C\".\n  has value of type R{}.\n",
            index - 1
        ));
    }
    let layouts = c_record_layouts(&ir(&source), CAbiTarget::LinuxX86_64).unwrap();
    assert_eq!(layouts.len(), 2000);
    assert_eq!(layouts["R1999"].size, 1);
}

#[test]
fn primitive_record_collisions_fail_for_source_and_raw_ir() {
    assert!(
        check_types(&ir("entity Text:\n  layout \"C\".\n  has x of type u8.\n"))
            .iter()
            .any(|d| d.message.contains("primitive"))
    );
    let mut raw = ir("entity R:\n  layout \"C\".\n  has x of type u8.\n");
    let mut record = raw.entities.remove("R").unwrap();
    record.name = "u64".into();
    raw.entities.insert("u64".into(), record);
    assert!(c_record_layouts(&raw, CAbiTarget::LinuxX86_64)
        .unwrap_err()
        .iter()
        .any(|d| d.message.contains("primitive")));
}

#[test]
fn constructor_field_address_and_reflection_typing() {
    let ir = ir(&format!("{RECORDS}operation Make:\n  returns i32.\n  effects: UnsafeMemory.\n  body:\n    let mut value = Outer(true, Inner(255, -2147483648), 65535).\n    let pointer = address(value).\n    let size = size_of(Outer).\n    let alignment = align_of(Inner).\n    let offset = offset_of(Outer, \"inner\").\n    set value = Outer(false, Inner(0, 2147483647), 0).\n    return value.inner.wide.\n"));
    assert!(check_types(&ir).is_empty());
    assert!(check_bodies(&ir).is_empty(), "{:?}", check_bodies(&ir));
    assert!(check_effects(&ir).is_empty());
}

#[test]
fn constructors_reject_arity_ranges_and_wrong_record_types() {
    for expression in [
        "Inner()",
        "Inner(1, 2, 3)",
        "Inner(256, 0)",
        "Inner(0, 2147483648)",
        "Outer(true, Inner(0, 0), -1)",
        "Outer(true, Outer(true, Inner(0, 0), 0), 0)",
    ] {
        let ir = ir(&format!(
            "{RECORDS}operation F:\n  body:\n    {expression}.\n"
        ));
        assert!(!check_bodies(&ir).is_empty(), "{expression}");
    }
    let ir = ir(&format!("{RECORDS}operation F:\n  body:\n    let wide = 1.\n    Inner(wide, 0).\n    let mut value = Inner(0, 0).\n    set value = Outer(true, Inner(0, 0), 0).\n"));
    assert_eq!(
        check_bodies(&ir)
            .iter()
            .filter(|d| d.code == "B107")
            .count(),
        2
    );
}

#[test]
fn reflection_operands_are_types_not_locals_and_fail_closed() {
    for expression in [
        "size_of()",
        "size_of(Inner, 0)",
        "size_of(1)",
        "size_of(i64)",
        "size_of(Missing)",
        "size_of(value)",
        "offset_of(Inner, value)",
        "offset_of(Inner, \"missing\")",
        "offset_of(Inner)",
        "align_of(Inner(0, 0))",
    ] {
        let ir = ir(&format!(
            "{RECORDS}operation F:\n  body:\n    let value = Inner(0, 0).\n    {expression}.\n"
        ));
        let diagnostics = check_bodies(&ir);
        assert_eq!(diagnostics.len(), 1, "{expression}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code, "B108");
    }
}

#[test]
fn imported_operations_require_both_effects_at_declaration_and_call() {
    let missing = ir("operation Foreign:\n  imports \"C\" as \"foreign\".\n  returns i16.\noperation Caller:\n  returns i16.\n  body:\n    return Foreign().\n");
    assert!(check_types(&missing).is_empty());
    assert!(check_bodies(&missing).is_empty());
    let diagnostics = check_effects(&missing);
    assert_eq!(diagnostics.len(), 4);
    assert!(diagnostics.iter().all(|d| d.code == "EFF203"));
    let ir = ir("operation Foreign:\n  imports \"C\" as \"foreign\".\n  returns i16.\n  effects: SystemCall, UnsafeMemory.\noperation Caller:\n  returns i16.\n  effects: SystemCall, UnsafeMemory.\n  body:\n    return Foreign().\n");
    assert!(check_effects(&ir).is_empty());
}

#[test]
fn imported_operations_cannot_have_bodies_responses_or_exports() {
    for body in ["  body:\n    return 1.\n", "  responds with \"text\".\n"] {
        let ir = ir(&format!(
            "operation F:\n  imports \"C\" as \"foreign\".\n{body}"
        ));
        assert!(check_types(&ir).iter().any(|d| d.code == "E2011"));
    }
    let mut raw = ir("operation F:\n  imports \"C\" as \"foreign\".\n");
    raw.operations.get_mut("F").unwrap().c_export = Some("exported".into());
    assert!(check_types(&raw).iter().any(|d| d.code == "E2011"));
}

#[test]
fn all_integer_casts_are_reserved_integer_only_and_keep_width() {
    for ty in [
        "i8", "i16", "i32", "i64", "isize", "u8", "u16", "u32", "u64", "usize",
    ] {
        let source = format!("operation F:\n  accepts n of type i64.\n  returns {ty}.\n  body:\n    return {ty}(n).\n");
        assert!(check_bodies(&ir(&source)).is_empty(), "{ty}");
        let source = format!("operation F:\n  body:\n    {ty}(true).\n    {ty}(\"text\").\n");
        assert_eq!(check_bodies(&ir(&source)).len(), 2, "{ty}");
        let (file, diagnostics) = sal_syntax::parse(&format!("operation {ty}:\n  returns i64.\n"));
        assert!(diagnostics.is_empty());
        assert_eq!(build(&file).1[0].code, "E1003");
    }
    for name in ["size_of", "align_of", "offset_of"] {
        let (file, _) = sal_syntax::parse(&format!("operation {name}:\n  returns i64.\n"));
        assert_eq!(build(&file).1[0].code, "E1003");
    }
}

#[test]
fn narrow_contextual_literals_check_both_range_boundaries() {
    for (ty, minimum, maximum) in [
        ("i8", -128i64, 127i64),
        ("i16", -32768, 32767),
        ("i32", -2147483648, 2147483647),
        ("u8", 0, 255),
        ("u16", 0, 65535),
        ("u32", 0, 4294967295),
    ] {
        for value in [minimum, maximum] {
            let source = format!("operation F:\n  returns {ty}.\n  body:\n    return {value}.\n");
            assert!(check_bodies(&ir(&source)).is_empty(), "{ty}({value})");
        }
        for value in [minimum - 1, maximum + 1] {
            let source = format!("operation F:\n  returns {ty}.\n  body:\n    return {value}.\n");
            assert_eq!(check_bodies(&ir(&source))[0].code, "B102", "{ty}({value})");
            // Explicit casts retain their checked runtime semantics even for
            // known failing constants; they are not implicit coercions.
            let source =
                format!("operation F:\n  returns {ty}.\n  body:\n    return {ty}({value}).\n");
            assert!(check_bodies(&ir(&source)).is_empty(), "{ty}({value})");
        }
    }
}
