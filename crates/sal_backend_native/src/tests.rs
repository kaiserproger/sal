use super::*;

fn ir(source: &str) -> Ir {
    let (file, diagnostics) = sal_syntax::parse(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (ir, diagnostics) = sal_ir::build(&file);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    ir
}

// Native rejection may come from the shared pre-native passes (which
// emit_native re-runs and reports) or from native lowering itself.
fn rejected(source: &str, target: NativeTarget, code: &str) {
    let (file, diagnostics) = sal_syntax::parse(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let errors =
        emit_native(&sal_ir::build(&file).0, target).expect_err("unsupported program was accepted");
    assert!(
        errors.iter().any(|error| error.code == code),
        "expected {code}: {errors:?}"
    );
}

#[test]
fn rejects_missing_bodies_results_and_partial_returns() {
    rejected(
        "operation Main:\n    returns Text.\n",
        NativeTarget::Executable,
        "N103",
    );
    rejected(
        "operation Main:\n    body:\n        return \"no declared result\".\n",
        NativeTarget::Executable,
        "N100",
    );
    rejected("operation Main:\n    returns Text.\n    body:\n        if true:\n            return \"only one branch\".\n", NativeTarget::Executable, "B106");
}

#[test]
fn validates_types_bodies_and_duplicate_top_level_names_itself() {
    rejected(
        "operation Main:\n    returns Missing.\n    body:\n        return 1.\n",
        NativeTarget::Executable,
        "E2001",
    );
    rejected(
        "operation Main:\n    returns Text.\n    body:\n        return unknown.\n",
        NativeTarget::Executable,
        "B100",
    );
    rejected(
        "operation Main:\n    returns Text.\n    body:\n        return 1.\n",
        NativeTarget::Executable,
        "B102",
    );
    let (file, diagnostics) = sal_syntax::parse("operation Main:\n    returns Text.\n    responds with \"a\".\noperation Main:\n    returns Text.\n    responds with \"b\".\n");
    assert!(diagnostics.is_empty());
    let (ir, _) = sal_ir::build(&file);
    let errors = emit_native(&ir, NativeTarget::Executable).unwrap_err();
    assert!(errors.iter().any(|error| error.code == "E1001"));
}

#[test]
fn refuses_server_for_and_foreign_or_aggregate_operations() {
    rejected(
        "server Web:\n    listens on port 8080.\n    speaks HTTP/1.\n",
        NativeTarget::Executable,
        "N107",
    );
    rejected("operation Main:\n    returns Text.\n    body:\n        for item in \"nope\":\n            item.\n        return \"end\".\n", NativeTarget::Executable, "N108");
    rejected("operation Main:\n    returns Text.\n    body:\n        printf(\"no foreign imports\").\n        return \"end\".\n", NativeTarget::Executable, "B101");
    rejected(
        "operation Main:\n    returns Word.\n    responds with \"word\".\n",
        NativeTarget::Executable,
        "N100",
    );
    rejected("operation Main:\n    returns Text.\n    body:\n        let float = 1.25.\n        return \"no floats\".\n", NativeTarget::Executable, "N100");
}

#[test]
fn export_boundary_rejects_unsafe_types_contracts_effects_and_duplicates() {
    rejected("operation Main:\n    exports \"C\" as \"sal_text\".\n    returns Text.\n    responds with \"unsafe span\".\n", NativeTarget::StaticLibrary, "N100");
    rejected("operation Buf:\n    exports \"C\" as \"sal_buf\".\n    accepts owner of type Buffer.\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N100");
    rejected("operation Held:\n    exports \"C\" as \"sal_held\".\n    accepts slot of type Borrow<Buffer>.\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N100");
    // Header contracts are lowered to ordinary guards by the declarations pass:
    // a violated bare `requires:` is a runtime trap, not a native rejection.
    let program = emit_native(&ir("operation Main:\n    returns Text.\n    requires:\n        false.\n    responds with \"checked\".\n"), NativeTarget::Executable).unwrap();
    assert!(program.assembly.contains("ud2"));
    // Contract conditions must still type-check as bool.
    rejected("operation Main:\n    returns Text.\n    requires:\n        1.\n    responds with \"mistyped\".\n", NativeTarget::Executable, "DEC204");
    rejected("operation Helper:\n    returns i64.\n    effects: HTTPAccess.\n    body:\n        return 2.\noperation Main:\n    returns Text.\n    responds with \"ignored helper still rejected\".\n", NativeTarget::Executable, "N104");
    rejected(
        "operation Only:\n    returns i64.\n    body:\n        return 1.\n",
        NativeTarget::StaticLibrary,
        "N106",
    );
}

#[test]
fn memory_disjoint_guards_view_bytes_locals_of_the_same_root() {
    // The memory pass guards a new mutable window against every live span
    // local of the same root with `view(existing)`; `existing` may be a plain
    // Bytes result (here a Static-rooted helper return) and must lower.
    let source = "operation Line:\n    accepts status of type i64.\n    returns Bytes.\n    body:\n        if status == 1:\n            return bytes(\"a\").\n        return bytes(\"\").\noperation Fill:\n    accepts status of type i64.\n    accepts scratch of type MutBytes.\n    returns i64.\n    body:\n        let line = Line(status).\n        if len(line) == 0:\n            return -22.\n        let window = slice_mut(scratch, usize(0), len(scratch)).\n        borrow_end(window).\n        return 0.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n";
    emit_native(&ir(source), NativeTarget::Executable).unwrap();
}

#[test]
fn break_free_while_true_diverges_but_breaking_loops_still_fall_through() {
    emit_native(
        &ir("operation Main:\n    returns i64.\n    body:\n        let mut i = 0.\n        while true:\n            if i > 3:\n                return i.\n            set i = i + 1.\n"),
        NativeTarget::Executable,
    )
    .unwrap();
    // A break reaches the code after the loop, which has no return.
    rejected("operation Main:\n    returns i64.\n    body:\n        while true:\n            break.\n", NativeTarget::Executable, "B106");
    // A break in a nested loop exits only that loop; the outer one diverges.
    emit_native(
        &ir("operation Main:\n    returns i64.\n    body:\n        while true:\n            while true:\n                break.\n            return 1.\n"),
        NativeTarget::Executable,
    )
    .unwrap();
}

#[test]
fn borrowed_buffer_params_support_non_consuming_owner_operations_only() {
    let fill = "operation Fill:\n    accepts arena of type Buffer.\n    borrows arena.\n    returns i64.\n    body:\n        let span = borrow_mut(arena, usize(0), usize(4)).\n        put(span, usize(0), u8(7)).\n        borrow_end(span).\n        let head = view(arena).\n        let size = len(arena).\n        borrow_end(head).\n        return i64(size).\n";
    // The runtime allocator is supplied by the CLI source loader, so the
    // unit fixture only exercises the borrowing callee (end-to-end: native_memory).
    let main = "operation Main:\n    returns i64.\n    body:\n        return 0.\n";
    emit_native(&ir(&format!("{fill}{main}")), NativeTarget::Executable).unwrap();
    // Dropping through a borrow is consuming and stays rejected.
    rejected("operation Fill:\n    accepts arena of type Buffer.\n    borrows arena.\n    returns i64.\n    effects: SystemCall.\n    body:\n        buffer_drop(arena).\n        return 0.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "MEM203");
}

#[test]
fn void_procedures_fall_through_but_never_bind_or_take_void() {
    // Void procedures may fall through with no-return expression statements.
    let source = "operation DoWork:\n    exports \"C\" as \"sal_do_work\".\n    effects: Pure.\n    body:\n        1.\n";
    let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
    assert!(program.header.unwrap().contains("void sal_do_work(void);"));
    // Void values cannot be bound.
    rejected("operation Store:\n    effects: UnsafeMemory.\n    body:\n        store8(usize(0), u8(0)).\noperation Main:\n    returns Text.\n    body:\n        let value = Store().\n        return \"bad\".\n", NativeTarget::Executable, "B108");
    // Void values cannot be returned where a value is expected, and value
    // operations cannot return empty.
    rejected("operation Store:\n    effects: UnsafeMemory.\n    body:\n        store8(usize(0), u8(0)).\noperation Main:\n    returns Text.\n    body:\n        return Store().\n", NativeTarget::Executable, "B102");
    // Void is absence-of-returns, not a declarable type: `of type Void` is E2001.
    rejected("operation TakesVoid:\n    accepts nothing of type Void.\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::Executable, "E2001");
}

#[test]
fn span_and_entry_selection_follow_machine_contract() {
    // Stack spills are accepted: four spans now execute with order intact.
    let program = emit_native(
        &ir("operation TakeFour:\n    accepts a of type Bytes.\n    accepts b of type Bytes.\n    accepts c of type Bytes.\n    accepts d of type Bytes.\n    returns i64.\n    body:\n        return i64(len(a)) + i64(len(b)) + i64(len(c)) + i64(len(d)).\noperation Main:\n    returns i64.\n    body:\n        return TakeFour(bytes(\"a\"), bytes(\"bb\"), bytes(\"ccc\"), bytes(\"dddd\")).\n"),
        NativeTarget::Executable,
    )
    .unwrap();
    assert!(program.header.is_none());
    // Bytes spans never cross the C boundary.
    rejected("operation Bad:\n    exports \"C\" as \"sal_bad\".\n    returns Bytes.\n    body:\n        return bytes(\"x\").\n", NativeTarget::StaticLibrary, "N100");
    // A sole non-Main i64 operation is not a fallback entrypoint.
    rejected(
        "operation Other:\n    returns i64.\n    body:\n        return 1.\n",
        NativeTarget::Executable,
        "N105",
    );
    // A Void-only program has no executable entrypoint.
    rejected(
        "operation Quiet:\n    effects: Pure.\n    body:\n        1.\n",
        NativeTarget::Executable,
        "N105",
    );
    // Main() -> i64 is an accepted entrypoint.
    let program = emit_native(
        &ir("operation Main:\n    returns i64.\n    body:\n        return 3.\n"),
        NativeTarget::Executable,
    )
    .unwrap();
    assert!(program.header.is_none());
    assert!(program.assembly.contains("movl $60, %eax"));
}

#[test]
fn syscall_arity_effects_and_reserved_names_follow_contract() {
    // Syscall takes exactly seven machineword arguments.
    rejected("operation Main:\n    returns Text.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        syscall(1, 0, 0, 0, 0, 0).\n        return \"bad\".\n", NativeTarget::Executable, "B101");
    rejected("operation Main:\n    returns Text.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        syscall(1, 0, 0, 0, 0, 0, 0, 0).\n        return \"bad\".\n", NativeTarget::Executable, "B101");
    rejected("operation Main:\n    returns Text.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        syscall(1, 0, 0, 0, 0, 0, false).\n        return \"bad\".\n", NativeTarget::Executable, "B108");
    // Raw syscall requires both capabilities; either half alone fails closed.
    rejected("operation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        return syscall(1, 0, 0, 0, 0, 0, 0).\n", NativeTarget::Executable, "EFF203");
    rejected("operation Main:\n    returns i64.\n    effects: UnsafeMemory.\n    body:\n        return syscall(1, 0, 0, 0, 0, 0, 0).\n", NativeTarget::Executable, "EFF203");
    rejected("operation Main:\n    returns i64.\n    body:\n        return syscall(1, 0, 0, 0, 0, 0, 0).\n", NativeTarget::Executable, "EFF203");
    // Pure wrappers calling syscall fail the effect check.
    rejected("operation Wrapper:\n    returns i64.\n    effects: Pure.\n    body:\n        return syscall(1, 0, 0, 0, 0, 0, 0).\noperation Main:\n    returns Text.\n    responds with \"pure wrapper still checked\".\n", NativeTarget::Executable, "EFF203");
    // Pure combined with another effect remains EFF202.
    rejected("operation Bad:\n    returns i64.\n    effects: Pure, SystemCall.\n    body:\n        return 1.\n", NativeTarget::Executable, "EFF202");
    // C exports reject enforced effects; non-exports may declare them.
    rejected("operation Exported:\n    exports \"C\" as \"sal_exported\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N104");
    rejected("operation Exported:\n    exports \"C\" as \"sal_unknown\".\n    returns i64.\n    effects: DatabaseAccess.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N104");
    let program = emit_native(
        &ir("operation Helper:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        return 1.\noperation Main:\n    returns Text.\n    responds with \"unused effects allowed\".\n"),
        NativeTarget::Executable,
    )
    .unwrap();
    assert!(program.assembly.contains(".Lsal_fn_"));
    // Intrinsic names are reserved even as declarations.
    for name in [
        "len",
        "bytes",
        "byte",
        "slice",
        "usize",
        "i64",
        "u8",
        "syscall",
        "address",
        "bytes_at",
        "load8",
        "store8",
        "buffer",
        "buffer_drop",
        "borrow_mut",
        "slice_mut",
        "view",
        "put",
        "borrow_end",
        "borrow",
        "text",
        "SalContractAssert",
        "SalMemoryAssertDisjoint",
    ] {
        let (file, diagnostics) =
            sal_syntax::parse(&format!("operation {name}:\n    returns i64.\n"));
        assert!(diagnostics.is_empty());
        let (ir, _) = sal_ir::build(&file);
        let errors = emit_native(&ir, NativeTarget::Executable).unwrap_err();
        assert!(
            errors.iter().any(|error| error.code == "E1003"),
            "expected E1003 for {name}: {errors:?}"
        );
    }
}

#[test]
fn stack_scalar_arguments_are_accepted_in_order() {
    let program = emit_native(
        &ir("operation TakeNine:\n    accepts a0 of type i64.\n    accepts a1 of type i64.\n    accepts a2 of type i64.\n    accepts a3 of type i64.\n    accepts a4 of type i64.\n    accepts a5 of type i64.\n    accepts a6 of type i64.\n    accepts a7 of type i64.\n    accepts a8 of type i64.\n    returns i64.\n    body:\n        return a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8.\noperation Main:\n    returns i64.\n    body:\n        return TakeNine(1, 2, 3, 4, 5, 6, 7, 8, 9).\n"),
        NativeTarget::Executable,
    )
    .unwrap();
    assert!(program.header.is_none());
}

#[test]
fn selects_main_and_rejects_ambiguous_entrypoints() {
    let source = "operation Other:\n    returns Text.\n    responds with \"other\".\noperation Main:\n    returns Text.\n    responds with \"main\".\n";
    let program = emit_native(&ir(source), NativeTarget::Executable).unwrap();
    assert!(program
        .assembly
        .contains("_start:\n    andq $-16, %rsp\n    call .Lsal_fn_0"));
    rejected("operation One:\n    returns Text.\n    responds with \"one\".\noperation Two:\n    returns Text.\n    responds with \"two\".\n", NativeTarget::Executable, "N105");
}

#[test]
fn library_header_describes_only_explicit_scalar_exports() {
    let source = "operation Hidden:\n    returns i64.\n    body:\n        return 7.\noperation Total:\n    exports \"C\" as \"sal_total\".\n    accepts left of type i64.\n    accepts right of type i64.\n    returns i64.\n    effects: Pure.\n    body:\n        return Hidden() + left + right.\noperation Equal:\n    exports \"C\" as \"sal_equal\".\n    accepts left of type usize.\n    accepts right of type usize.\n    returns bool.\n    body:\n        return left == right.\n";
    let ir = ir(source);
    let first = emit_native(&ir, NativeTarget::StaticLibrary).unwrap();
    let second = emit_native(&ir, NativeTarget::StaticLibrary).unwrap();
    assert_eq!(first.assembly, second.assembly);
    let header = first.header.unwrap();
    assert!(header.contains("int64_t sal_total(int64_t arg0, int64_t arg1);"));
    assert!(header.contains("bool sal_equal(size_t arg0, size_t arg1);"));
    assert!(header.contains("not C ABI safe"));
    assert!(!header.contains("Hidden"));
    assert!(!first.assembly.contains(".globl Hidden"));
    assert!(!first.assembly.contains("_start"));
    assert!(!first.assembly.contains("syscall"));
    assert!(first.assembly.contains("jo .Lsal_trap_"));
    assert!(first.assembly.contains(".note.GNU-stack"));
}

#[test]
fn unrelated_library_headers_have_distinct_deterministic_guards() {
    let first = ir("operation First:\n    exports \"C\" as \"sal_first\".\n    returns i64.\n    body:\n        return 1.\n");
    let second = ir("operation Second:\n    exports \"C\" as \"sal_second\".\n    returns i64.\n    body:\n        return 2.\n");
    let first_header = emit_native(&first, NativeTarget::StaticLibrary)
        .unwrap()
        .header
        .unwrap();
    let second_header = emit_native(&second, NativeTarget::StaticLibrary)
        .unwrap()
        .header
        .unwrap();
    assert_ne!(first_header.lines().next(), second_header.lines().next());
    assert_eq!(
        first_header,
        emit_native(&first, NativeTarget::StaticLibrary)
            .unwrap()
            .header
            .unwrap()
    );
}

#[test]
fn rejects_oversized_record_frame_without_huge_allocation() {
    let mut source = String::from("entity R0:\n    layout \"C\".\n    has value of type u64.\n");
    for index in 1..=32 {
        let previous = index - 1;
        source.push_str(&format!("entity R{index}:\n    layout \"C\".\n    has a of type R{previous}.\n    has b of type R{previous}.\n"));
    }
    source.push_str("operation Main:\n    returns i64.\n    body:\n        return 0.\n");
    rejected(&source, NativeTarget::Executable, "N109");
}

#[test]
fn rejects_deeply_nested_malformed_reflection_without_stack_overflow() {
    let mut expression = String::from("0");
    for _ in 0..300 {
        expression = format!("size_of({expression})");
    }
    // Malformed operand: an integer quizzes a type-only intrinsic.
    let source = format!("entity R:\n    layout \"C\".\n    has value of type u8.\noperation Main:\n    returns i64.\n    body:\n        return {expression}.\n");
    let (file, diagnostics) = sal_syntax::parse(&source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    let (ir, _) = sal_ir::build(&file);
    let errors = emit_native(&ir, NativeTarget::Executable).expect_err("deep nesting was accepted");
    assert!(
        errors.iter().any(|error| error.code == "N109"),
        "{errors:?}"
    );
}

#[test]
fn rejects_loop_control_outside_loops() {
    rejected(
        "operation Main:\n    returns i64.\n    body:\n        break.\n        return 0.\n",
        NativeTarget::Executable,
        "B111",
    );
    rejected(
        "operation Main:\n    returns i64.\n    body:\n        continue.\n        return 0.\n",
        NativeTarget::Executable,
        "B111",
    );
}

#[test]
fn short_circuit_rhs_stays_statically_checked_and_loop_jumps_do_not_return() {
    rejected("operation Touch:\n    returns bool.\n    effects: UnsafeMemory.\n    body:\n        store8(usize(0), u8(1)).\n        return true.\noperation Main:\n    returns i64.\n    effects: Pure.\n    body:\n        if false && Touch():\n            return 1.\n        return 0.\n", NativeTarget::Executable, "EFF203");
    // `break` leaves the loop and falls off the end; `continue` is a break-free
    // infinite loop that diverges, matching the sal_ir return-path rule.
    rejected("operation Main:\n    returns i64.\n    body:\n        while true:\n            break.\n", NativeTarget::Executable, "B106");
    emit_native(
        &ir("operation Main:\n    returns i64.\n    body:\n        while true:\n            continue.\n"),
        NativeTarget::Executable,
    )
    .unwrap();
}

#[test]
fn rejects_conflicting_import_and_export_symbols() {
    let import = "operation Foreign:\n    imports \"C\" as \"same_symbol\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n";
    for second in [
        "operation Other:\n    imports \"C\" as \"same_symbol\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n",
        "operation Other:\n    exports \"C\" as \"same_symbol\".\n    returns i64.\n    body:\n        return 1.\n",
    ] {
        let source = format!("{import}{second}operation Main:\n    returns i64.\n    body:\n        return 0.\n");
        rejected(&source, NativeTarget::Executable, "N102");
    }
}

#[test]
fn rejects_nonbool_control_operands_and_rhs_type_errors() {
    rejected("operation Main:\n    returns i64.\n    body:\n        if 1:\n            return 1.\n        else:\n            return 0.\n", NativeTarget::Executable, "B103");
    rejected("operation Main:\n    returns i64.\n    body:\n        if true && 1:\n            return 1.\n        else:\n            return 0.\n", NativeTarget::Executable, "N100");
    rejected("operation Main:\n    returns i64.\n    body:\n        if false || unknown:\n            return 1.\n        else:\n            return 0.\n", NativeTarget::Executable, "B100");
    rejected(
        "operation Main:\n    returns i64.\n    body:\n        return !1.\n",
        NativeTarget::Executable,
        "N100",
    );
}

#[test]
fn memory_surface_rejects_forgery_comparison_and_c_escape() {
    // Buffer is an ABI pair, never a general span: no equality, no bytes/slice
    // projection, no address even inside unsafe, no C boundary.
    rejected("operation Main:\n    accepts owner of type Buffer.\n    returns bool.\n    body:\n        return owner == owner.\n", NativeTarget::Executable, "B105");
    rejected("operation Main:\n    accepts slot of type MutBytes.\n    returns bool.\n    body:\n        return slot == slot.\n", NativeTarget::Executable, "B105");
    rejected("operation Main:\n    accepts owner of type Buffer.\n    returns Bytes.\n    body:\n        return slice(owner, usize(0), usize(0)).\n", NativeTarget::Executable, "B107");
    rejected("operation Main:\n    accepts owner of type Buffer.\n    returns usize.\n    effects: UnsafeMemory.\n    body:\n        unsafe:\n            return address(owner).\n", NativeTarget::Executable, "B108");
    // MutBytes address is allowed only at an explicit unsafe raw OS boundary.
    rejected("operation Main:\n    accepts slot of type MutBytes.\n    returns usize.\n    body:\n        return address(slot).\n", NativeTarget::Executable, "EFF203");
    // Internal records never cross the C boundary, but address the stable
    // frame slot like C records inside ordinary code.
    rejected("entity Box:\n    has span of type Bytes.\noperation Main:\n    exports \"C\" as \"sal_box\".\n    accepts value of type Box.\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N100");
    // Vector/Map must be erased by collections lowering before native code.
    rejected("operation Main:\n    accepts items of type Vector<i64>.\n    returns i64.\n    body:\n        return vector_len(items).\n", NativeTarget::Executable, "N100");
    rejected(
        "operation Main:\n    returns i64.\n    body:\n        return vector_len(1).\n",
        NativeTarget::Executable,
        "N100",
    );
}

#[test]
fn rejects_import_export_metadata_problems() {
    // Import with a SAL body is an IR metadata error surfaced natively.
    rejected("operation Foreign:\n    imports \"C\" as \"foreign_impl\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        return 1.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "E2011");
    // Imports must declare both machine capabilities.
    rejected("operation Foreign:\n    imports \"C\" as \"foreign_impl\".\n    returns i64.\n    effects: SystemCall.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "N104");
    rejected("operation Foreign:\n    imports \"C\" as \"foreign_impl\".\n    returns i64.\n    effects: Pure.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "N104");
    // Imports can never be the executable entrypoint.
    rejected("operation Main:\n    imports \"C\" as \"foreign_main\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n", NativeTarget::Executable, "N105");
    // Reserved and C++ keyword identifiers fail closed.
    rejected("entity R:\n    layout \"C\".\n    has value of type u8.\noperation Foreign:\n    imports \"C\" as \"sal_record_R\".\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "N102");
    rejected("operation Exported:\n    exports \"C\" as \"INT64_C\".\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N102");
    rejected("operation Exported:\n    exports \"C\" as \"SIZE_MAX\".\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N102");
    rejected("entity R:\n    layout \"C\".\n    has INT32_MAX of type u8.\noperation Exported:\n    exports \"C\" as \"sal_ok\".\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N102");
    rejected("entity R:\n    layout \"C\".\n    has value of type u8.\noperation Exported:\n    exports \"C\" as \"class\".\n    returns i64.\n    body:\n        return 1.\n", NativeTarget::StaticLibrary, "N102");
    // Invalid marked records fail via shared layouts even when unused.
    rejected("entity Bad:\n    layout \"C\".\n    has value of type Text.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "E2010");
    // Bodyless non-import operations fail closed, including Void.
    rejected("operation Helper:\n    returns i64.\noperation Main:\n    returns i64.\n    body:\n        return Helper().\n", NativeTarget::Executable, "N103");
    rejected("operation Quiet:\n    effects: Pure.\noperation Main:\n    returns i64.\n    body:\n        return 0.\n", NativeTarget::Executable, "N103");
}
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod machine {
    use super::*;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Output};
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "sal-native-{}-{}",
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
    fn runs_recursive_calls_locals_scopes_text_spans_and_conditionals() {
        let source = r#"operation Sum:
    accepts n of type i64.
    returns i64.
    body:
        if n == 0:
            return 0.
        else:
            return n + Sum(n - 1).
operation Choose:
    accepts first of type Text.
    accepts second of type Text.
    accepts choose of type bool.
    returns Text.
    body:
        if choose:
            let result = first.
            return result.
        else:
            return second.
operation Main:
    returns Text.
    body:
        let answer = Sum(5).
        let result = Choose("hé\u{0}llo", "wrong", answer == 15).
        if len(result) == 7:
            if result != "different":
                return result.
            else:
                return "wrong equality".
        else:
            return "wrong byte length".
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert!(output.status.success(), "{:?}", output.status);
        assert_eq!(output.stdout, "hé\0llo\n".as_bytes());
    }

    #[test]
    fn mutable_slots_nested_scopes_and_long_while_reuse_frame() {
        let source = r#"operation Main:
    returns Text.
    body:
        let mut total = 0.
        let mut i = 0.
        while i < 200000:
            let shadow = i.
            if shadow == i:
                let inner = 1.
                if inner == 1:
                    set total = total + 1.
                else:
                    set total = total + 1000000.
            else:
                set total = total + 1000000.
            let outer = total.
            if outer == total:
                set i = i + 1.
            else:
                set i = i + 1000000.
        if total == 200000:
            if i == 200000:
                let mut x = 1.
                if true:
                    let mut x = 2.
                    set x = 3.
                    if x == 3:
                        x.
                    else:
                        return "bad inner".
                else:
                    return "bad branch".
                if x == 1:
                    return "ok".
                else:
                    return "bad shadow".
            else:
                return "bad count".
        else:
            return "bad total".
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert!(
            output.status.success(),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
        assert_eq!(output.stdout, b"ok\n");
    }

    #[test]
    fn i64_main_exits_with_status_and_no_output() {
        let (_directory, path) =
            executable("operation Main:\n    returns i64.\n    body:\n        return 20 + 22.\n");
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(42));
        assert!(output.stdout.is_empty());
    }

    #[test]
    fn signed_unsigned_mul_div_rem_and_comparisons() {
        let source = r#"operation SignedSize:
    accepts value of type isize.
    returns bool.
    body:
        if value < 0:
            if value / 2 == -3:
                return value % 2 == -1.
            else:
                return false.
        else:
            return false.
operation HighUnsigned:
    accepts value of type u64.
    returns bool.
    body:
        if value > 9223372036854775807:
            if value / 2 == 9223372036854775807:
                return value % 2 == 1.
            else:
                return false.
        else:
            return false.
operation Check:
    returns Text.
    body:
        if 6 * 7 == 42:
            if 20 / 3 == 6:
                if 20 % 3 == 2:
                    if 2 + 3 * 4 == 14:
                        if 0 - 7 + 10 == 3:
                            if 1 < 2:
                                if 2 <= 2:
                                    if 3 > 2:
                                        if 3 >= 3:
                                            if usize(6) * usize(7) == usize(42):
                                                if usize(20) / usize(3) == usize(6):
                                                    if usize(20) % usize(3) == usize(2):
                                                        if usize(1) < usize(2):
                                                            if usize(2) <= usize(2):
                                                                if usize(3) > usize(2):
                                                                    if usize(3) >= usize(3):
                                                                        if u8(6) * u8(7) == u8(42):
                                                                            if u8(20) / u8(4) == u8(5):
                                                                                if u8(20) % u8(6) == u8(2):
                                                                                    if u8(200) > u8(100):
                                                                                        if 0 - 5 < 0:
                                                                                            if SignedSize(-7):
                                                                                                if HighUnsigned(9223372036854775807 + 9223372036854775807 + 1):
                                                                                                    return "ok".
                                                                                                else:
                                                                                                    return "bad sdiv".
                                                                                            else:
                                                                                                return "bad slt".
                                                                                        else:
                                                                                            return "bad u8gt".
                                                                                    else:
                                                                                        return "bad u8rem".
                                                                                else:
                                                                                    return "bad u8div".
                                                                            else:
                                                                                return "bad u8mul".
                                                                        else:
                                                                            return "bad uge".
                                                                    else:
                                                                        return "bad ugt".
                                                                else:
                                                                    return "bad ule".
                                                            else:
                                                                return "bad ult".
                                                        else:
                                                            return "bad urem".
                                                    else:
                                                        return "bad udiv".
                                                else:
                                                    return "bad umul".
                                            else:
                                                return "bad ge".
                                        else:
                                            return "bad gt".
                                    else:
                                        return "bad le".
                                else:
                                    return "bad lt".
                            else:
                                return "bad addsub".
                        else:
                            return "bad prec".
                    else:
                        return "bad rem".
                else:
                    return "bad div".
            else:
                return "bad mul".
        else:
            return "bad entry".
operation Main:
    returns Text.
    body:
        return Check().
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert!(
            output.status.success(),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
        assert_eq!(output.stdout, b"ok\n");
    }

    #[test]
    fn div_rem_traps_cover_zero_and_signed_min() {
        for (ty, expression) in [
            ("i64", "10 / 0"),
            ("i64", "10 % 0"),
            ("u64", "10 / 0"),
            ("u64", "10 % 0"),
            ("usize", "usize(10) / usize(0)"),
            ("u8", "u8(1) / u8(0)"),
            ("i64", "-9223372036854775808 / (0 - 1)"),
            ("i64", "-9223372036854775808 % (0 - 1)"),
        ] {
            let source = format!("operation Div:\n    returns {ty}.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Div().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{ty}: {expression}");
            assert!(output.stdout.is_empty());
        }
    }

    #[test]
    fn u8_checked_arithmetic_and_conversions_trap() {
        // 200+55 is exactly 255 and must succeed; a nested 16*16 (256)
        // traps before any comparison executes.
        let (_directory, path) = executable(
            "operation Main:\n    returns Text.\n    body:\n        if u8(200) + u8(55) == u8(255):\n            if u8(1) + u8(2) == u8(3):\n                return \"ok\".\n            else:\n                return \"bad second\".\n        else:\n            return \"bad add\".\n",
        );
        let output = Command::new(path).output().unwrap();
        assert!(output.status.success(), "{:?}", output.status);
        assert_eq!(output.stdout, b"ok\n");
        let (_directory, path) = executable(
            "operation Main:\n    returns Text.\n    body:\n        if u8(16) * u8(16) == u8(0):\n            return \"unreachable\".\n        else:\n            return \"bad\".\n",
        );
        // 16*16 is 256 and must trap before any comparison runs.
        let output = Command::new(path).output().unwrap();
        assert_eq!(trap_signal(&output), Some(4));
        for expression in [
            "u8(255) + u8(1)",
            "u8(255) * u8(2)",
            "u8(0) - u8(1)",
            "u8(256)",
            "u8(0 - 1)",
            "u8(300)",
            "u8(usize(256))",
        ] {
            let source = format!("operation Convert:\n    returns u8.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Convert().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{expression}");
            assert!(output.stdout.is_empty());
        }
        // Negative-to-unsigned conversion traps for the wider word too.
        let source = "operation Convert:\n    returns usize.\n    body:\n        return usize(0 - 1).\noperation Main:\n    returns Text.\n    body:\n        Convert().\n        return \"must not run\".\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(trap_signal(&output), Some(4));
        assert!(output.stdout.is_empty());
        let (_directory, path) = executable("operation Main:\n    returns i64.\n    body:\n        return i64(usize(9223372036854775807) + usize(1)).\n");
        let output = Command::new(path).output().unwrap();
        assert_eq!(trap_signal(&output), Some(4));
        // In-range conversions succeed.
        let (_directory, path) = executable(
            "operation Main:\n    returns Text.\n    body:\n        if u8(255) == u8(usize(255)):\n            if usize(u8(255)) == usize(255):\n                if i64(u8(255)) == 255:\n                    return \"ok\".\n                else:\n                    return \"bad i64\".\n            else:\n                return \"bad usize\".\n        else:\n            return \"bad u8\".\n",
        );
        let output = Command::new(path).output().unwrap();
        assert!(output.status.success(), "{:?}", output.status);
        assert_eq!(output.stdout, b"ok\n");
    }

    #[test]
    fn bytes_views_bounds_equality_and_empty_endpoints() {
        let source = r#"operation Main:
    returns Text.
    body:
        let data = bytes("Hello").
        if len(data) == usize(5):
            if byte(data, 0) == u8(72):
                if byte(data, 1) == u8(101):
                    let part = slice(data, 1, 3).
                    if len(part) == usize(3):
                        if byte(part, 0) == u8(101):
                            if slice(data, 2, 0) == bytes(""):
                                if slice(data, 0, 0) == slice(data, 2, 0):
                                    if slice(bytes(""), 0, 0) == bytes(""):
                                        if bytes("abc") == bytes("abc"):
                                            if bytes("abc") != bytes("abd"):
                                                if bytes("a") != bytes("aa"):
                                                    if slice(bytes("zHelloz"), 1, 5) == data:
                                                        return "ok".
                                                    else:
                                                        return "bad full".
                                                else:
                                                    return "bad len".
                                            else:
                                                return "bad ne".
                                        else:
                                            return "bad eq".
                                    else:
                                        return "bad empty view".
                                else:
                                    return "bad empty eq".
                            else:
                                return "bad empty endpoint".
                        else:
                            return "bad slice byte".
                    else:
                        return "bad slice len".
                else:
                    return "bad byte1".
            else:
                return "bad byte0".
        else:
            return "bad len".
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert!(
            output.status.success(),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
        assert_eq!(output.stdout, b"ok\n");
        // Out-of-bounds reads and overlong slices trap; empty endpoints do not.
        let byte_traps = [
            "byte(bytes(\"hi\"), 2)",
            "byte(bytes(\"\"), 0)",
            "byte(bytes(\"hi\"), usize(9223372036854775807) + usize(9223372036854775807) + usize(1))",
        ];
        for expression in byte_traps {
            let source = format!("operation Probe:\n    returns u8.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Probe().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{expression}");
            assert!(output.stdout.is_empty());
        }
        let slice_traps = [
            "slice(bytes(\"hi\"), 3, 0)",
            "slice(bytes(\"hi\"), 0, 3)",
            "slice(bytes(\"hi\"), 1, 2)",
        ];
        for expression in slice_traps {
            let source = format!("operation Probe:\n    returns Bytes.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Probe().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{expression}");
            assert!(output.stdout.is_empty());
        }
        // Huge endpoints must trap in the slice comparison itself. (Checked
        // Add/Sub trap on overflow, so wrapping endpoints cannot be built
        // arithmetically; single huge literals pin the boundary logic.)
        for expression in [
            "slice(bytes(\"hi\"), usize(9223372036854775807), 1)",
            "slice(bytes(\"hi\"), 0, usize(9223372036854775807))",
        ] {
            let source = format!("operation Probe:\n    returns Bytes.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Probe().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{expression}");
            assert!(output.stdout.is_empty());
        }
    }

    #[test]
    fn syscall_seventh_argument_reaches_r9_with_file_backed_mmap() {
        // Anonymous mmap ignores its offset, so this test uses a file-backed
        // mapping where offset 0 succeeds and offset 1 deterministically fails
        // with EINVAL. The failing probe passes its offset through a nested
        // SAL call that clobbers every caller-saved register, proving both
        // seven-operand spills and r9 delivery.
        let source = r#"operation Ordered:
    accepts marker of type usize.
    accepts expected of type u8.
    accepts value of type i64.
    returns i64.
    effects: UnsafeMemory.
    body:
        if load8(marker) == expected:
            store8(marker, expected + 1).
            return value.
        else:
            return -1.
operation ClobberOne:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        syscall(1, 2, address("clobber"), len("clobber"), 0, 0, 0).
        return 1.
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let scratch = syscall(9, 0, 4096, 3, 34, -1, 0).
        if scratch < 0:
            return 10.
        else:
            let base = usize(scratch).
            store8(base, u8(47)).
            store8(base + usize(1), u8(100)).
            store8(base + usize(2), u8(101)).
            store8(base + usize(3), u8(118)).
            store8(base + usize(4), u8(47)).
            store8(base + usize(5), u8(122)).
            store8(base + usize(6), u8(101)).
            store8(base + usize(7), u8(114)).
            store8(base + usize(8), u8(111)).
            store8(base + usize(9), u8(0)).
            let fd = syscall(2, base, 0, 0, 0, 0, 0).
            if fd < 0:
                return 11.
            else:
                let good = syscall(9, 0, 4096, 1, 2, fd, 0).
                if good < 0:
                    return 12.
                else:
                    store8(base, u8(0)).
                    let bad = syscall(Ordered(base, 0, 9), Ordered(base, 1, 0), Ordered(base, 2, 4096), Ordered(base, 3, 1), Ordered(base, 4, 2), Ordered(base, 5, fd), Ordered(base, 6, ClobberOne())).
                    if bad == 0 - 22:
                        if load8(base) == u8(7):
                            return 0.
                        else:
                            return 14.
                    else:
                        return 13.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(0),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
        assert!(output.stdout.is_empty());
    }

    #[test]
    fn syscall_mmap_store_load_address_bytes_at_and_binary_output() {
        let source = r#"operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let region = syscall(9, 0, 4096, 3, 34, -1, 0).
        if region < 0:
            return 99.
        else:
            let base = usize(region).
            store8(base, u8(65)).
            store8(base + usize(1), u8(0)).
            store8(base + usize(2), u8(66)).
            store8(base + usize(3), u8(255)).
            store8(base + usize(4), u8(10)).
            let written = syscall(1, 1, base, 5, 0, 0, 0).
            if written == 5:
                if load8(base) == u8(65):
                    if load8(base + usize(3)) == u8(255):
                        let view = bytes_at(base, usize(5)).
                        if len(view) == usize(5):
                            if byte(view, 1) == u8(0):
                                if view == bytes_at(base, usize(5)):
                                    let txt = bytes("hello").
                                    let addr = address(txt).
                                    if addr == usize(0):
                                        return 31.
                                    else:
                                        let back = bytes_at(addr, len(txt)).
                                        if back == txt:
                                            if len(txt) == usize(5):
                                                if byte(txt, 1) == u8(101):
                                                    return 7.
                                                else:
                                                    return 32.
                                            else:
                                                return 33.
                                        else:
                                            return 34.
                                else:
                                    return 21.
                            else:
                                return 22.
                        else:
                            return 23.
                    else:
                        return 24.
                else:
                    return 25.
            else:
                return 26.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(7), "{:?}", output.status);
        assert_eq!(output.stdout, [65, 0, 66, 255, 10]);
    }

    #[test]
    fn text_comparison_checks_bytes_not_just_lengths() {
        let source = "operation Main:\n    returns Text.\n    body:\n        if \"same\" == \"diff\":\n            return \"wrong\".\n        else:\n            if \"same\" != \"same\":\n                return \"wrong\".\n            else:\n                if \"\" == \"\":\n                    return \"correct\".\n                else:\n                    return \"wrong\".\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"correct\n");
    }

    #[test]
    fn arithmetic_overflow_traps_instead_of_wrapping() {
        use std::os::unix::process::ExitStatusExt;
        for (ty, expression) in [
            ("i64", "9223372036854775807 + 1"),
            ("i64", "-9223372036854775808 - 1"),
            ("u64", "0 - 1"),
            ("u64", "9223372036854775807 + 9223372036854775807 + 2"),
            ("i64", "9223372036854775807 * 2"),
            ("u64", "9223372036854775807 * 3"),
            ("isize", "-9223372036854775808 * (0 - 1)"),
        ] {
            let source = format!("operation Overflow:\n    returns {ty}.\n    body:\n        return {expression}.\noperation Main:\n    returns Text.\n    body:\n        Overflow().\n        return \"must not run\".\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(output.status.signal(), Some(4), "{ty}: {expression}");
            assert!(output.stdout.is_empty());
        }
    }

    #[test]
    fn output_failure_exits_nonzero() {
        use std::process::Stdio;
        let (_directory, path) = executable(
            "operation Main:\n    returns Text.\n    responds with \"write failure\".\n",
        );
        let full = std::fs::OpenOptions::new()
            .write(true)
            .open("/dev/full")
            .unwrap();
        let status = Command::new(path)
            .stdout(Stdio::from(full))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(1));
    }

    #[test]
    fn static_library_links_to_real_c_and_has_only_explicit_global_exports() {
        let source = "operation Hidden:\n    accepts value of type i64.\n    returns i64.\n    body:\n        return value + 1.\noperation Total:\n    exports \"C\" as \"sal_total\".\n    accepts left of type i64.\n    accepts right of type i64.\n    returns i64.\n    body:\n        return Hidden(left) + right.\noperation Equal:\n    exports \"C\" as \"sal_equal\".\n    accepts left of type i64.\n    accepts right of type i64.\n    returns bool.\n    body:\n        return left == right.\noperation Not:\n    exports \"C\" as \"sal_not\".\n    accepts value of type bool.\n    returns bool.\n    body:\n        return value == false.\noperation Unsigned:\n    exports \"C\" as \"sal_unsigned\".\n    accepts left of type u64.\n    accepts right of type u64.\n    returns u64.\n    body:\n        return left + right.\noperation SignedSize:\n    exports \"C\" as \"sal_signed_size\".\n    accepts value of type isize.\n    returns isize.\n    body:\n        return value - 1.\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        std::fs::write(directory.0.join("sal.s"), program.assembly).unwrap();
        std::fs::write(directory.0.join("sal.h"), program.header.unwrap()).unwrap();
        std::fs::write(
            directory.0.join("caller.c"),
            r#"#include "sal.h"
int main(void) {
    return !(sal_total(20, 21) == 42 && sal_equal(-7, -7)
        && !sal_equal(-7, 7) && sal_not(false) && !sal_not(true)
        && sal_unsigned(UINT64_C(9223372036854775808), 1) == UINT64_C(9223372036854775809)
        && sal_signed_size(-4) == -5);
}
"#,
        )
        .unwrap();
        command("as", &["--64", "-o", "sal.o", "sal.s"], &directory.0);
        command("ar", &["rcsD", "libsal.a", "sal.o"], &directory.0);
        command(
            "cc",
            &[
                "-std=c11", "-Wall", "-Wextra", "-Werror", "caller.c", "libsal.a", "-o", "caller",
            ],
            &directory.0,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
        let symbols = command("nm", &["-g", "--defined-only", "sal.o"], &directory.0);
        let symbols = String::from_utf8(symbols.stdout).unwrap();
        let names: BTreeSet<_> = symbols
            .lines()
            .filter_map(|line| line.split_whitespace().last())
            .collect();
        assert_eq!(
            names,
            BTreeSet::from([
                "sal_equal",
                "sal_not",
                "sal_signed_size",
                "sal_total",
                "sal_unsigned"
            ])
        );
        let imports = command("nm", &["-u", "sal.o"], &directory.0);
        assert!(imports.stdout.is_empty(), "SAL library has runtime imports");
        // Exercise the ABI's unspecified upper bool argument bits explicitly.
        std::fs::write(directory.0.join("bool.s"), ".text\n.globl _start\n_start:\n    andq $-16, %rsp\n    movabsq $0x123456789abcde00, %rdi\n    call sal_not\n    cmpq $1, %rax\n    jne failure\n    movabsq $0x123456789abcde01, %rdi\n    call sal_not\n    testq %rax, %rax\n    jne failure\n    xorl %edi, %edi\n    jmp exit\nfailure:\n    movl $1, %edi\nexit:\n    movl $60, %eax\n    syscall\n.section .note.GNU-stack,\"\",@progbits\n").unwrap();
        command("as", &["--64", "-o", "bool.o", "bool.s"], &directory.0);
        command("ld", &["-o", "bool", "bool.o", "libsal.a"], &directory.0);
        assert!(Command::new(directory.0.join("bool"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn static_library_pure_u8_void_and_upper_bits() {
        let source = "operation Identity:\n    exports \"C\" as \"sal_id_u8\".\n    accepts value of type u8.\n    returns u8.\n    effects: Pure.\n    body:\n        return value.\noperation Sum:\n    exports \"C\" as \"sal_add_u8\".\n    accepts left of type u8.\n    accepts right of type u8.\n    returns u8.\n    effects: Pure.\n    body:\n        return left + right.\noperation Done:\n    exports \"C\" as \"sal_do_nothing\".\n    effects: Pure.\n    body:\n        1.\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        assert!(header.contains("uint8_t sal_id_u8(uint8_t arg0);"));
        assert!(header.contains("uint8_t sal_add_u8(uint8_t arg0, uint8_t arg1);"));
        assert!(header.contains("void sal_do_nothing(void);"));
        std::fs::write(directory.0.join("sal.s"), program.assembly).unwrap();
        std::fs::write(directory.0.join("sal.h"), header).unwrap();
        std::fs::write(
            directory.0.join("caller.c"),
            r#"#include "sal.h"
int main(void) {
    sal_do_nothing();
    return !(sal_id_u8(5) == 5 && sal_add_u8(200, 55) == 255);
}
"#,
        )
        .unwrap();
        command("as", &["--64", "-o", "sal.o", "sal.s"], &directory.0);
        command("ar", &["rcsD", "libsal.a", "sal.o"], &directory.0);
        command(
            "cc",
            &[
                "-std=c11", "-Wall", "-Wextra", "-Werror", "caller.c", "libsal.a", "-o", "caller",
            ],
            &directory.0,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
        let symbols = command("nm", &["-g", "--defined-only", "sal.o"], &directory.0);
        let symbols = String::from_utf8(symbols.stdout).unwrap();
        let names: BTreeSet<_> = symbols
            .lines()
            .filter_map(|line| line.split_whitespace().last())
            .collect();
        assert_eq!(
            names,
            BTreeSet::from(["sal_add_u8", "sal_do_nothing", "sal_id_u8"])
        );
        let imports = command("nm", &["-u", "sal.o"], &directory.0);
        assert!(imports.stdout.is_empty(), "SAL library has runtime imports");
        // Upper u8 argument bits are unspecified; only the low byte counts.
        std::fs::write(directory.0.join("u8.s"), ".text\n.globl _start\n_start:\n    andq $-16, %rsp\n    movabsq $0x123456789abcde05, %rdi\n    call sal_id_u8\n    cmpq $5, %rax\n    jne failure\n    movabsq $0x123456789abcff00, %rdi\n    movabsq $0x0000000000000005, %rsi\n    call sal_add_u8\n    cmpq $5, %rax\n    jne failure\n    xorl %edi, %edi\n    jmp exit\nfailure:\n    movl $1, %edi\nexit:\n    movl $60, %eax\n    syscall\n.section .note.GNU-stack,\"\",@progbits\n").unwrap();
        command("as", &["--64", "-o", "u8.o", "u8.s"], &directory.0);
        command("ld", &["-o", "u8", "u8.o", "libsal.a"], &directory.0);
        assert!(Command::new(directory.0.join("u8"))
            .status()
            .unwrap()
            .success());
        // u8 addition beyond 255 traps rather than wrapping.
        std::fs::write(directory.0.join("trap.s"), ".text\n.globl _start\n_start:\n    andq $-16, %rsp\n    movl $200, %edi\n    movl $56, %esi\n    call sal_add_u8\n    movl $1, %edi\n    movl $60, %eax\n    syscall\n.section .note.GNU-stack,\"\",@progbits\n").unwrap();
        command("as", &["--64", "-o", "trap.o", "trap.s"], &directory.0);
        command("ld", &["-o", "trap", "trap.o", "libsal.a"], &directory.0);
        let output = Command::new(directory.0.join("trap")).output().unwrap();
        assert_eq!(trap_signal(&output), Some(4));
    }

    fn archive_library(directory: &Path, assembly: &str, header: &str) {
        std::fs::write(directory.join("sal.s"), assembly).unwrap();
        std::fs::write(directory.join("sal.h"), header).unwrap();
        command("as", &["--64", "-o", "sal.o", "sal.s"], directory);
        command("ar", &["rcsD", "libsal.a", "sal.o"], directory);
        let imports = command("nm", &["-u", "sal.o"], directory);
        assert!(imports.stdout.is_empty(), "SAL library has runtime imports");
    }

    fn compile_freestanding(directory: &Path, name: &str, source: &str) {
        std::fs::write(directory.join(name), source).unwrap();
        let object = format!("{}.o", name.trim_end_matches(".s").trim_end_matches(".c"));
        match name.rsplit('.').next() {
            Some("c") => {
                command(
                    "cc",
                    &[
                        "-std=c11",
                        "-ffreestanding",
                        "-fno-stack-protector",
                        "-fno-pie",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        "-c",
                        name,
                        "-o",
                        &object,
                    ],
                    directory,
                );
            }
            _ => {
                command("as", &["--64", "-o", &object, name], directory);
            }
        }
    }

    fn link_executable(directory: &Path, objects: &[&str], output: &str) {
        let mut args = Vec::with_capacity(objects.len() + 3);
        args.extend_from_slice(objects);
        args.extend_from_slice(&["-o", output]);
        command("ld", &args, directory);
    }

    fn compile_c_main(directory: &Path, source: &str) {
        std::fs::write(directory.join("caller.c"), source).unwrap();
        command(
            "cc",
            &[
                "-std=c11", "-Wall", "-Wextra", "-Werror", "caller.c", "libsal.a", "-o", "caller",
            ],
            directory,
        );
    }

    #[test]
    fn narrow_signed_unsigned_argument_and_return_poison() {
        let source = "operation Neg8:\n    exports \"C\" as \"sal_neg8\".\n    accepts value of type i8.\n    returns i8.\n    effects: Pure.\n    body:\n        return 0 - value.\noperation Add16:\n    exports \"C\" as \"sal_add16\".\n    accepts left of type i16.\n    accepts right of type u16.\n    returns i32.\n    effects: Pure.\n    body:\n        return i32(left) + i32(right).\noperation Widen32:\n    exports \"C\" as \"sal_widen32\".\n    accepts value of type u32.\n    returns u64.\n    effects: Pure.\n    body:\n        return u64(value).\noperation Narrow32:\n    exports \"C\" as \"sal_narrow32\".\n    accepts value of type i64.\n    returns i32.\n    effects: Pure.\n    body:\n        return i32(value).\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        archive_library(&directory.0, &program.assembly, &header);
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
#include <stdint.h>
int main(void) {
    if (sal_neg8((int8_t)-5) != 5) return 1;
    if (sal_neg8((int8_t)127) != (int8_t)-127) return 2;
    if (sal_add16((int16_t)-300, (uint16_t)700) != 400) return 3;
    if (sal_add16((int16_t)-1, (uint16_t)65535) != 65534) return 4;
    if (sal_widen32(UINT32_C(4294967295)) != UINT64_C(4294967295)) return 5;
    if (sal_narrow32((int64_t)-2147483648) != (int32_t)-2147483648) return 6;
    return 0;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
        // Poisoned upper argument and return bits collapse to defined values.
        compile_freestanding(
            &directory.0,
            "poison.s",
            ".text\n.globl _start\n_start:\n    andq $-16, %rsp\n    movabsq $0xFFFFFFFFFFFFFFFB, %rdi\n    call sal_neg8\n    cmpq $5, %rax\n    jne failure\n    movabsq $0x12345678ABCDFED4, %rdi\n    movabsq $0xFFFFFFFF000002BC, %rsi\n    call sal_add16\n    cmpq $400, %rax\n    jne failure\n    movabsq $0xFFFFFFFFFFFFFFFF, %rdi\n    call sal_widen32\n    movabsq $4294967295, %rcx\n    cmpq %rcx, %rax\n    jne failure\n    movabsq $0xFFFFFFFF80000000, %rdi\n    call sal_narrow32\n    cmpq $-2147483648, %rax\n    jne failure\n    xorl %edi, %edi\n    jmp exit\nfailure:\n    movl $1, %edi\nexit:\n    movl $60, %eax\n    syscall\n.section .note.GNU-stack,\"\",@progbits\n",
        );
        link_executable(&directory.0, &["poison.o", "libsal.a"], "poison");
        assert!(Command::new(directory.0.join("poison"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn narrow_min_div_rem_traps_cover_all_widths() {
        let pairs = [
            ("i8", "-128", "0 - 1"),
            ("i16", "-32768", "0 - 1"),
            ("i32", "-2147483648", "0 - 1"),
            ("i64", "-9223372036854775808", "0 - 1"),
        ];
        for (ty, minimum, minus_one) in pairs {
            for operator in ["/", "%"] {
                let source = format!("operation Probe:\n    returns {ty}.\n    body:\n        return {minimum} {operator} ({minus_one}).\noperation Main:\n    returns i64.\n    body:\n        Probe().\n        return 0.\n");
                let (_directory, path) = executable(&source);
                let output = Command::new(path).output().unwrap();
                assert_eq!(trap_signal(&output), Some(4), "{ty} {operator}");
                assert!(output.stdout.is_empty());
            }
        }
        let traps = [
            ("i8", "127 + 1"),
            ("i8", "-128 - 1"),
            ("i16", "32767 + 1"),
            ("i16", "-32768 - 1"),
            ("i32", "2147483647 + 1"),
            ("i32", "-2147483648 - 1"),
            ("u16", "65535 + 1"),
            ("u16", "0 - 1"),
            ("u32", "4294967295 + 1"),
            ("u32", "0 - 1"),
            ("u16", "u16(70000 + 0)"),
            ("u32", "u32(0 - 1)"),
            ("i16", "i16(40000 + 0)"),
            ("i32", "i32(2147483648 + 0)"),
            ("i8", "64 * 2"),
            ("i16", "256 * 128"),
            ("i32", "65536 * 32768"),
            ("u16", "256 * 256"),
            ("u32", "65536 * 65536"),
            ("i8", "1 / 0"),
            ("i16", "1 / 0"),
            ("i32", "1 % 0"),
            ("u16", "1 / 0"),
            ("u32", "1 % 0"),
        ];
        for (ty, expression) in traps {
            let source = format!("operation Probe:\n    returns {ty}.\n    body:\n        return {expression}.\noperation Main:\n    returns i64.\n    body:\n        Probe().\n        return 0.\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{ty}: {expression}");
        }
    }

    #[test]
    fn narrow_cast_bounds_cover_signed_unsigned_min_and_minus_one() {
        let source = "operation Main:\n    returns i64.\n    body:\n        if i16(-32768) != -32768:\n            return 99.\n        if i16(32767) != 32767:\n            return 99.\n        if u16(65535) != 65535:\n            return 99.\n        if i32(-2147483648) != -2147483648:\n            return 99.\n        if i32(2147483647) != 2147483647:\n            return 99.\n        if u32(4294967295) != u32(4294967295):\n            return 99.\n        if i8(-128) != -128:\n            return 99.\n        if i8(127) != 127:\n            return 99.\n        if u8(255) != u8(255):\n            return 99.\n        if i16(u16(123)) != 123:\n            return 99.\n        if u16(i16(123)) != u16(123):\n            return 99.\n        if i32(u32(123)) != 123:\n            return 99.\n        if u32(i32(123)) != u32(123):\n            return 99.\n        return 7.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(7));
        // Negative-to-unsigned traps for every narrow width; MIN/-1 analysis
        // must cover signed narrow division as well as remainders.
        for (ty, expression) in [
            ("u16", "u16(0 - 1)"),
            ("u32", "u32(0 - 1)"),
            ("i16", "i16(u16(65535))"),
            ("u16", "u16(i16(0 - 1))"),
            ("i32", "i32(u32(4294967295))"),
            ("u32", "u32(i32(0 - 1))"),
            ("i16", "-32768 / (0 - 1)"),
            ("i32", "-2147483648 / (0 - 1)"),
        ] {
            let source = format!("operation Probe:\n    returns {ty}.\n    body:\n        return {expression}.\noperation Main:\n    returns i64.\n    body:\n        Probe().\n        return 0.\n");
            let (_directory, path) = executable(&source);
            let output = Command::new(path).output().unwrap();
            assert_eq!(trap_signal(&output), Some(4), "{ty}: {expression}");
        }
    }

    #[test]
    fn records_agree_with_c_size_align_and_offsets() {
        let source = "entity Inner:\n    layout \"C\".\n    has small of type u8.\n    has wide of type i32.\nentity Outer:\n    layout \"C\".\n    has flag of type bool.\n    has inner of type Inner.\n    has end of type u16.\noperation Metrics:\n    exports \"C\" as \"sal_layout_metrics\".\n    accepts value of type Outer.\n    returns usize.\n    effects: Pure.\n    body:\n        return size_of(Outer) + align_of(Inner) + offset_of(Outer, \"inner\").\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        archive_library(&directory.0, &program.assembly, &header);
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
#include <stddef.h>
_Static_assert(sizeof(sal_record_Inner) == 8u, "inner size");
_Static_assert(sizeof(sal_record_Outer) == 16u, "outer size");
_Static_assert(offsetof(sal_record_Outer, inner) == 4u, "inner offset");
_Static_assert(offsetof(sal_record_Inner, wide) == 4u, "wide offset");
_Static_assert(offsetof(sal_record_Outer, end) == 12u, "end offset");
int main(void) {
    sal_record_Outer value = { .flag = true, .inner = { .small = 7, .wide = -9 }, .end = 258 };
    size_t expect = sizeof(sal_record_Outer) + _Alignof(sal_record_Inner) + offsetof(sal_record_Outer, inner);
    return sal_layout_metrics(value) != expect;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn small_records_return_packed_rax_rdx_by_value() {
        let source = "entity Pair:\n    layout \"C\".\n    has first of type i64.\n    has second of type i64.\noperation Make:\n    exports \"C\" as \"sal_make_pair\".\n    accepts first of type i64.\n    accepts second of type i64.\n    returns Pair.\n    effects: Pure.\n    body:\n        return Pair(first, second).\noperation First:\n    exports \"C\" as \"sal_first_of\".\n    accepts value of type Pair.\n    returns i64.\n    effects: Pure.\n    body:\n        return value.first.\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        archive_library(&directory.0, &program.assembly, &header);
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
int main(void) {
    sal_record_Pair made = sal_make_pair(-3, 9);
    if (made.first != -3) return 1;
    if (made.second != 9) return 2;
    if (sal_first_of(made) != -3) return 3;
    sal_record_Pair literal = { .first = 5, .second = -6 };
    if (sal_first_of(literal) != 5) return 4;
    return 0;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn nested_tail_field_reads_exact_final_byte() {
        let source = "entity Tiny:\n    layout \"C\".\n    has last of type u8.\nentity Outer:\n    layout \"C\".\n    has head of type u64.\n    has tail of type Tiny.\noperation Tail:\n    exports \"C\" as \"sal_tail_byte\".\n    accepts value of type Outer.\n    returns u8.\n    effects: Pure.\n    body:\n        return value.tail.last.\noperation Nested:\n    exports \"C\" as \"sal_nested_tail\".\n    accepts value of type Outer.\n    returns Tiny.\n    effects: Pure.\n    body:\n        return value.tail.\noperation Wrap:\n    exports \"C\" as \"sal_wrap_outer\".\n    accepts head of type u64.\n    accepts last of type u8.\n    returns Outer.\n    effects: Pure.\n    body:\n        return Outer(head, Tiny(last)).\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        archive_library(
            &directory.0,
            &program.assembly,
            &program.header.clone().unwrap(),
        );
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
int main(void) {
    sal_record_Outer built = sal_wrap_outer(UINT64_C(0x0102030405060708), 0xA5);
    if (built.head != UINT64_C(0x0102030405060708)) return 1;
    if (built.tail.last != 0xA5) return 2;
    sal_record_Tiny tail = sal_nested_tail(built);
    if (tail.last != 0xA5) return 3;
    if (sal_tail_byte(built) != 0xA5) return 4;
    sal_record_Outer literal = { .head = 1, .tail = { .last = 0x5A } };
    if (sal_tail_byte(literal) != 0x5A) return 5;
    return 0;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn large_records_use_hidden_sret_pointer() {
        let source = "entity Big:\n    layout \"C\".\n    has a of type u64.\n    has b of type u64.\n    has c of type u64.\noperation Make:\n    exports \"C\" as \"sal_make_big\".\n    accepts first of type u64.\n    accepts second of type u64.\n    accepts third of type u64.\n    returns Big.\n    effects: Pure.\n    body:\n        return Big(first, second, third).\noperation Sum:\n    exports \"C\" as \"sal_sum_big\".\n    accepts value of type Big.\n    returns u64.\n    effects: Pure.\n    body:\n        return value.a + value.b + value.c.\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        archive_library(&directory.0, &program.assembly, &header);
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
int main(void) {
    sal_record_Big made = sal_make_big(1, 2, 4);
    if (made.a != 1) return 1;
    if (made.b != 2) return 2;
    if (made.c != 4) return 3;
    if (sal_sum_big(made) != 7) return 4;
    return 0;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn record_register_rollback_keeps_later_scalar_in_register() {
        let source = "entity Two:\n    layout \"C\".\n    has first of type i64.\n    has second of type i64.\noperation Probe:\n    accepts a0 of type i64.\n    accepts a1 of type i64.\n    accepts a2 of type i64.\n    accepts a3 of type i64.\n    accepts a4 of type i64.\n    accepts pair of type Two.\n    accepts tail of type i64.\n    returns i64.\n    body:\n        return a0 + a1 + a2 + a3 + a4 + pair.first + pair.second + tail.\noperation Main:\n    returns i64.\n    body:\n        return Probe(1, 2, 3, 4, 5, Two(6, 7), 8).\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(36), "{:?}", output.status);
    }

    #[test]
    fn stack_scalar_and_record_calls_preserve_source_order() {
        let source = "entity Two:\n    layout \"C\".\n    has first of type u64.\n    has second of type u64.\noperation Add:\n    accepts a0 of type i64.\n    accepts a1 of type i64.\n    accepts a2 of type i64.\n    accepts a3 of type i64.\n    accepts a4 of type i64.\n    accepts a5 of type i64.\n    accepts a6 of type i64.\n    accepts a7 of type i64.\n    returns i64.\n    body:\n        return a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7.\noperation Nested:\n    accepts value of type Two.\n    returns u64.\n    body:\n        return value.first + value.second.\noperation Main:\n    returns i64.\n    body:\n        return Add(1, 2, 3, 4, 5, 6, i64(Nested(Two(7, 8))), 9).\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(45), "{:?}", output.status);
    }

    #[test]
    fn stack_span_arguments_execute_in_order() {
        let source = "operation TakeFour:\n    accepts a of type Bytes.\n    accepts b of type Bytes.\n    accepts c of type Bytes.\n    accepts d of type Bytes.\n    returns i64.\n    body:\n        return i64(len(a)) + i64(len(b)) + i64(len(c)) + i64(len(d)).\noperation Main:\n    returns i64.\n    body:\n        return TakeFour(bytes(\"a\"), bytes(\"bb\"), bytes(\"ccc\"), bytes(\"dddd\")).\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(10), "{:?}", output.status);
    }

    #[test]
    fn record_assignment_copies_through_long_loops() {
        let source = "entity Point:\n    layout \"C\".\n    has x of type i64.\n    has y of type i64.\noperation Main:\n    returns i64.\n    body:\n        let mut point = Point(1, 2).\n        let mut i = 0.\n        while i < 200000:\n            let snapshot = point.\n            set point = Point(point.x + 1, point.y + 2).\n            if snapshot.x + 1 != point.x:\n                return 10.\n            if snapshot.y + 2 != point.y:\n                return 11.\n            set i = i + 1.\n        return point.x + point.y.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(195),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
    }

    #[test]
    fn record_addresses_stay_stable_across_constructors() {
        let source = "entity Point:\n    layout \"C\".\n    has x of type i64.\n    has y of type i64.\noperation Read:\n    accepts pointer of type usize.\n    returns i64.\n    effects: UnsafeMemory.\n    body:\n        return i64(load8(pointer)) + i64(load8(pointer + usize(8))).\noperation Main:\n    returns i64.\n    effects: UnsafeMemory.\n    body:\n        let first = Point(3, 4).\n        let pointer = address(first).\n        let second = Point(30, 40).\n        if Read(pointer) != 7:\n            return 99.\n        return first.x + first.y + second.x + second.y.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(77), "{:?}", output.status);
    }

    #[test]
    fn genuine_archive_imports_link_without_runtime() {
        let source = "entity Pair:\n    layout \"C\".\n    has first of type i32.\n    has second of type u16.\noperation Double:\n    imports \"C\" as \"foreign_double\".\n    accepts value of type i32.\n    returns i32.\n    effects: SystemCall, UnsafeMemory.\noperation Fetch:\n    imports \"C\" as \"foreign_fetch\".\n    accepts first of type i32.\n    accepts second of type u16.\n    returns Pair.\n    effects: SystemCall, UnsafeMemory.\noperation Sum:\n    imports \"C\" as \"foreign_sum\".\n    accepts value of type Pair.\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        return i64(Double(21)) + Sum(Fetch(3, u16(4))).\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::Executable).unwrap();
        std::fs::write(directory.0.join("main.s"), program.assembly).unwrap();
        compile_freestanding(
            &directory.0,
            "helpers.c",
            "typedef struct { int first; unsigned short second; } sal_record_Pair;\nint foreign_double(int value) { return value * 2; }\nsal_record_Pair foreign_fetch(int first, unsigned short second) {\n    sal_record_Pair made = { first, second };\n    return made;\n}\nlong foreign_sum(sal_record_Pair value) { return (long)value.first + value.second; }\n",
        );
        command("ar", &["rcsD", "libforeign.a", "helpers.o"], &directory.0);
        command("as", &["--64", "-o", "main.o", "main.s"], &directory.0);
        link_executable(&directory.0, &["main.o", "libforeign.a"], "main");
        let output = Command::new(directory.0.join("main")).output().unwrap();
        assert_eq!(output.status.code(), Some(49), "{:?}", output.status);
        let undefined = command("nm", &["-u", "main"], &directory.0);
        assert!(
            undefined.stdout.is_empty(),
            "executable has undefined imports"
        );
    }

    #[test]
    fn imported_c_arithmetic_and_poisoned_results() {
        let source = "operation Echo8:\n    imports \"C\" as \"foreign_echo8\".\n    accepts value of type i8.\n    returns i8.\n    effects: SystemCall, UnsafeMemory.\noperation Echo16:\n    imports \"C\" as \"foreign_echo16\".\n    accepts value of type i16.\n    returns i16.\n    effects: SystemCall, UnsafeMemory.\noperation Echo32:\n    imports \"C\" as \"foreign_echo32\".\n    accepts first of type u32.\n    accepts second of type i32.\n    returns i32.\n    effects: SystemCall, UnsafeMemory.\noperation Poison8:\n    imports \"C\" as \"foreign_poison8\".\n    returns u8.\n    effects: SystemCall, UnsafeMemory.\noperation Poison16:\n    imports \"C\" as \"foreign_poison16\".\n    returns i16.\n    effects: SystemCall, UnsafeMemory.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        if Poison8() != u8(251):\n            return 100.\n        if Poison16() != i16(0 - 300):\n            return 101.\n        return i64(Echo8(i8(0 - 5))) + i64(Echo16(i16(0 - 300))) + i64(Echo32(u32(70000), -7)).\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::Executable).unwrap();
        std::fs::write(directory.0.join("main.s"), program.assembly).unwrap();
        compile_freestanding(
            &directory.0,
            "echo.c",
            "signed char foreign_echo8(signed char value) { return (signed char)(value + 3); }\nshort foreign_echo16(short value) { return (short)(value - 7); }\nint foreign_echo32(unsigned value, int other) { return (int)value + other; }\n",
        );
        compile_freestanding(
            &directory.0,
            "poison_ret.s",
            ".text\n.globl foreign_poison8\n.type foreign_poison8,@function\nforeign_poison8:\n    movabsq $0x123456789ABCDEFB, %rax\n    ret\n.size foreign_poison8, .-foreign_poison8\n.globl foreign_poison16\n.type foreign_poison16,@function\nforeign_poison16:\n    movabsq $0xDEADBEEEFFFFFED4, %rax\n    ret\n.size foreign_poison16, .-foreign_poison16\n.section .note.GNU-stack,\"\",@progbits\n",
        );
        command(
            "ar",
            &["rcsD", "libecho.a", "echo.o", "poison_ret.o"],
            &directory.0,
        );
        command("as", &["--64", "-o", "main.o", "main.s"], &directory.0);
        link_executable(&directory.0, &["main.o", "libecho.a"], "main");
        let output = Command::new(directory.0.join("main")).output().unwrap();
        assert_eq!(output.status.code(), Some(52), "{:?}", output.status);
    }

    #[test]
    fn short_circuit_skips_rhs_side_effects_and_traps() {
        let source = "operation Main:\n    returns i64.\n    body:\n        if false && ((10 / 0) == 0):\n            return 1.\n        if true || ((10 / 0) == 0):\n            return 7.\n        return 2.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(7),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
    }

    #[test]
    fn short_circuit_evaluates_rhs_once_in_order_with_normalized_bool() {
        let source = r#"operation Count:
    accepts marker of type usize.
    accepts expected of type u8.
    returns bool.
    effects: UnsafeMemory.
    body:
        if load8(marker) != expected:
            return false.
        store8(marker, expected + 1).
        return true.
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let scratch = syscall(9, 0, 4096, 3, 34, -1, 0).
        if scratch < 0:
            return 90.
        let base = usize(scratch).
        store8(base, u8(0)).
        if !(Count(base, u8(0)) && Count(base, u8(1))):
            return 10.
        if !(Count(base, u8(9)) || Count(base, u8(2))):
            return 11.
        if false && Count(base, u8(3)):
            return 12.
        if !(true || Count(base, u8(3))):
            return 13.
        if load8(base) != u8(3):
            return 8.
        return 7.
"#;
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(7), "{:?}", output.status);
    }

    #[test]
    fn nested_while_break_continue_use_nearest_loop() {
        let source = "operation Main:\n    returns i64.\n    body:\n        let mut total = 0.\n        let mut outer = 0.\n        let mut budget = 0.\n        while outer < 5:\n            set budget = budget + 1.\n            if budget > 100:\n                return 90.\n            let mut inner = 0.\n            while inner < 10:\n                set inner = inner + 1.\n                if inner == 2:\n                    continue.\n                if inner == 5:\n                    break.\n                set total = total + 1.\n            set outer = outer + 1.\n        if total != 15:\n            return total.\n        return 7.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some(7),
            "{:?} {:?}",
            output.status,
            output.stdout
        );
    }

    #[test]
    fn boolean_not_normalizes_and_while_conditions_reevaluate() {
        let source = "operation Main:\n    returns i64.\n    body:\n        let mut count = 0.\n        let mut guard = true.\n        while !!guard:\n            if !true:\n                return 90.\n            set count = count + 1.\n            if count == 200000:\n                set guard = false.\n        if count != 200000:\n            return count.\n        return 7.\n";
        let (_directory, path) = executable(source);
        let output = Command::new(path).output().unwrap();
        assert_eq!(output.status.code(), Some(7), "{:?}", output.status);
    }

    #[test]
    fn exported_cpp_header_compiles_and_matches_layout() {
        let source = "entity Pair:\n    layout \"C\".\n    has first of type i32.\n    has second of type u16.\noperation Make:\n    exports \"C\" as \"sal_cpp_make\".\n    accepts first of type i32.\n    accepts second of type u16.\n    returns Pair.\n    effects: Pure.\n    body:\n        return Pair(first, second).\n";
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        let header = program.header.clone().unwrap();
        archive_library(&directory.0, &program.assembly, &header);
        std::fs::write(
            directory.0.join("caller.cpp"),
            "#include \"sal.h\"\nint main() {\n    sal_record_Pair made = sal_cpp_make(-7, 9);\n    return !(made.first == -7 && made.second == 9);\n}\n",
        )
        .unwrap();
        command(
            "c++",
            &[
                "-std=c++11",
                "-Wall",
                "-Wextra",
                "-Werror",
                "caller.cpp",
                "libsal.a",
                "-o",
                "caller",
            ],
            &directory.0,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }

    #[test]
    fn c_objects_check_rollback_sret_stack_values_and_nested_evaluation() {
        let source = r#"entity Pair:
    layout "C".
    has first of type i64.
    has second of type i64.
entity Big:
    layout "C".
    has a of type u64.
    has b of type u64.
    has c of type u64.
operation Rollback:
    exports "C" as "sal_rollback".
    accepts a of type i64.
    accepts b of type i64.
    accepts c of type i64.
    accepts d of type i64.
    accepts e of type i64.
    accepts pair of type Pair.
    accepts tail of type i64.
    returns i64.
    body:
        return a + b * 10 + c * 100 + d * 1000 + e * 10000 + pair.first * 100000 + pair.second * 1000000 + tail * 10000000.
operation Large:
    exports "C" as "sal_large".
    accepts a of type u64.
    accepts b of type u64.
    accepts c of type u64.
    accepts d of type u64.
    accepts e of type u64.
    accepts f of type u64.
    accepts g of type u64.
    returns Big.
    body:
        return Big(a + f, b + g, c + d + e).
operation ForeignRollback:
    imports "C" as "foreign_rollback".
    accepts a of type i64.
    accepts b of type i64.
    accepts c of type i64.
    accepts d of type i64.
    accepts e of type i64.
    accepts pair of type Pair.
    accepts tail of type i64.
    returns i64.
    effects: SystemCall, UnsafeMemory.
operation ForeignBig:
    imports "C" as "foreign_big".
    accepts seed of type u64.
    returns Big.
    effects: SystemCall, UnsafeMemory.
operation ForeignScore:
    imports "C" as "foreign_score".
    accepts big of type Big.
    accepts pair of type Pair.
    accepts tail of type i64.
    returns i64.
    effects: SystemCall, UnsafeMemory.
operation ForeignVerify:
    imports "C" as "foreign_verify".
    returns i64.
    effects: SystemCall, UnsafeMemory.
operation Mark:
    imports "C" as "foreign_mark".
    accepts expected of type i64.
    returns i64.
    effects: SystemCall, UnsafeMemory.
operation Fold:
    imports "C" as "foreign_fold".
    accepts a of type i64.
    accepts b of type i64.
    accepts c of type i64.
    accepts d of type i64.
    accepts e of type i64.
    accepts f of type i64.
    accepts g of type i64.
    accepts h of type i64.
    returns i64.
    effects: SystemCall, UnsafeMemory.
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        if ForeignRollback(1, 2, 3, 4, 5, Pair(6, 7), 8) != 87654321:
            return 1.
        let big = ForeignBig(40).
        if ForeignScore(big, Pair(3, 4), 5) != 310:
            return 2.
        if ForeignVerify() != 0:
            return 3.
        if Fold(Mark(1), Mark(2), Mark(3), Mark(4), Mark(5), Mark(6), Pair(Mark(7), Mark(8)).first, Mark(9)) != 97654321:
            return 4.
        return 0.
"#;
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::Executable).unwrap();
        std::fs::write(directory.0.join("main.s"), program.assembly).unwrap();
        compile_freestanding(
            &directory.0,
            "interop.c",
            r#"
typedef struct { long first, second; } Pair;
typedef struct { unsigned long a, b, c; } Big;
extern long sal_rollback(long, long, long, long, long, Pair, long);
extern Big sal_large(unsigned long, unsigned long, unsigned long,
                     unsigned long, unsigned long, unsigned long, unsigned long);
long foreign_rollback(long a, long b, long c, long d, long e, Pair pair, long tail) {
    return a + b*10 + c*100 + d*1000 + e*10000 +
           pair.first*100000 + pair.second*1000000 + tail*10000000;
}
Big foreign_big(unsigned long seed) {
    Big result = { seed, seed + 1, seed + 2 };
    return result;
}
long foreign_score(Big big, Pair pair, long tail) {
    return (long)(big.a + big.b*2 + big.c*3) +
           pair.first*4 + pair.second*5 + tail*6;
}
extern long verify_sret(void);
long foreign_verify(void) {
    Pair pair = { 3, 2 };
    if (sal_rollback(8, 7, 6, 5, 4, pair, 1) != 12345678) return 1;
    Big value = sal_large(1, 2, 3, 4, 5, 6, 7);
    if (value.a != 7 || value.b != 9 || value.c != 12) return 2;
    if (verify_sret() != 0) return 3;
    return 0;
}
static long counter;
long foreign_mark(long expected) {
    if (++counter != expected) return -100;
    return expected;
}
long foreign_fold(long a, long b, long c, long d, long e, long f, long g, long h) {
    return a + b*10 + c*100 + d*1000 + e*10000 + f*100000 + g*1000000 + h*10000000;
}
"#,
        );
        compile_freestanding(
            &directory.0,
            "sret.s",
            r#".text
.globl verify_sret
.type verify_sret,@function
verify_sret:
    pushq %rbp
    movq %rsp, %rbp
    subq $48, %rsp
    leaq 16(%rsp), %rdi
    movq $1, %rsi
    movq $2, %rdx
    movq $3, %rcx
    movq $4, %r8
    movq $5, %r9
    movq $6, (%rsp)
    movq $7, 8(%rsp)
    call sal_large
    leaq 16(%rsp), %rcx
    cmpq %rcx, %rax
    jne .Lsret_bad
    cmpq $7, 16(%rsp)
    jne .Lsret_bad
    cmpq $9, 24(%rsp)
    jne .Lsret_bad
    cmpq $12, 32(%rsp)
    jne .Lsret_bad
    xorl %eax, %eax
    leave
    ret
.Lsret_bad:
    movl $1, %eax
    leave
    ret
.size verify_sret, .-verify_sret
.section .note.GNU-stack,"",@progbits
"#,
        );
        command("as", &["--64", "-o", "main.o", "main.s"], &directory.0);
        command(
            "ar",
            &["rcsD", "libinterop.a", "interop.o", "sret.o"],
            &directory.0,
        );
        link_executable(&directory.0, &["main.o", "libinterop.a"], "main");
        let output = Command::new(directory.0.join("main")).output().unwrap();
        assert_eq!(output.status.code(), Some(0), "{:?}", output.status);
        let undefined = command("nm", &["-u", "main"], &directory.0);
        assert!(undefined.stdout.is_empty(), "unexpected executable imports");
    }

    #[test]
    fn each_narrow_argument_uses_only_its_defined_low_bits() {
        for (ty, poison, expected) in [
            ("i8", "0x123456789ABCDEFB", -5_i64),
            ("i16", "0x123456789ABCFED4", -300),
            ("i32", "0x1234567880000000", -2147483648),
            ("u8", "0x123456789ABCDEFB", 251),
            ("u16", "0x123456789ABCFFFA", 65530),
            ("u32", "0x12345678FFFFFFFA", 4294967290),
        ] {
            let source = format!("operation Probe:\n    exports \"C\" as \"sal_probe\".\n    accepts value of type {ty}.\n    returns i64.\n    body:\n        return i64(value).\n");
            let directory = Directory::new();
            let program = emit_native(&ir(&source), NativeTarget::StaticLibrary).unwrap();
            archive_library(&directory.0, &program.assembly, &program.header.unwrap());
            let caller = format!(".text\n.globl _start\n_start:\n    andq $-16, %rsp\n    movabsq ${poison}, %rdi\n    call sal_probe\n    movabsq ${expected}, %rcx\n    cmpq %rcx, %rax\n    setne %dil\n    movzbl %dil, %edi\n    movl $60, %eax\n    syscall\n.section .note.GNU-stack,\"\",@progbits\n");
            compile_freestanding(&directory.0, "caller.s", &caller);
            link_executable(&directory.0, &["caller.o", "libsal.a"], "main");
            let output = Command::new(directory.0.join("main")).output().unwrap();
            assert_eq!(output.status.code(), Some(0), "{ty}: {:?}", output.status);
        }
    }

    #[test]
    fn each_narrow_result_uses_only_its_defined_low_bits() {
        for (ty, poison, expected) in [
            ("i8", "0x123456789ABCDEFB", "-5"),
            ("i16", "0x123456789ABCFED4", "-300"),
            ("i32", "0x1234567880000000", "-2147483648"),
            ("u8", "0x123456789ABCDEFB", "251"),
            ("u16", "0x123456789ABCFFFA", "65530"),
            ("u32", "0x12345678FFFFFFFA", "4294967290"),
            ("bool", "0x123456789ABCDE01", "true"),
            ("bool", "0x123456789ABCDE00", "false"),
        ] {
            let source = format!("operation Value:\n    imports \"C\" as \"foreign_value\".\n    returns {ty}.\n    effects: SystemCall, UnsafeMemory.\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        if Value() != {expected}:\n            return 1.\n        return 0.\n");
            let directory = Directory::new();
            let program = emit_native(&ir(&source), NativeTarget::Executable).unwrap();
            std::fs::write(directory.0.join("main.s"), program.assembly).unwrap();
            let foreign = format!(".text\n.globl foreign_value\nforeign_value:\n    movabsq ${poison}, %rax\n    ret\n.section .note.GNU-stack,\"\",@progbits\n");
            compile_freestanding(&directory.0, "foreign.s", &foreign);
            command("as", &["--64", "-o", "main.o", "main.s"], &directory.0);
            link_executable(&directory.0, &["main.o", "foreign.o"], "main");
            let output = Command::new(directory.0.join("main")).output().unwrap();
            assert_eq!(output.status.code(), Some(0), "{ty}: {:?}", output.status);
        }
    }

    #[test]
    fn c_record_fields_pack_and_load_each_integer_width() {
        let source = r#"entity Fields:
    layout "C".
    has a of type i8.
    has b of type u8.
    has c of type i16.
    has d of type u16.
    has e of type i32.
    has f of type u32.
operation Make:
    exports "C" as "sal_fields".
    returns Fields.
    body:
        return Fields(-5, 250, -300, 65000, -70000, 4000000000).
operation Checksum:
    exports "C" as "sal_fields_checksum".
    accepts value of type Fields.
    returns i64.
    body:
        return i64(value.a) + i64(value.b) + i64(value.c) + i64(value.d) + i64(value.e) + i64(value.f).
"#;
        let directory = Directory::new();
        let program = emit_native(&ir(source), NativeTarget::StaticLibrary).unwrap();
        archive_library(&directory.0, &program.assembly, &program.header.unwrap());
        compile_c_main(
            &directory.0,
            r#"#include "sal.h"
int main(void) {
    sal_record_Fields value = sal_fields();
    if (value.a != -5 || value.b != 250 || value.c != -300) return 1;
    if (value.d != 65000 || value.e != -70000 || value.f != UINT32_C(4000000000)) return 2;
    if (sal_fields_checksum(value) != INT64_C(3999994945)) return 3;
    sal_record_Fields negative = { -1, 2, -3, 4, -5, 6 };
    if (sal_fields_checksum(negative) != 3) return 4;
    return 0;
}
"#,
        );
        assert!(Command::new(directory.0.join("caller"))
            .status()
            .unwrap()
            .success());
    }
}
