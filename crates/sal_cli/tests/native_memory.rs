#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

//! Safe-memory consumer regressions: Buffer/MutBytes ownership, borrowing,
//! explicit borrow_end, and unsafe-block effect scoping.
//!
//! These tests assert only observable behavior: build success/failure,
//! emitted-artifact presence/absence, and native exit status. They never
//! inspect diagnostic wording, AST shape, or generated assembly text.
//! Every rejection pairs with a positive control so blanket accept/reject
//! cannot go green.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const DEADLINE: Duration = Duration::from_secs(15);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "sal-native-memory-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("fixture directory");
        Self(path)
    }

    fn compile(&self, name: &str, source: &str) -> (Output, PathBuf) {
        let src = self.0.join(format!("{name}.sal"));
        std::fs::write(&src, source).expect("write SAL fixture");
        let out = self.0.join(format!("out-{name}"));
        let output = Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(&src)
            .arg("--out")
            .arg(&out)
            .output()
            .expect("run SAL compiler");
        (output, out.join(name))
    }

    fn build_success(&self, name: &str, source: &str) -> PathBuf {
        let (output, artifact) = self.compile(name, source);
        assert!(
            output.status.success(),
            "expected build success for {name}:\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            artifact.exists(),
            "successful build must emit artifact for {name}"
        );
        artifact
    }

    fn build_rejected(&self, name: &str, source: &str) {
        let (output, artifact) = self.compile(name, source);
        assert!(
            !output.status.success(),
            "expected rejection for {name} but build succeeded"
        );
        assert_eq!(
            output.status.code(),
            Some(1),
            "rejection must exit 1 for {name}"
        );
        assert!(
            !artifact.exists(),
            "rejected SAL must not emit an artifact for {name}"
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn run_binary(program: &Path) -> Output {
    struct Guard(std::process::Child);
    impl Drop for Guard {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut child = Guard(
        Command::new(program)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run native binary"),
    );
    let deadline = Instant::now() + DEADLINE;
    loop {
        if let Some(status) = child.0.try_wait().expect("poll native binary") {
            let mut stdout = Vec::new();
            let mut stderr = Vec::new();
            use std::io::Read as _;
            if let Some(mut out) = child.0.stdout.take() {
                out.read_to_end(&mut stdout).expect("drain stdout");
            }
            if let Some(mut err) = child.0.stderr.take() {
                err.read_to_end(&mut stderr).expect("drain stderr");
            }
            let _ = child.0.wait();
            std::mem::forget(child);
            return Output {
                status,
                stdout,
                stderr,
            };
        }
        if Instant::now() >= deadline {
            panic!("native memory binary timed out: {}", program.display());
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn assert_executed(path: &Path) {
    let output = run_binary(path);
    assert!(
        output.status.success(),
        "native execution failed: status={} stdout={:?} stderr={:?}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_trapped(path: &Path) {
    let output = run_binary(path);
    assert!(
        !output.status.success(),
        "expected runtime trap but exited 0: {}",
        path.display()
    );
}

#[test]
fn buffer_allocate_metadata_and_drop_once_executes() {
    let fixture = Fixture::new();
    let program = fixture.build_success(
        "alloc",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(4096)).
        let mut failure = len(arena) != 4096.
        if failure:
            buffer_drop(arena).
            return 1.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&program);
}

#[test]
fn zero_length_buffer_is_valid_and_droppable() {
    let fixture = Fixture::new();
    let program = fixture.build_success(
        "zero",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(0)).
        let mut failure = 0.
        if len(arena) != 0:
            set failure = 1.
        let empty = borrow_mut(arena, usize(0), usize(0)).
        if len(empty) != 0:
            if failure == 0:
                set failure = 2.
        borrow_end(empty).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&program);
}

#[test]
fn end_exact_borrows_succeed_but_past_end_is_rejected() {
    let fixture = Fixture::new();
    // Positive: offset+length exactly at the end is in bounds.
    let ok = fixture.build_success(
        "end_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let tail = borrow_mut(arena, usize(54), usize(10)).
        let mut failure = 0.
        put(tail, usize(9), u8(7)).
        if byte(view(tail), usize(9)) != 7:
            set failure = 1.
        borrow_end(tail).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: constant past-the-end borrow is rejected.
    fixture.build_rejected(
        "end_past",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let tail = borrow_mut(arena, usize(55), usize(10)).
        borrow_end(tail).
        buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn dynamic_end_overflow_traps_at_runtime() {
    let fixture = Fixture::new();
    // Positive: computed in-bounds end access executes.
    let ok = fixture.build_success(
        "dyn_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), len(arena)).
        let last = len(span) - 1.
        let mut failure = 0.
        put(span, last, u8(9)).
        if byte(view(span), last) != 9:
            set failure = 1.
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: computed past-the-end index traps instead of corrupting.
    let trapped = fixture.build_success(
        "dyn_trap",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), len(arena)).
        put(span, len(span), u8(9)).
        borrow_end(span).
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_trapped(&trapped);
}

#[test]
fn disjoint_partitions_of_one_arena_read_and_write() {
    let fixture = Fixture::new();
    // Mirrors the warehouse 2MiB partition pattern at small scale:
    // request, parameters, scratch and output loans coexist disjointly.
    let program = fixture.build_success(
        "disjoint",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(4096)).
        let request = borrow_mut(arena, usize(0), usize(1024)).
        let params = borrow_mut(arena, usize(1024), usize(1024)).
        let scratch = borrow_mut(arena, usize(2048), usize(1024)).
        let output = borrow_mut(arena, usize(3072), usize(1024)).
        let mut failure = 0.
        put(request, usize(0), u8(1)).
        put(params, usize(0), u8(2)).
        put(scratch, usize(0), u8(3)).
        put(output, usize(0), u8(4)).
        if byte(view(request), usize(0)) != 1:
            set failure = 1.
        if byte(view(params), usize(0)) != 2:
            if failure == 0:
                set failure = 2.
        if byte(view(scratch), usize(0)) != 3:
            if failure == 0:
                set failure = 3.
        if byte(view(output), usize(0)) != 4:
            if failure == 0:
                set failure = 4.
        if len(request) != 1024:
            if failure == 0:
                set failure = 5.
        if len(output) != 1024:
            if failure == 0:
                set failure = 6.
        borrow_end(request).
        borrow_end(params).
        borrow_end(scratch).
        borrow_end(output).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&program);
}

#[test]
fn constant_overlapping_mutable_aliases_are_rejected() {
    let fixture = Fixture::new();
    // Positive control: adjacent loans succeed.
    let ok = fixture.build_success(
        "adjacent_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(4096)).
        let first = borrow_mut(arena, usize(0), usize(16)).
        let second = borrow_mut(arena, usize(16), usize(16)).
        put(first, usize(0), u8(1)).
        put(second, usize(0), u8(2)).
        borrow_end(first).
        borrow_end(second).
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: constant overlap cannot be granted.
    fixture.build_rejected(
        "overlap_no",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(4096)).
        let first = borrow_mut(arena, usize(0), usize(16)).
        let second = borrow_mut(arena, usize(8), usize(16)).
        borrow_end(first).
        borrow_end(second).
        buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn slice_mut_siblings_must_also_be_disjoint() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "slices_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let whole = borrow_mut(arena, usize(0), usize(128)).
        let left = slice_mut(whole, usize(0), usize(64)).
        let right = slice_mut(whole, usize(64), usize(64)).
        let mut failure = 0.
        put(left, usize(0), u8(11)).
        put(right, usize(0), u8(22)).
        if byte(view(left), usize(0)) != 11:
            set failure = 1.
        if byte(view(right), usize(0)) != 22:
            if failure == 0:
                set failure = 2.
        borrow_end(left).
        borrow_end(right).
        borrow_end(whole).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    fixture.build_rejected(
        "slices_overlap",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let whole = borrow_mut(arena, usize(0), usize(128)).
        let left = slice_mut(whole, usize(0), usize(96)).
        let right = slice_mut(whole, usize(32), usize(96)).
        borrow_end(left).
        borrow_end(right).
        borrow_end(whole).
        buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn buffer_double_drop_and_use_after_move_are_rejected() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "drop_once",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    fixture.build_rejected(
        "double_drop",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        buffer_drop(arena).
        buffer_drop(arena).
        return 0.
"#,
    );
    fixture.build_rejected(
        "use_after_move",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        buffer_drop(arena).
        if len(arena) != 0:
            return 1.
        return 0.
"#,
    );
}

#[test]
fn early_return_and_branch_loops_cannot_leak_the_owner() {
    let fixture = Fixture::new();
    // Positive: single cleanup tail across branches and loops.
    let ok = fixture.build_success(
        "tail_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let span = borrow_mut(arena, usize(0), usize(128)).
        let mut failure = 0.
        let mut index = usize(0).
        while index < 128:
            put(span, index, u8(1)).
            set index = index + 1.
        if byte(view(span), usize(0)) != 1:
            set failure = 1.
        if byte(view(span), usize(127)) != 1:
            if failure == 0:
                set failure = 2.
        borrow_end(span).
        buffer_drop(arena).
        return failure.
"#,
    );
    assert_executed(&ok);
    // Negative: early return while owning the mapping leaks.
    fixture.build_rejected(
        "early_leak",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let span = borrow_mut(arena, usize(0), usize(128)).
        if byte(view(span), usize(0)) == 0:
            return 0.
        borrow_end(span).
        buffer_drop(arena).
        return 1.
"#,
    );
}

#[test]
fn borrowed_return_from_dead_local_is_rejected() {
    let fixture = Fixture::new();
    // Positive: a view rooted in a caller argument may be returned.
    let ok = fixture.build_success(
        "arg_root_ok",
        r#"operation Identity:
    accepts span of type MutBytes.
    returns MutBytes.
    body:
        return span.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let back = Identity(span).
        let mut failure = 0.
        put(back, usize(0), u8(5)).
        if byte(view(back), usize(0)) != 5:
            set failure = 1.
        borrow_end(back).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: a view rooted in a dead local owner cannot be returned.
    fixture.build_rejected(
        "local_root_no",
        r#"operation Leaker:
    returns MutBytes.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        return span.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let leaked = Leaker().
        borrow_end(leaked).
        return 0.
"#,
    );
}

#[test]
fn immutable_aliases_retain_lifetime_until_ended() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "alias_end_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let mut failure = 0.
        put(span, usize(0), u8(42)).
        let first = view(span).
        let second = view(span).
        if byte(first, usize(0)) != 42:
            set failure = 1.
        if byte(second, usize(0)) != 42:
            if failure == 0:
                set failure = 2.
        borrow_end(first).
        borrow_end(second).
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: dropping the owner while an immutable alias is live.
    fixture.build_rejected(
        "drop_below_alias",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let kept = view(span).
        buffer_drop(arena).
        if byte(kept, usize(0)) == 0:
            return 1.
        return 0.
"#,
    );
}

#[test]
fn mutation_while_a_read_view_is_live_is_rejected() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "mutate_after_end",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let reader = view(span).
        let mut failure = 0.
        if byte(reader, usize(0)) != 0:
            set failure = 1.
        borrow_end(reader).
        put(span, usize(0), u8(9)).
        if byte(view(span), usize(0)) != 9:
            if failure == 0:
                set failure = 2.
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    fixture.build_rejected(
        "mutate_during_read",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let reader = view(span).
        put(span, usize(0), u8(9)).
        borrow_end(reader).
        borrow_end(span).
        buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn ended_borrows_cannot_be_reused() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "use_before_end",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        put(span, usize(0), u8(3)).
        borrow_end(span).
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    fixture.build_rejected(
        "reuse_after_end",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        borrow_end(span).
        put(span, usize(0), u8(3)).
        buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn same_owner_cannot_be_consumed_twice_across_arguments() {
    let fixture = Fixture::new();
    let ok = fixture.build_success(
        "two_owners_ok",
        r#"operation TakeTwo:
    accepts first of type Buffer.
    accepts second of type Buffer.
    returns i64.
    effects: SystemCall.
    body:
        buffer_drop(first).
        buffer_drop(second).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let first = buffer(usize(32)).
        let second = buffer(usize(32)).
        return TakeTwo(first, second).
"#,
    );
    assert_executed(&ok);
    fixture.build_rejected(
        "double_consume",
        r#"operation TakeTwo:
    accepts first of type Buffer.
    accepts second of type Buffer.
    returns i64.
    effects: SystemCall.
    body:
        buffer_drop(first).
        buffer_drop(second).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let only = buffer(usize(32)).
        return TakeTwo(only, only).
"#,
    );
}

#[test]
fn opaque_owners_cannot_be_forged_cast_or_exported() {
    let fixture = Fixture::new();
    // Opaque integer cast of an owner is rejected.
    fixture.build_rejected(
        "cast_owner",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(32)).
        let exposed = usize(arena).
        buffer_drop(arena).
        return i64(exposed).
"#,
    );
    // Raw address escape of an owner outside an unsafe block is rejected.
    fixture.build_rejected(
        "address_escape",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(32)).
        let span = borrow_mut(arena, usize(0), usize(32)).
        let exposed = address(view(span)).
        borrow_end(span).
        buffer_drop(arena).
        return i64(exposed).
"#,
    );
    // Even an unsafe scope cannot expose the opaque owner's metadata.
    fixture.build_rejected(
        "address_owner_inside_unsafe",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(32)).
        unsafe:
            let exposed = address(arena).
        buffer_drop(arena).
        return 0.
"#,
    );
    // C ABI payloads cannot carry an opaque owner.
    fixture.build_rejected(
        "cabi_owner",
        r#"operation Smuggle:
    accepts owned of type Buffer.
    exports "C" as "smuggle".
    returns i64.
    body:
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        return 0.
"#,
    );
    // Channel payloads cannot carry an opaque owner either.
    fixture.build_rejected(
        "send_owner",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(32)).
        let ch = channel(Buffer, usize(1)).
        let outcome = send(ch, arena).
        if outcome.sent == false:
            return 1.
        channel_drop(ch).
        return 0.
"#,
    );
}

#[test]
fn unsafe_block_discharges_only_unsafe_memory() {
    let fixture = Fixture::new();
    // Positive: a SystemCall-only wrapper may use raw memory strictly
    // inside an explicit unsafe block and still execute.
    let ok = fixture.build_success(
        "scoped_unsafe_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(4096)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let mut failure = 0.
        put(span, usize(0), u8(77)).
        if byte(view(span), usize(0)) != 77:
            set failure = 1.
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        unsafe:
            unsafe:
                let pid = syscall(39, 0, 0, 0, 0, 0, 0).
                if pid <= 0:
                    return 4.
            let mapped = syscall(9, 0, usize(4096), 3, 34, -1, 0).
            if mapped < 0:
                return 2.
            let released = syscall(11, mapped, usize(4096), 0, 0, 0, 0).
            if released != 0:
                return 3.
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: raw calls outside any unsafe block without UnsafeMemory.
    fixture.build_rejected(
        "raw_without_scope",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mapped = syscall(9, 0, usize(4096), 3, 34, -1, 0).
        if mapped < 0:
            return 1.
        return 0.
"#,
    );
    // Negative: an unsafe block does not excuse a missing SystemCall.
    fixture.build_rejected(
        "unsafe_keeps_syscall",
        r#"operation Main:
    returns i64.
    effects: UnsafeMemory.
    body:
        unsafe:
            let mapped = syscall(9, 0, usize(4096), 3, 34, -1, 0).
            if mapped < 0:
                return 1.
        return 0.
"#,
    );
    // Negative: a SystemCall-only operation cannot hide raw stores
    // without an explicit unsafe block (no whitelist by module or name).
    fixture.build_rejected(
        "falsely_safe_store",
        r#"operation QuietWrite:
    accepts target of type usize.
    returns i64.
    effects: SystemCall.
    body:
        store8(target, u8(1)).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        return QuietWrite(usize(0)).
"#,
    );
    // UnsafeMemory permission must end at the block, not leak onward.
    fixture.build_rejected(
        "unsafe_grant_does_not_escape",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        unsafe:
            let allowed = syscall(39, 0, 0, 0, 0, 0, 0).
        let denied = syscall(39, 0, 0, 0, 0, 0, 0).
        return 0.
"#,
    );
    // Unsafe only grants a raw-memory effect; owner checks still apply.
    fixture.build_rejected(
        "unsafe_preserves_affinity",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        unsafe:
            let arena = buffer(usize(32)).
            buffer_drop(arena).
            buffer_drop(arena).
        return 0.
"#,
    );
    // Safe allocation is still an OS effect, even inside an unsafe block.
    fixture.build_rejected(
        "unsafe_allocator_keeps_system_call",
        r#"operation Main:
    returns i64.
    effects: Pure.
    body:
        unsafe:
            let arena = buffer(usize(32)).
            buffer_drop(arena).
        return 0.
"#,
    );
}

#[test]
fn bytes_in_internal_record_preserves_argument_provenance() {
    let fixture = Fixture::new();
    // Positive: internal non-C record carrying Bytes rooted in a live caller
    // argument returns a usable view. The record holds that view, so it is
    // ended before the owner drops (record-held views gate owner drops).
    let ok = fixture.build_success(
        "record_arg_ok",
        r#"entity SpanBox:
    has data of type Bytes.
operation Wrap:
    accepts value of type Bytes.
    returns SpanBox.
    body:
        return SpanBox(value).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let mut failure = 0.
        put(span, usize(0), u8(9)).
        let probe = view(span).
        let boxed = Wrap(probe).
        if byte(boxed.data, usize(0)) != 9:
            set failure = 1.
        borrow_end(boxed).
        borrow_end(probe).
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: the same record still holding the view blocks the drop.
    fixture.build_rejected(
        "record_held_drop_no",
        r#"entity SpanBox:
    has data of type Bytes.
operation Wrap:
    accepts value of type Bytes.
    returns SpanBox.
    body:
        return SpanBox(value).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let probe = view(span).
        let boxed = Wrap(probe).
        let first = byte(boxed.data, usize(0)).
        borrow_end(probe).
        borrow_end(span).
        buffer_drop(arena).
        return i64(first).
"#,
    );
    // Negative: record view rooted in a dead local owner cannot escape.
    fixture.build_rejected(
        "record_local_no",
        r#"entity SpanBox:
    has data of type Bytes.
operation Leaks:
    returns SpanBox.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let probe = view(span).
        return SpanBox(probe).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let boxed = Leaks().
        if len(boxed.data) != 64:
            return 1.
        return 0.
"#,
    );
}

#[test]
fn callee_borrows_reject_interargument_consumption() {
    let fixture = Fixture::new();
    // Positive: distinct owners pass side by side and each is consumed once.
    let ok = fixture.build_success(
        "args_ok",
        r#"operation TakeTwo:
    accepts first of type Buffer.
    accepts second of type Buffer.
    returns i64.
    effects: SystemCall.
    body:
        buffer_drop(first).
        buffer_drop(second).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let first = buffer(usize(16)).
        let second = buffer(usize(16)).
        return TakeTwo(first, second).
"#,
    );
    assert_executed(&ok);
    // Negative: a borrowed loan freed as another argument is rejected.
    fixture.build_rejected(
        "args_consume",
        r#"operation TakeLoan:
    accepts held of type MutBytes.
    accepts owned of type Buffer.
    returns i64.
    effects: SystemCall.
    body:
        buffer_drop(owned).
        borrow_end(held).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(32)).
        let span = borrow_mut(arena, usize(0), usize(32)).
        let status = TakeLoan(span, arena).
        borrow_end(span).
        return status.
"#,
    );
}

#[test]
fn borrows_clause_lends_the_callers_owner_and_keeps_it_usable() {
    let fixture = Fixture::new();
    // Positive: owner locals are lent at the call site, the callee writes
    // through the borrowed slot, and the caller still owns, reads and drops
    // it. The concurrency import keeps that pass in the pipeline too.
    let ok = fixture.build_success(
        "borrows_ok",
        r#"use "std/concurrency.sal".
operation Fill:
    accepts arena of type Buffer.
    borrows arena.
    accepts value of type u8.
    returns usize.
    body:
        let span = borrow_mut(arena, usize(0), usize(1)).
        put(span, usize(0), value).
        borrow_end(span).
        return len(arena).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(8)).
        let first = Fill(arena, u8(3)).
        let second = Fill(arena, u8(7)).
        let span = borrow_mut(arena, usize(0), usize(1)).
        let seen = byte(span, usize(0)).
        borrow_end(span).
        buffer_drop(arena).
        return i64(first + second) + i64(seen) - 23.
"#,
    );
    assert_executed(&ok);
    // Negative: a borrowed owner cannot be consumed by the callee.
    fixture.build_rejected(
        "borrows_drop",
        r#"operation Free:
    accepts arena of type Buffer.
    borrows arena.
    returns i64.
    effects: SystemCall.
    body:
        buffer_drop(arena).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(8)).
        let status = Free(arena).
        buffer_drop(arena).
        return status.
"#,
    );
}

#[test]
fn dynamic_disjoint_executes_and_dynamic_overlap_traps() {
    let fixture = Fixture::new();
    // Positive: adjacent windows computed at runtime execute.
    let ok = fixture.build_success(
        "dyn_disjoint_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let half = len(arena) / 2.
        let left = borrow_mut(arena, usize(0), half).
        let right = borrow_mut(arena, half, len(arena) - half).
        let mut failure = 0.
        put(left, usize(0), u8(3)).
        put(right, usize(0), u8(4)).
        if byte(view(left), usize(0)) != 3:
            set failure = 1.
        if byte(view(right), usize(0)) != 4:
            if failure == 0:
                set failure = 2.
        borrow_end(left).
        borrow_end(right).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: overlapping runtime windows trap before memory access.
    let trapped = fixture.build_success(
        "dyn_overlap_trap",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(128)).
        let half = len(arena) / 2.
        let left = borrow_mut(arena, usize(0), half + 1).
        let right = borrow_mut(arena, half, len(arena) - half).
        put(left, usize(0), u8(1)).
        put(right, usize(0), u8(2)).
        borrow_end(left).
        borrow_end(right).
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_trapped(&trapped);
}

#[test]
fn diverging_paths_do_not_feed_joins_or_exit_checks() {
    let fixture = Fixture::new();
    // Positive: a break-free `while true` exits only through its returns,
    // each of which drops the owner first; the impossible fallthrough is not
    // an exit, and the returning branch does not leak into the loop state.
    let ok = fixture.build_success(
        "loop_exit_ok",
        r#"operation Count:
    accepts limit of type i64.
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let mut count = 0.
        while true:
            set count = count + 1.
            if count >= limit:
                buffer_drop(arena).
                return count.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        return Count(3) - 3.
"#,
    );
    assert_executed(&ok);
    // Negative: an owner consumed on only one reachable branch has no single
    // state afterwards (double drop or leak depending on the path).
    fixture.build_rejected(
        "one_branch_drop_no",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let failure = 0.
        if len(arena) == 64:
            buffer_drop(arena).
        buffer_drop(arena).
        return failure.
"#,
    );
    // Negative: a break out of `while true` reaches the exit with the owner.
    fixture.build_rejected(
        "break_leak_no",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        while true:
            break.
        return 0.
"#,
    );
}

#[test]
fn branch_loop_retained_view_blocks_later_mutation_or_drop() {
    let fixture = Fixture::new();
    // Positive: joined view ends before later mutation.
    let ok = fixture.build_success(
        "join_ok",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let mut failure = 0.
        if len(span) == 64:
            set failure = 0.
        let reader = view(span).
        if byte(reader, usize(0)) != 0:
            set failure = 1.
        borrow_end(reader).
        put(span, usize(0), u8(6)).
        borrow_end(span).
        if failure != 0:
            buffer_drop(arena).
            return failure.
        buffer_drop(arena).
        return 0.
"#,
    );
    assert_executed(&ok);
    // Negative: branch-retained live view cannot be bypassed by mutation.
    fixture.build_rejected(
        "branch_bypass_no",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let mut reader = view(span).
        if len(span) == 64:
            set reader = view(span).
        put(span, usize(0), u8(6)).
        borrow_end(reader).
        borrow_end(span).
        buffer_drop(arena).
        return 0.
"#,
    );
    // Negative: loop-retained live view blocks owner drop.
    fixture.build_rejected(
        "loop_drop_no",
        r#"operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(64)).
        let span = borrow_mut(arena, usize(0), usize(64)).
        let reader = view(span).
        let mut index = usize(0).
        while index < 4:
            set index = index + 1.
        buffer_drop(arena).
        borrow_end(reader).
        borrow_end(span).
        return 0.
"#,
    );
}
