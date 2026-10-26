#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

//! Native SAL concurrency consumer tests.
//!
//! Canonical API (heterogeneous wait arms):
//! - `channel(TypeName, capacity)` with a bare scalar/C-record name and a
//!   usize capacity; `channel_clone(c)` borrows; `channel_drop(c)` consumes
//!   (Void); `close(c)` borrows and returns bool; `send(c, v)` and
//!   `receive(c)` borrow. All via `use "std/concurrency.sal".`
//!   The safe surface needs only `effects: SystemCall.`; erased runtime
//!   pointer entry points remain unsafe and are never a safe-handle factory.
//! - `spawn(Worker, value)` takes a bare operation name; `join(t)` consumes.
//!   Each worker takes one scalar / C-record / `Channel<T>` and returns `i64`.
//!   A `Channel<T>` spawn argument moves; the worker consumes it. Clone the
//!   channel when the caller needs to retain its own handle.
//! - Heterogeneous `wait_for(...)`: at least one `receive(c)`/`send(c, v)` arm
//!   with independent payload types per arm plus an optional trailing
//!   `timeout(ms)` or `otherwise()` fallback. `WaitResult` carries
//!   `index:usize`, `status:usize` (0 success, 1 closed, 2 fallback) plus one
//!   `armN` field per non-fallback arm. Each arm reports `selected:bool`,
//!   `open:bool`, `value:T`: the chosen arm reports `selected true` (open on
//!   success, closed with zeroed receive payload); unchosen receive arms are
//!   zero, unchosen send arms keep the original value. Fallback `index`
//!   equals the non-fallback arm count.
//! - `SendResult{sent:bool,value:T}` keeps `value` on both paths (including
//!   sends on a closed channel); `ReceiveResult{open:bool,value:T}` is zero
//!   when `open == false`.
//! - Safe payloads are integers, bool, and C records of those (transitively);
//!   `Bytes`/`Text`/handle payloads are rejected. Ownership violations report
//!   `CON` diagnostics.
//! - Raw boundary: `atomic_load(usize)->u32`, `atomic_store(usize,u32)`,
//!   `atomic_cas(usize,u32,u32)->u32` (returns prior), `load64`/`store64`,
//!   `operation_address(Worker)->usize`. Unaligned u32 atomics trap (SIGILL).
//!
//! Affine discipline: every positive test accumulates `failure` and runs a
//! single cleanup tail, so each channel is dropped exactly once and each
//! thread joined exactly once on every exit. No early return owns a handle.
//!
//! These tests compile real SAL via `CARGO_BIN_EXE_sal`, execute the produced
//! native binaries under a bounded external watchdog, and assert only
//! observable exit status / rejection diagnostics. They never inspect
//! generated assembly text.

use std::io::Read;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const DEADLINE: Duration = Duration::from_secs(10);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "sal-native-concurrency-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("temporary fixture directory");
        Self(path)
    }

    fn source(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, text).expect("write SAL fixture");
        path
    }

    fn build(&self, source: &Path, out_dir: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(source)
            .arg("--strict")
            .arg("--out")
            .arg(self.0.join(out_dir))
            .output()
            .expect("run SAL compiler")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct Running(Child);

impl Running {
    fn wait_bounded(mut self) -> Output {
        let deadline = Instant::now() + DEADLINE;
        loop {
            if let Some(status) = self.0.try_wait().expect("poll native binary") {
                let mut stdout = Vec::new();
                let mut stderr = Vec::new();
                if let Some(mut out) = self.0.stdout.take() {
                    out.read_to_end(&mut stdout).expect("drain stdout");
                }
                if let Some(mut err) = self.0.stderr.take() {
                    err.read_to_end(&mut stderr).expect("drain stderr");
                }
                let _ = self.0.wait();
                return Output {
                    status,
                    stdout,
                    stderr,
                };
            }
            assert!(
                Instant::now() < deadline,
                "native concurrency binary timed out (lost wake or deadlock)"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
    }
}

impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn spawn_bounded(program: &Path) -> Running {
    Running(
        Command::new(program)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run native concurrency binary"),
    )
}

fn run_bounded(program: &Path) -> Output {
    spawn_bounded(program).wait_bounded()
}

fn success(output: &Output) {
    assert!(
        output.status.success(),
        "status={}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn combined(output: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn assert_rejected_code(output: &Output, artifact: &Path, code: &str) {
    assert_eq!(
        output.status.code(),
        Some(1),
        "rejection must exit 1: {}",
        combined(output)
    );
    assert!(
        combined(output).contains(code),
        "expected diagnostic {code}: {}",
        combined(output)
    );
    assert!(
        !artifact.exists(),
        "rejected SAL must not emit an artifact: {}",
        artifact.display()
    );
}

#[test]
fn bounded_buffered_send_receive_drain_then_close_reports_typed_outcomes() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "bounded.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(2)).
        let first = send(ch, 11).
        if first.sent == false:
            if failure == 0:
                set failure = 1.
        if first.value != 11:
            if failure == 0:
                set failure = 2.
        let second = send(ch, 22).
        if second.sent == false:
            if failure == 0:
                set failure = 3.
        if second.value != 22:
            if failure == 0:
                set failure = 4.
        if close(ch) == false:
            if failure == 0:
                set failure = 5.
        let drain_one = receive(ch).
        if drain_one.open == false:
            if failure == 0:
                set failure = 6.
        if drain_one.value != 11:
            if failure == 0:
                set failure = 7.
        let drain_two = receive(ch).
        if drain_two.open == false:
            if failure == 0:
                set failure = 8.
        if drain_two.value != 22:
            if failure == 0:
                set failure = 9.
        let closed = receive(ch).
        if closed.open == true:
            if failure == 0:
                set failure = 10.
        if closed.value != 0:
            if failure == 0:
                set failure = 11.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-bounded");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-bounded/bounded"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn rendezvous_channel_moves_through_native_thread_send_join() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "rendezvous.sal",
        r#"use "std/concurrency.sal".
operation EchoWorker:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        let got = receive(ch).
        channel_drop(ch).
        if got.open == false:
            return -1.
        return got.value + 1.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(0)).
        let worker_ch = channel_clone(ch).
        let thread = spawn(EchoWorker, worker_ch).
        let sent = send(ch, 41).
        if sent.sent == false:
            if failure == 0:
                set failure = 1.
        if sent.value != 41:
            if failure == 0:
                set failure = 2.
        let code = join(thread).
        channel_drop(ch).
        if code != 42:
            if failure == 0:
                set failure = 3.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-rendezvous");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-rendezvous/rendezvous"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn wait_for_commits_exactly_one_ready_arm_without_loss_or_double_consume() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "wait_atomic.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let left = channel(i64, usize(1)).
        let right = channel(i64, usize(1)).
        let one = send(left, 11).
        if one.sent == false:
            if failure == 0:
                set failure = 1.
        let two = send(right, 22).
        if two.sent == false:
            if failure == 0:
                set failure = 2.
        let winner = wait_for(receive(left), receive(right)).
        if winner.status != 0:
            if failure == 0:
                set failure = 3.
        if winner.index == 0:
            if winner.arm0.selected == false:
                if failure == 0:
                    set failure = 4.
            if winner.arm0.open == false:
                if failure == 0:
                    set failure = 5.
            if winner.arm0.value != 11:
                if failure == 0:
                    set failure = 6.
            if winner.arm1.selected == true:
                if failure == 0:
                    set failure = 7.
            if winner.arm1.value != 0:
                if failure == 0:
                    set failure = 8.
            let other = receive(right).
            if other.open == false:
                if failure == 0:
                    set failure = 9.
            if other.value != 22:
                if failure == 0:
                    set failure = 10.
        else:
            if winner.index != 1:
                if failure == 0:
                    set failure = 11.
            if winner.arm1.selected == false:
                if failure == 0:
                    set failure = 12.
            if winner.arm1.open == false:
                if failure == 0:
                    set failure = 13.
            if winner.arm1.value != 22:
                if failure == 0:
                    set failure = 14.
            if winner.arm0.selected == true:
                if failure == 0:
                    set failure = 15.
            if winner.arm0.value != 0:
                if failure == 0:
                    set failure = 16.
            let other = receive(left).
            if other.open == false:
                if failure == 0:
                    set failure = 17.
            if other.value != 11:
                if failure == 0:
                    set failure = 18.
        channel_drop(left).
        channel_drop(right).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-wait-atomic");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-wait-atomic/wait_atomic"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn losing_record_send_preserves_owned_value_for_later_use() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "losing.sal",
        r#"use "std/concurrency.sal".
entity Pair:
    layout "C".
    has x of type i64.
    has y of type i64.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ready = channel(Pair, usize(1)).
        let full = channel(Pair, usize(1)).
        let fill = send(full, Pair(100, 200)).
        if fill.sent == false:
            if failure == 0:
                set failure = 1.
        let first = Pair(1, 2).
        let second = Pair(3, 4).
        let winner = wait_for(send(ready, first), send(full, second)).
        if winner.status != 0:
            if failure == 0:
                set failure = 2.
        if winner.index != 0:
            if failure == 0:
                set failure = 3.
        if winner.arm0.selected == false:
            if failure == 0:
                set failure = 4.
        if winner.arm0.open == false:
            if failure == 0:
                set failure = 5.
        if winner.arm0.value.x != 1:
            if failure == 0:
                set failure = 6.
        if winner.arm0.value.y != 2:
            if failure == 0:
                set failure = 7.
        if winner.arm1.selected == true:
            if failure == 0:
                set failure = 8.
        if winner.arm1.value.x != 3:
            if failure == 0:
                set failure = 9.
        if winner.arm1.value.y != 4:
            if failure == 0:
                set failure = 10.
        let drained = receive(full).
        if drained.open == false:
            if failure == 0:
                set failure = 11.
        if drained.value.x != 100:
            if failure == 0:
                set failure = 12.
        let retry = send(full, second).
        if retry.sent == false:
            if failure == 0:
                set failure = 13.
        if retry.value.x != 3:
            if failure == 0:
                set failure = 14.
        let got_ready = receive(ready).
        if got_ready.value.x != 1:
            if failure == 0:
                set failure = 15.
        if got_ready.value.y != 2:
            if failure == 0:
                set failure = 16.
        let got_full = receive(full).
        if got_full.value.x != 3:
            if failure == 0:
                set failure = 17.
        if got_full.value.y != 4:
            if failure == 0:
                set failure = 18.
        channel_drop(ready).
        channel_drop(full).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-losing");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-losing/losing"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn heterogeneous_record_bool_covers_ready_fallback_and_closed() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "cancel.sal",
        r#"use "std/concurrency.sal".
entity Pair:
    layout "C".
    has x of type i64.
    has y of type i64.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let data = channel(Pair, usize(1)).
        let stop = channel(bool, usize(1)).
        let ready = send(data, Pair(10, 20)).
        if ready.sent == false:
            if failure == 0:
                set failure = 1.
        let picked = wait_for(receive(data), receive(stop)).
        if picked.status != 0:
            if failure == 0:
                set failure = 2.
        if picked.index != 0:
            if failure == 0:
                set failure = 3.
        if picked.arm0.selected == false:
            if failure == 0:
                set failure = 4.
        if picked.arm0.open == false:
            if failure == 0:
                set failure = 5.
        if picked.arm0.value.x != 10:
            if failure == 0:
                set failure = 6.
        if picked.arm0.value.y != 20:
            if failure == 0:
                set failure = 7.
        if picked.arm1.selected == true:
            if failure == 0:
                set failure = 8.
        if picked.arm1.value == true:
            if failure == 0:
                set failure = 9.
        let idle = wait_for(receive(data), receive(stop), otherwise()).
        if idle.status != 2:
            if failure == 0:
                set failure = 10.
        if idle.index != 2:
            if failure == 0:
                set failure = 11.
        if idle.arm0.selected == true:
            if failure == 0:
                set failure = 12.
        if idle.arm1.selected == true:
            if failure == 0:
                set failure = 13.
        if close(data) == false:
            if failure == 0:
                set failure = 14.
        if close(stop) == false:
            if failure == 0:
                set failure = 15.
        let gone_data = receive(data).
        if gone_data.open == true:
            if failure == 0:
                set failure = 16.
        let gone_stop = wait_for(receive(stop), timeout(usize(20))).
        if gone_stop.status != 1:
            if failure == 0:
                set failure = 17.
        if gone_stop.index != 0:
            if failure == 0:
                set failure = 18.
        if gone_stop.arm0.selected == false:
            if failure == 0:
                set failure = 19.
        if gone_stop.arm0.open == true:
            if failure == 0:
                set failure = 20.
        if gone_stop.arm0.value == true:
            if failure == 0:
                set failure = 21.
        let data_two = channel(Pair, usize(0)).
        let stop_two = channel(bool, usize(1)).
        let woke = send(stop_two, true).
        if woke.sent == false:
            if failure == 0:
                set failure = 22.
        let signal = wait_for(receive(data_two), receive(stop_two)).
        if signal.status != 0:
            if failure == 0:
                set failure = 23.
        if signal.index != 1:
            if failure == 0:
                set failure = 24.
        if signal.arm1.selected == false:
            if failure == 0:
                set failure = 25.
        if signal.arm1.open == false:
            if failure == 0:
                set failure = 26.
        if signal.arm1.value == false:
            if failure == 0:
                set failure = 27.
        if signal.arm0.selected == true:
            if failure == 0:
                set failure = 28.
        if signal.arm0.value.x != 0:
            if failure == 0:
                set failure = 29.
        if signal.arm0.value.y != 0:
            if failure == 0:
                set failure = 30.
        channel_drop(data_two).
        channel_drop(stop_two).
        channel_drop(data).
        channel_drop(stop).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-cancel");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-cancel/cancel"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn otherwise_fallback_reports_arm_count_without_blocking() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "otherwise.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(1)).
        let picked = wait_for(receive(ch), otherwise()).
        if picked.status != 2:
            if failure == 0:
                set failure = 1.
        if picked.index != 1:
            if failure == 0:
                set failure = 2.
        if picked.arm0.selected == true:
            if failure == 0:
                set failure = 3.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-otherwise");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-otherwise/otherwise"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn timeout_fallback_then_close_drain_covers_time_and_close_races() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "timeout_close.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(0)).
        let timed = wait_for(receive(ch), timeout(usize(20))).
        if timed.status != 2:
            if failure == 0:
                set failure = 1.
        if timed.index != 1:
            if failure == 0:
                set failure = 2.
        if timed.arm0.selected == true:
            if failure == 0:
                set failure = 3.
        if close(ch) == false:
            if failure == 0:
                set failure = 4.
        let closed = receive(ch).
        if closed.open == true:
            if failure == 0:
                set failure = 5.
        if closed.value != 0:
            if failure == 0:
                set failure = 6.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-timeout");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-timeout/timeout_close"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn blocked_wait_wakes_exactly_once_without_lost_wakeup() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "nowake.sal",
        r#"use "std/concurrency.sal".
operation Sender:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        let sent = send(ch, 99).
        channel_drop(ch).
        if sent.sent == false:
            return 1.
        else:
            return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(0)).
        let worker_ch = channel_clone(ch).
        let thread = spawn(Sender, worker_ch).
        let got = wait_for(receive(ch)).
        if got.status != 0:
            if failure == 0:
                set failure = 1.
        if got.index != 0:
            if failure == 0:
                set failure = 2.
        if got.arm0.selected == false:
            if failure == 0:
                set failure = 3.
        if got.arm0.open == false:
            if failure == 0:
                set failure = 4.
        if got.arm0.value != 99:
            if failure == 0:
                set failure = 5.
        let code = join(thread).
        channel_drop(ch).
        if code != 0:
            if failure == 0:
                set failure = 6.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-nowake");
    success(&build);
    // The watchdog is the assertion: a lost wake deadlocks and trips DEADLINE.
    let output = run_bounded(&fixture.0.join("out-nowake/nowake"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn double_close_and_send_on_closed_preserves_original_value() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "double_close.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(1)).
        let opened = send(ch, 10).
        if opened.sent == false:
            if failure == 0:
                set failure = 1.
        if close(ch) == false:
            if failure == 0:
                set failure = 2.
        if close(ch) == true:
            if failure == 0:
                set failure = 3.
        let refused = send(ch, 77).
        if refused.sent == true:
            if failure == 0:
                set failure = 4.
        if refused.value != 77:
            if failure == 0:
                set failure = 5.
        let drained = receive(ch).
        if drained.open == false:
            if failure == 0:
                set failure = 6.
        if drained.value != 10:
            if failure == 0:
                set failure = 7.
        let closed = receive(ch).
        if closed.open == true:
            if failure == 0:
                set failure = 8.
        if closed.value != 0:
            if failure == 0:
                set failure = 9.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-double-close");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-double-close/double_close"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn two_ready_arms_share_selection_over_repeated_waits() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "fairness.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let left = channel(i64, usize(1)).
        let right = channel(i64, usize(1)).
        let mut seen_left = 0.
        let mut seen_right = 0.
        let mut round = 0.
        while round < 8:
            let fill_left = send(left, round).
            if fill_left.sent == false:
                if failure == 0:
                    set failure = 1.
            let fill_right = send(right, round).
            if fill_right.sent == false:
                if failure == 0:
                    set failure = 2.
            let winner = wait_for(receive(left), receive(right)).
            if winner.status != 0:
                if failure == 0:
                    set failure = 3.
            if winner.index == 0:
                if winner.arm0.selected == false:
                    if failure == 0:
                        set failure = 4.
                if winner.arm0.value != round:
                    if failure == 0:
                        set failure = 5.
                set seen_left = 1.
                let spare = receive(right).
                if spare.open == false:
                    if failure == 0:
                        set failure = 6.
                if spare.value != round:
                    if failure == 0:
                        set failure = 7.
            else:
                if winner.index != 1:
                    if failure == 0:
                        set failure = 8.
                if winner.arm1.selected == false:
                    if failure == 0:
                        set failure = 9.
                if winner.arm1.value != round:
                    if failure == 0:
                        set failure = 10.
                set seen_right = 1.
                let spare = receive(left).
                if spare.open == false:
                    if failure == 0:
                        set failure = 11.
                if spare.value != round:
                    if failure == 0:
                        set failure = 12.
            set round = round + 1.
        if seen_left != 1:
            if failure == 0:
                set failure = 13.
        if seen_right != 1:
            if failure == 0:
                set failure = 14.
        channel_drop(left).
        channel_drop(right).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-fairness");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-fairness/fairness"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn wait_send_value_is_evaluated_exactly_once() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "eval_once.sal",
        r#"use "std/concurrency.sal".
use "std/buffer.sal".
operation Next:
    accepts cell of type MutBytes.
    returns i64.
    requires:
        len(cell) == usize(1).
    body:
        let observed = view(cell).
        let n = byte(observed, usize(0)).
        borrow_end(observed).
        put(cell, usize(0), n + u8(1)).
        return i64(n).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(1)).
        let cell = borrow_mut(arena, usize(0), usize(1)).
        put(cell, usize(0), u8(0)).
        let mut failure = 0.
        let ch = channel(i64, usize(1)).
        let winner = wait_for(send(ch, Next(cell)), timeout(usize(50))).
        if winner.status != 0:
            if failure == 0:
                set failure = 2.
        if winner.index != 0:
            if failure == 0:
                set failure = 3.
        if winner.arm0.selected == false:
            if failure == 0:
                set failure = 4.
        if winner.arm0.value != 0:
            if failure == 0:
                set failure = 5.
        if byte(view(cell), usize(0)) != u8(1):
            if failure == 0:
                set failure = 6.
        let got = receive(ch).
        if got.open == false:
            if failure == 0:
                set failure = 7.
        if got.value != 0:
            if failure == 0:
                set failure = 8.
        channel_drop(ch).
        borrow_end(cell).
        buffer_drop(arena).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-eval-once");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-eval-once/eval_once"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn concurrent_rendezvous_select_commits_exactly_one_then_drains_loser() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "race.sal",
        r#"use "std/concurrency.sal".
operation SenderOne:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        let sent = send(ch, 1).
        channel_drop(ch).
        if sent.sent == false:
            return 1.
        else:
            return 0.
operation SenderTwo:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        let sent = send(ch, 2).
        channel_drop(ch).
        if sent.sent == false:
            return 1.
        else:
            return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let a = channel(i64, usize(0)).
        let b = channel(i64, usize(0)).
        let a_worker = channel_clone(a).
        let b_worker = channel_clone(b).
        let first = spawn(SenderOne, a_worker).
        let second = spawn(SenderTwo, b_worker).
        let winner = wait_for(receive(a), receive(b)).
        if winner.status != 0:
            if failure == 0:
                set failure = 1.
        if winner.index == 0:
            if winner.arm0.selected == false:
                if failure == 0:
                    set failure = 2.
            if winner.arm0.value != 1:
                if failure == 0:
                    set failure = 3.
            let code_first = join(first).
            if code_first != 0:
                if failure == 0:
                    set failure = 4.
            if close(b) == false:
                if failure == 0:
                    set failure = 5.
            let drained = receive(b).
            if drained.open == true:
                if failure == 0:
                    set failure = 6.
            let code_second = join(second).
            if code_second != 1:
                if failure == 0:
                    set failure = 7.
        else:
            if winner.index != 1:
                if failure == 0:
                    set failure = 8.
            if winner.arm1.selected == false:
                if failure == 0:
                    set failure = 9.
            if winner.arm1.value != 2:
                if failure == 0:
                    set failure = 10.
            let code_second = join(second).
            if code_second != 0:
                if failure == 0:
                    set failure = 11.
            if close(a) == false:
                if failure == 0:
                    set failure = 12.
            let drained = receive(a).
            if drained.open == true:
                if failure == 0:
                    set failure = 13.
            let code_first = join(first).
            if code_first != 1:
                if failure == 0:
                    set failure = 14.
        channel_drop(a).
        channel_drop(b).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-race");
    success(&build);
    // The watchdog is the assertion: exactly one arm commits, the blocked
    // loser is released by close, and both joins complete before DEADLINE.
    let output = run_bounded(&fixture.0.join("out-race/race"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn join_preserves_negative_worker_return_without_checked_trap() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "negative.sal",
        r#"use "std/concurrency.sal".
operation Fail:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return 0 - 7.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let thread = spawn(Fail, 3).
        let code = join(thread).
        if code != 0 - 7:
            if failure == 0:
                set failure = 1.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-negative");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-negative/negative"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn worker_checked_overflow_traps_the_whole_group() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "overflow.sal",
        r#"use "std/concurrency.sal".
operation Overflow:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return value + 1.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let thread = spawn(Overflow, 9223372036854775807).
        let code = join(thread).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-overflow");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-overflow/overflow"));
    assert!(
        !output.status.success(),
        "checked overflow must fail, got {output:?}"
    );
    assert_eq!(
        output.status.signal(),
        Some(4),
        "checked overflow must trap with SIGILL, got {output:?}"
    );
}

#[test]
fn close_before_wait_reports_closed_every_iteration_under_stress() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "close_stress.sal",
        r#"use "std/concurrency.sal".
operation Closer:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        if close(ch) == false:
            channel_drop(ch).
            return 1.
        channel_drop(ch).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let mut round = 0.
        while round < 32:
            let ch = channel(i64, usize(0)).
            let worker_ch = channel_clone(ch).
            let thread = spawn(Closer, worker_ch).
            let got = wait_for(receive(ch), timeout(usize(20))).
            if got.status != 1:
                if failure == 0:
                    set failure = 1.
            if got.index != 0:
                if failure == 0:
                    set failure = 2.
            if got.arm0.selected == false:
                if failure == 0:
                    set failure = 3.
            if got.arm0.open == true:
                if failure == 0:
                    set failure = 4.
            if got.arm0.value != 0:
                if failure == 0:
                    set failure = 5.
            let code = join(thread).
            channel_drop(ch).
            if code != 0:
                if failure == 0:
                    set failure = 6.
            set round = round + 1.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-close-stress");
    success(&build);
    // The watchdog is the assertion: a lost close-wake under stress trips
    // DEADLINE before all 32 closed rounds complete.
    let output = run_bounded(&fixture.0.join("out-close-stress/close_stress"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn send_payload_type_mismatch_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "mismatch.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let sent = send(ch, bytes("hi")).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-mismatch");
    assert_rejected_code(&build, &fixture.0.join("out-mismatch/mismatch"), "CON");
}

#[test]
fn bytes_payload_channel_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "bytes_payload.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(Bytes, usize(1)).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-bytes-payload");
    assert_rejected_code(
        &build,
        &fixture.0.join("out-bytes-payload/bytes_payload"),
        "CON",
    );
}

#[test]
fn record_with_bytes_field_payload_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "blob_payload.sal",
        r#"use "std/concurrency.sal".
entity Blob:
    layout "C".
    has data of type Bytes.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(Blob, usize(1)).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-blob-payload");
    assert_rejected_code(
        &build,
        &fixture.0.join("out-blob-payload/blob_payload"),
        "CON",
    );
}

#[test]
fn record_with_channel_field_payload_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "carrier_payload.sal",
        r#"use "std/concurrency.sal".
entity Carrier:
    layout "C".
    has tag of type i64.
    has ch of type Channel<i64>.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(Carrier, usize(1)).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-carrier-payload");
    assert_rejected_code(
        &build,
        &fixture.0.join("out-carrier-payload/carrier_payload"),
        "CON",
    );
}

#[test]
fn channel_use_after_drop_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "usedrop.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        channel_drop(ch).
        let sent = send(ch, 1).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-usedrop");
    assert_rejected_code(&build, &fixture.0.join("out-usedrop/usedrop"), "CON");
}

#[test]
fn leaked_channel_without_drop_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "leak.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let sent = send(ch, 1).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-leak");
    assert_rejected_code(&build, &fixture.0.join("out-leak/leak"), "CON");
}

#[test]
fn channel_escape_into_ordinary_callee_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "escape.sal",
        r#"use "std/concurrency.sal".
operation Identity:
    accepts v of type i64.
    returns i64.
    body:
        return v.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let x = Identity(ch).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-escape");
    assert_rejected_code(&build, &fixture.0.join("out-escape/escape"), "CON");
}

#[test]
fn channel_use_after_spawn_move_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "usemove.sal",
        r#"use "std/concurrency.sal".
operation Take:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        let got = receive(ch).
        channel_drop(ch).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(0)).
        let worker_ch = channel_clone(ch).
        let t = spawn(Take, worker_ch).
        let s = send(worker_ch, 1).
        let code = join(t).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-usemove");
    assert_rejected_code(&build, &fixture.0.join("out-usemove/usemove"), "CON");
}

#[test]
fn ordinary_channel_callee_consume_then_caller_reuse_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "callee_consume.sal",
        r#"use "std/concurrency.sal".
operation Consume:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(ch).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let freed = Consume(ch).
        let retry = send(ch, 1).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-callee-consume");
    assert_rejected_code(
        &build,
        &fixture.0.join("out-callee-consume/callee_consume"),
        "CON",
    );
}

#[test]
fn branch_partial_drop_then_use_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "branchdrop.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        if true:
            channel_drop(ch).
        else:
            let ok = send(ch, 9).
        let s = send(ch, 1).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-branchdrop");
    assert_rejected_code(&build, &fixture.0.join("out-branchdrop/branchdrop"), "CON");
}

#[test]
fn concurrent_close_wakes_blocked_waiter_with_closed_status() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "close_wake.sal",
        r#"use "std/concurrency.sal".
operation Closer:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        if close(ch) == false:
            channel_drop(ch).
            return 1.
        channel_drop(ch).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(0)).
        let worker_ch = channel_clone(ch).
        let thread = spawn(Closer, worker_ch).
        let got = wait_for(receive(ch), timeout(usize(1000))).
        if got.status != 1:
            if failure == 0:
                set failure = 1.
        if got.index != 0:
            if failure == 0:
                set failure = 2.
        if got.arm0.selected == false:
            if failure == 0:
                set failure = 3.
        if got.arm0.open == true:
            if failure == 0:
                set failure = 4.
        if got.arm0.value != 0:
            if failure == 0:
                set failure = 5.
        let code = join(thread).
        channel_drop(ch).
        if code != 0:
            if failure == 0:
                set failure = 6.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-close-wake");
    success(&build);
    // The watchdog is the assertion: a lost close-wake deadlocks until the
    // 1000ms wait arm fires, and a missed close status fails the check above.
    let output = run_bounded(&fixture.0.join("out-close-wake/close_wake"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn double_join_of_the_same_thread_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "doublejoin.sal",
        r#"use "std/concurrency.sal".
operation Worker:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return value.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let thread = spawn(Worker, 7).
        let first = join(thread).
        let second = join(thread).
        if first != 7:
            return 1.
        return second.
"#,
    );
    let build = fixture.build(&source, "out-doublejoin");
    assert_rejected_code(&build, &fixture.0.join("out-doublejoin/doublejoin"), "CON");
}

#[test]
fn spawned_thread_without_join_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "nojoin.sal",
        r#"use "std/concurrency.sal".
operation Worker:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return value.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let thread = spawn(Worker, 7).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-nojoin");
    assert_rejected_code(&build, &fixture.0.join("out-nojoin/nojoin"), "CON");
}

#[test]
fn atomic_boundary_roundtrip_reports_prior_values() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "atomic.sal",
        r#"use "std/linux/memory.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapping = LinuxMapMemory(usize(4096)).
        if mapping < 0:
            return 1.
        let buf = usize(mapping).
        let mut failure = 0.
        store64(buf, usize(123456789)).
        if load64(buf) != usize(123456789):
            if failure == 0:
                set failure = 2.
        atomic_store(buf, u32(7)).
        if atomic_load(buf) != u32(7):
            if failure == 0:
                set failure = 3.
        if atomic_cas(buf, u32(7), u32(8)) != u32(7):
            if failure == 0:
                set failure = 4.
        if atomic_load(buf) != u32(8):
            if failure == 0:
                set failure = 5.
        if atomic_cas(buf, u32(7), u32(9)) != u32(8):
            if failure == 0:
                set failure = 6.
        if atomic_load(buf) != u32(8):
            if failure == 0:
                set failure = 7.
        let unmapped = LinuxUnmapMemory(buf, usize(4096)).
        if unmapped != 0:
            if failure == 0:
                set failure = 8.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-atomic");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-atomic/atomic"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn atomic_boundary_without_unsafe_memory_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "atomic_noeff.sal",
        r#"operation Main:
    returns i64.
    body:
        atomic_store(usize(4096), u32(1)).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-atomic-noeff");
    assert_rejected_code(
        &build,
        &fixture.0.join("out-atomic-noeff/atomic_noeff"),
        "EFF203",
    );
}

#[test]
fn erased_runtime_handles_cannot_bypass_the_safe_api() {
    for (index, call) in [
        "SalChannelClone(usize(4096))",
        "SalChannelDrop(usize(4096))",
        "SalChannelClose(usize(4096))",
        "SalThreadJoin(usize(4096))",
    ]
    .iter()
    .enumerate()
    {
        let fixture = Fixture::new();
        let source = fixture.source(
            "raw_handle.sal",
            &format!(
                r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        {call}.
        return 0.
"#
            ),
        );
        let output_dir = format!("out-raw-{index}");
        let build = fixture.build(&source, &output_dir);
        assert_rejected_code(
            &build,
            &fixture.0.join(output_dir).join("raw_handle"),
            "EFF203",
        );
    }
}

#[test]
fn generated_wrappers_cannot_be_called_with_forged_handles() {
    for call in [
        "SalConcChannelClone(usize(4096))",
        "SalConcChannelDrop(usize(4096))",
        "SalConcChannelClose(usize(4096))",
        "SalConcThreadJoin(usize(4096))",
    ] {
        let fixture = Fixture::new();
        let source = fixture.source(
            "forged_handle.sal",
            &format!(
                r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let channel = channel(i64, usize(1)).
        {call}.
        channel_drop(channel).
        return 0.
"#
            ),
        );
        let build = fixture.build(&source, "out-forged");
        assert_rejected_code(&build, &fixture.0.join("out-forged/forged_handle"), "E0004");
    }
}

#[test]
fn operation_address_with_wrong_callback_signature_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "bad_entry.sal",
        r#"operation BadWorker:
    returns i64.
    effects: SystemCall.
    body:
        return 0.
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let entry = operation_address(BadWorker).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-bad-entry");
    assert_rejected_code(&build, &fixture.0.join("out-bad-entry/bad_entry"), "B108");
}

#[test]
fn unaligned_atomic_address_traps_instead_of_splitting() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "unaligned.sal",
        r#"use "std/linux/memory.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapping = LinuxMapMemory(usize(4096)).
        if mapping < 0:
            return 1.
        let buf = usize(mapping).
        atomic_store(buf + usize(1), u32(7)).
        LinuxUnmapMemory(buf, usize(4096)).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-unaligned");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-unaligned/unaligned"));
    assert!(
        !output.status.success(),
        "unaligned atomic must fail, got {output:?}"
    );
    assert_eq!(
        output.status.signal(),
        Some(4),
        "unaligned atomic must trap with SIGILL, got {output:?}"
    );
}

#[test]
fn repeated_spawn_join_reclaims_stacks_with_bounded_regression() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "stress.sal",
        r#"use "std/concurrency.sal".
use "std/linux/process.sal".
operation One:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return value + 1.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        if LinuxSetAddressSpaceLimit(usize(67108864)) != 0:
            return 70.
        let mut total = 0.
        let mut index = 0.
        while index < 32:
            let thread = spawn(One, index).
            let code = join(thread).
            if code != index + 1:
                if failure == 0:
                    set failure = 1.
            set total = total + code.
            set index = index + 1.
        if total != 528:
            if failure == 0:
                set failure = 2.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-stress");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-stress/stress"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn checked_in_concurrency_fixtures_build_and_run_as_standalone_proof() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cases = [
        "bounded_drain.sal",
        "rendezvous_thread.sal",
        "wait_atomic.sal",
        "cancel_heterogeneous.sal",
        "atomic_boundary.sal",
        "spawn_stress.sal",
    ];
    for case in cases {
        let fixture = Fixture::new();
        let source = manifest.join("tests/fixtures/concurrency").join(case);
        let stem = case.trim_end_matches(".sal");
        let build = fixture.build(&source, &format!("out-{stem}"));
        success(&build);
        let output = run_bounded(&fixture.0.join(format!("out-{stem}/{stem}")));
        success(&output);
        assert!(
            output.stdout.is_empty(),
            "fixture {case} must be silent on success: {output:?}"
        );
    }
}

#[test]
fn channel_drop_on_thread_instead_of_join_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "dropthread.sal",
        r#"use "std/concurrency.sal".
operation Worker:
    accepts value of type i64.
    returns i64.
    effects: SystemCall.
    body:
        return value.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let thread = spawn(Worker, 7).
        channel_drop(thread).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-dropthread");
    assert_rejected_code(&build, &fixture.0.join("out-dropthread/dropthread"), "CON");
}

#[test]
fn dead_handle_usize_cast_after_drop_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "deadcast.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        channel_drop(ch).
        let raw = usize(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-deadcast");
    assert_rejected_code(&build, &fixture.0.join("out-deadcast/deadcast"), "CON");
}

#[test]
fn returns_channel_body_returns_usize_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "rethandle.sal",
        r#"use "std/concurrency.sal".
operation Make:
    returns Channel<i64>.
    effects: SystemCall.
    body:
        return usize(0).
operation Main:
    returns i64.
    body:
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-rethandle");
    assert_rejected_code(&build, &fixture.0.join("out-rethandle/rethandle"), "CON");
}

#[test]
fn returns_usize_body_returns_channel_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "rethandle2.sal",
        r#"use "std/concurrency.sal".
operation Make:
    returns usize.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        return ch.
operation Main:
    returns i64.
    body:
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-rethandle2");
    assert_rejected_code(&build, &fixture.0.join("out-rethandle2/rethandle2"), "CON");
}

#[test]
fn early_return_while_channel_live_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "earlyret.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        if true:
            return 0.
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-earlyret");
    assert_rejected_code(&build, &fixture.0.join("out-earlyret/earlyret"), "CON");
}

#[test]
fn callee_returning_channel_leaking_second_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "leaksecond.sal",
        r#"use "std/concurrency.sal".
operation Make:
    returns Channel<i64>.
    effects: SystemCall.
    body:
        let a = channel(i64, usize(1)).
        let b = channel(i64, usize(1)).
        return a.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = Make().
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-leaksecond");
    assert_rejected_code(&build, &fixture.0.join("out-leaksecond/leaksecond"), "CON");
}

#[test]
fn same_channel_twice_to_two_handle_callee_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "twice.sal",
        r#"use "std/concurrency.sal".
operation Two:
    accepts a of type Channel<i64>.
    accepts b of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(a).
        channel_drop(b).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let x = Two(ch, ch).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-twice");
    assert_rejected_code(&build, &fixture.0.join("out-twice/twice"), "CON");
}

#[test]
fn channel_i64_passed_as_channel_bool_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "wrongchan.sal",
        r#"use "std/concurrency.sal".
operation TakeBool:
    accepts b of type Channel<bool>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(b).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let x = TakeBool(ch).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-wrongchan");
    assert_rejected_code(&build, &fixture.0.join("out-wrongchan/wrongchan"), "CON");
}

#[test]
fn loop_inner_channel_break_leaks_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "loopbreak.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut index = 0.
        while index < 1:
            let inner = channel(i64, usize(1)).
            if true:
                break.
            channel_drop(inner).
            set index = index + 1.
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-loopbreak");
    assert_rejected_code(&build, &fixture.0.join("out-loopbreak/loopbreak"), "CON");
}

#[test]
fn shortcircuit_conditional_move_then_use_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "condmove.sal",
        r#"use "std/concurrency.sal".
operation Consume:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(ch).
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        if false && Consume(ch) == 0:
            return 1.
        let s = send(ch, 1).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-condmove");
    assert_rejected_code(&build, &fixture.0.join("out-condmove/condmove"), "CON");
}

#[test]
fn ordinary_callee_returned_channel_receives_and_drops() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "makechan.sal",
        r#"use "std/concurrency.sal".
operation Make:
    returns Channel<i64>.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        return ch.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = Make().
        let sent = send(ch, 5).
        if sent.sent == false:
            if failure == 0:
                set failure = 1.
        if sent.value != 5:
            if failure == 0:
                set failure = 2.
        let got = receive(ch).
        if got.open == false:
            if failure == 0:
                set failure = 3.
        if got.value != 5:
            if failure == 0:
                set failure = 4.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-makechan");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-makechan/makechan"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn wait_result_return_copy_flows_through_ordinary_callee() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "waitcopy.sal",
        r#"use "std/concurrency.sal".
operation Check:
    accepts winner of type WaitResult<i64, i64>.
    returns i64.
    body:
        if winner.status != 0:
            return 1.
        if winner.index == 0:
            if winner.arm0.selected == false:
                return 2.
            if winner.arm0.value != 11:
                return 3.
        else:
            if winner.index != 1:
                return 4.
            if winner.arm1.selected == false:
                return 5.
            if winner.arm1.value != 22:
                return 6.
        return 0.
operation Pick:
    returns WaitResult<i64, i64>.
    effects: SystemCall.
    body:
        let left = channel(i64, usize(1)).
        let right = channel(i64, usize(1)).
        let one = send(left, 11).
        let two = send(right, 22).
        let winner = wait_for(receive(left), receive(right)).
        channel_drop(left).
        channel_drop(right).
        return winner.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let w = Pick().
        if w.status != 0:
            if failure == 0:
                set failure = 1.
        if w.index == 0:
            if w.arm0.selected == false:
                if failure == 0:
                    set failure = 2.
            if w.arm0.value != 11:
                if failure == 0:
                    set failure = 3.
            if w.arm1.selected == true:
                if failure == 0:
                    set failure = 4.
        else:
            if w.index != 1:
                if failure == 0:
                    set failure = 5.
            if w.arm1.selected == false:
                if failure == 0:
                    set failure = 6.
            if w.arm1.value != 22:
                if failure == 0:
                    set failure = 7.
            if w.arm0.selected == true:
                if failure == 0:
                    set failure = 8.
        let checked = Check(w).
        if checked != 0:
            if failure == 0:
                set failure = 9.
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-waitcopy");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-waitcopy/waitcopy"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn unrelated_text_entity_coexists_with_concurrency() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "textentity.sal",
        r#"use "std/concurrency.sal".
entity Note:
    has text of type Text.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(1)).
        let sent = send(ch, 9).
        if sent.sent == false:
            if failure == 0:
                set failure = 1.
        if sent.value != 9:
            if failure == 0:
                set failure = 2.
        if "memo" != "memo":
            if failure == 0:
                set failure = 3.
        let got = receive(ch).
        if got.open == false:
            if failure == 0:
                set failure = 4.
        if got.value != 9:
            if failure == 0:
                set failure = 5.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-textentity");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-textentity/textentity"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn wait_send_on_u8_channel_reports_narrow_value() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "narrow.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(u8, usize(1)).
        let winner = wait_for(send(ch, 1)).
        if winner.status != 0:
            if failure == 0:
                set failure = 1.
        if winner.index != 0:
            if failure == 0:
                set failure = 2.
        if winner.arm0.selected == false:
            if failure == 0:
                set failure = 3.
        if winner.arm0.open == false:
            if failure == 0:
                set failure = 4.
        if winner.arm0.value != u8(1):
            if failure == 0:
                set failure = 5.
        let got = receive(ch).
        if got.open == false:
            if failure == 0:
                set failure = 6.
        if got.value != u8(1):
            if failure == 0:
                set failure = 7.
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-narrow");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-narrow/narrow"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn concurrency_without_effects_is_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "noeffects.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    body:
        let ch = channel(i64, usize(1)).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-noeffects");
    assert_rejected_code(&build, &fixture.0.join("out-noeffects/noeffects"), "EFF203");
}

#[test]
fn nested_wait_and_copyable_wait_arm_cross_typed_call_boundaries() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "nestedwait.sal",
        r#"use "std/concurrency.sal".
operation Arm:
    accepts winner of type WaitResult<i64>.
    returns WaitArm<i64>.
    body:
        return winner.arm0.
operation Check:
    accepts result of type WaitArm<i64>.
    returns i64.
    body:
        if result.selected == false:
            return 1.
        if result.open == false:
            return 2.
        if result.value != 41:
            return 3.
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let sent = send(ch, 41).
        let checked = Check(Arm(wait_for(receive(ch)))).
        channel_drop(ch).
        return checked.
"#,
    );
    let build = fixture.build(&source, "out-nestedwait");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-nestedwait/nestedwait"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn owned_temporaries_are_consumed_by_spawn_join_and_typed_calls() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "ownedtemps.sal",
        r#"use "std/concurrency.sal".
operation Make:
    returns Channel<i64>.
    effects: SystemCall.
    body:
        return channel(i64, usize(1)).
operation Worker:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(ch).
        return 7.
operation Join:
    accepts thread of type Thread<i64>.
    returns i64.
    effects: SystemCall.
    body:
        return join(thread).
operation Take:
    accepts ch of type Channel<i64>.
    returns i64.
    effects: SystemCall.
    body:
        channel_drop(ch).
        return 9.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let first = spawn(Worker, channel_clone(ch)).
        let a = Join(first).
        let b = Join(spawn(Worker, channel_clone(ch))).
        let c = join(spawn(Worker, Make())).
        let d = Take(channel_clone(ch)).
        channel_drop(ch).
        return a + b + c + d - 30.
"#,
    );
    let build = fixture.build(&source, "out-ownedtemps");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-ownedtemps/ownedtemps"));
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn result_signatures_are_declared_without_a_local_wait_expression() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "resultdecl.sal",
        r#"use "std/concurrency.sal".
operation Identity:
    accepts result of type WaitResult<i64, bool>.
    returns WaitResult<i64, bool>.
    body:
        return result.
operation Arm:
    accepts result of type WaitArm<i64>.
    returns WaitArm<i64>.
    body:
        return result.
operation Main:
    returns i64.
    body:
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-resultdecl");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-resultdecl/resultdecl"));
    success(&output);
}

#[test]
fn nested_wait_payload_and_timeout_operands_evaluate_once() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "nestedoperands.sal",
        r#"use "std/concurrency.sal".
operation Value:
    accepts result of type WaitResult<i64>.
    returns i64.
    body:
        return result.arm0.value + 1.
operation Milliseconds:
    accepts result of type WaitResult<i64>.
    returns usize.
    body:
        return usize(result.arm0.value).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let a = channel(i64, usize(1)).
        let b = channel(i64, usize(1)).
        let c = channel(i64, usize(1)).
        let winner = wait_for(send(a, Value(wait_for(send(b, 41)))), timeout(Milliseconds(wait_for(send(c, 0))))).
        let first = receive(a).
        let second = receive(b).
        let third = receive(c).
        channel_drop(a).
        channel_drop(b).
        channel_drop(c).
        return first.value + second.value + third.value - 83.
"#,
    );
    let build = fixture.build(&source, "out-nestedoperands");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-nestedoperands/nestedoperands"));
    success(&output);
}

#[test]
fn timeout_arithmetic_retains_unsigned_checked_context() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "timeoutunderflow.sal",
        r#"use "std/concurrency.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let ch = channel(i64, usize(1)).
        let selected = wait_for(send(ch, 7), timeout(1 - 2)).
        channel_drop(ch).
        return 0.
"#,
    );
    let build = fixture.build(&source, "out-timeoutunderflow");
    success(&build);
    let output = run_bounded(&fixture.0.join("out-timeoutunderflow/timeoutunderflow"));
    assert_eq!(output.status.signal(), Some(4), "{output:?}");
}

#[test]
fn concurrency_composes_with_collections_and_signed_binary_codecs() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "composition.sal",
        r#"use "std/concurrency.sal".
use "std/collections.sal".
use "std/binary.sal".
use "std/buffer.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let ch = channel(i64, usize(1)).
        let values = map(i64, i64, usize(2)).
        let arena = buffer(usize(8)).
        let scratch = borrow_mut(arena, usize(0), usize(8)).
        let sent = send(ch, bits_as(i64, u64(42))).
        let got = receive(ch).
        if sent.sent == false || got.open == false:
            set failure = 1.
        if map_insert(values, 7, got.value) != 0:
            set failure = 2.
        let found = map_get(values, 7).
        if found.found == false || found.value + 1 != 43:
            set failure = 3.
        if BinaryWriteI64Be(scratch, usize(0), 0 - 1) != 8:
            set failure = 4.
        let decoded = BinaryReadI64Be(view(scratch), usize(0)).
        if decoded.status != 0 || decoded.value != 0 - 1:
            set failure = 5.
        borrow_end(scratch).
        buffer_drop(arena).
        map_drop(values).
        channel_drop(ch).
        return failure.
"#,
    );
    let build = fixture.build(&source, "out-composition");
    success(&build);
    success(&run_bounded(&fixture.0.join("out-composition/composition")));
}

#[test]
fn warehouse_qa_builders_preserve_exact_nonnetwork_wire_bytes() {
    let fixture = Fixture::new();
    let helpers = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../apps/warehouse/tests");
    std::fs::copy(
        helpers.join("qa_payloads.sal"),
        fixture.0.join("qa_payloads.sal"),
    )
    .expect("copy real QA payload builders");
    let probe = r#"use "qa_payloads.sal".
operation Expect:
    accepts failure of type i64.
    accepts code of type i64.
    accepts holds of type bool.
    returns i64.
    requires:
        failure == 0 otherwise failure.
        holds otherwise code.
    body:
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let arena = buffer(usize(65600)).
        let work = borrow_mut(arena, usize(0), usize(65600)).
        let mut failure = 0.
        let raw = QaHexBody(slice_mut(work, usize(0), len(work)), bytes("7b22636f646573223a5b22ff225d7d")).
        set failure = Expect(failure, 1, len(raw) == usize(15) && byte(raw, usize(11)) == u8(255) && BytesStartsWith(raw, bytes("{\"codes\":[\""))).
        borrow_end(raw).
        let spaces = QaSpaces(slice_mut(work, usize(0), len(work)), 65537).
        set failure = Expect(failure, 2, len(spaces) == usize(65537) && byte(spaces, usize(0)) == u8(32) && byte(spaces, usize(65536)) == u8(32)).
        borrow_end(spaces).
        let long = QaLongCodeBody(slice_mut(work, usize(0), len(work)), 129).
        set failure = Expect(failure, 3, len(long) == usize(143) && BytesFind(long, bytes("xx\"]}")) == 138).
        borrow_end(long).
        let many = QaCodesBody(slice_mut(work, usize(0), len(work)), bytes("BATCH-"), 3, true).
        set failure = Expect(failure, 4, many == bytes("{\"codes\":[\"BATCH-2\",\"BATCH-1\",\"BATCH-0\"]}")).
        borrow_end(many).
        let code = QaCodeBody(slice_mut(work, usize(0), len(work)), bytes("q\"\\\n")).
        set failure = Expect(failure, 5, code == bytes("{\"codes\":[\"q\\\"\\\\\\u000a\"]}")).
        borrow_end(code).
        let marker = QaCountMarker(slice_mut(work, usize(0), len(work)), bytes("SKU-RED-M"), 10, 3).
        set failure = Expect(failure, 6, marker == bytes("\"code\":\"SKU-RED-M\",\"quantity\":10,\"reserved\":3,\"available_quantity\":7}")).
        borrow_end(marker).
        let stock = QaStockBody(slice_mut(work, usize(0), len(work)), 99999).
        set failure = Expect(failure, 7, stock == bytes("{\"warehouse_id\":99999}")).
        borrow_end(stock).
        let bound = QaBindThree(slice_mut(work, usize(0), len(work)), bytes("O'R"), bytes(""), bytes("Ё")).
        set failure = Expect(failure, 8, len(bound) == usize(17) && byte(bound, usize(3)) == u8(3) && byte(bound, usize(10)) == u8(0) && byte(bound, usize(14)) == u8(2)).
        borrow_end(bound).
        let head = QaRenamedHead(slice_mut(work, usize(0), len(work)), bytes("A\t")).
        set failure = Expect(failure, 9, head == bytes("{\"warehouse\":{\"id\":1,\"name\":\"A\\u0009\",\"available\":true},\"items\":[")).
        borrow_end(head).
        let row = QaQuotedRow(slice_mut(work, usize(0), len(work)), bytes("n"), bytes("s"), bytes("c")).
        set failure = Expect(failure, 10, row == bytes("{\"name\":\"n\",\"size\":\"s\",\"code\":\"c\",\"quantity\":2,\"reserved\":0,\"available_quantity\":2}")).
        borrow_end(row).
        borrow_end(work).
        buffer_drop(arena).
        return failure.
"#;
    let source = fixture.source("qa_builders.sal", probe);
    success(&fixture.build(&source, "out-qa-builders"));
    success(&run_bounded(&fixture.0.join("out-qa-builders/qa_builders")));
}
