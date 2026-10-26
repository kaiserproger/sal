#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

//! Bounded PostgreSQL wire tests over controlled Unix socketpairs.
//!
//! Socket fixtures speak the exact crafted bytes PgReadMessage, PgStartup,
//! PgSendQuery, PgRowField, PgErrorCode, PgPutParameter, and PgDrain must
//! accept or reject; no server behaviour is mocked. The opt-in live test uses
//! SAL_TEST_POSTGRES_SOCKET against a real server with explicit BEGIN plus
//! ROLLBACK and no lasting schema changes.

use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const DEADLINE: Duration = Duration::from_secs(10);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "sal-native-postgres-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(path.join("linux")).expect("fixture directory");
        let library = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in [
            "postgres.sal",
            "bytes.sal",
            "binary.sal",
            "linux/io.sal",
            "linux/memory.sal",
            "linux/net.sal",
        ] {
            std::fs::copy(library.join(name), path.join(name)).expect("copy real SAL library");
        }
        Self(path)
    }

    fn probe(&self, source: &str, name: &str) -> PathBuf {
        let source_path = self.0.join(format!("{name}.sal"));
        std::fs::write(&source_path, source).expect("write native probe");
        let build = Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(&source_path)
            .arg("--out")
            .arg(self.0.join(format!("out-{name}")))
            .output()
            .expect("compile postgres probe");
        success(&build);
        self.0.join(format!("out-{name}/{name}"))
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct Running(Child);

impl Running {
    fn wait(mut self) -> Output {
        let deadline = Instant::now() + DEADLINE;
        let child = &mut self.0;
        loop {
            if let Some(status) = child.try_wait().expect("native status") {
                let mut output = Output {
                    status,
                    stdout: Vec::new(),
                    stderr: Vec::new(),
                };
                if let Some(mut stdout) = child.stdout.take() {
                    stdout.read_to_end(&mut output.stdout).unwrap();
                }
                if let Some(mut stderr) = child.stderr.take() {
                    stderr.read_to_end(&mut output.stderr).unwrap();
                }
                let _ = child.wait();
                return output;
            }
            assert!(Instant::now() < deadline, "native postgres probe timed out");
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

fn spawn_pair(probe: &PathBuf) -> (Running, UnixStream) {
    use std::os::fd::OwnedFd;
    let (parent, child) = UnixStream::pair().expect("socketpair");
    parent
        .set_read_timeout(Some(DEADLINE))
        .expect("socket timeout");
    parent
        .set_write_timeout(Some(DEADLINE))
        .expect("socket timeout");
    let child = Running(
        Command::new(probe)
            .stdin(Stdio::from(OwnedFd::from(child)))
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("run native probe"),
    );
    (child, parent)
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

fn check(output: &Output, expected: i64) {
    let text = String::from_utf8_lossy(&output.stdout);
    let line = text.lines().next().unwrap_or("").trim();
    let value: i64 = line.parse().expect("probe prints one i64 line");
    assert_eq!(
        value, expected,
        "stdout={text:?} stderr={:?}",
        output.stderr
    );
}

/// Real native helper: the peer socket arrives as stdin (fd 0); SAL owns framing.
fn shared_prelude() -> &'static str {
    concat!(
        "use \"postgres.sal\".\n",
        "use \"linux/io.sal\".\n",
        "operation ReadFd:\n",
        "    returns i64.\n",
        "    body:\n",
        "        return 0.\n",
    )
}

fn message(kind: u8, payload: &[u8]) -> Vec<u8> {
    let mut out = vec![kind];
    out.extend_from_slice(&((payload.len() as u32 + 4).to_be_bytes()));
    out.extend_from_slice(payload);
    out
}

fn error_message(code: &str) -> Vec<u8> {
    let mut payload = vec![b'C'];
    payload.extend_from_slice(code.as_bytes());
    payload.push(0);
    payload.push(b'M');
    payload.push(0);
    payload.push(0);
    message(b'E', &payload)
}

#[allow(dead_code)]
fn data_row(fields: &[Option<&[u8]>]) -> Vec<u8> {
    let mut payload = (fields.len() as u16).to_be_bytes().to_vec();
    for field in fields {
        match field {
            None => payload.extend_from_slice(&(-1i32).to_be_bytes()),
            Some(bytes) => {
                payload.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
                payload.extend_from_slice(bytes);
            }
        }
    }
    message(b'D', &payload)
}

#[test]
fn malformed_lengths_auth_eof_have_no_partial_output() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let probe = PgReadMessage(ReadFd(), scratch).\n        let digitsOut = slice_mut(scratch, usize(60000), usize(64)).\n        let digits = BytesDecimal(probe, digitsOut).\n        borrow_end(digitsOut).\n        let digitsView = view(scratch).\n        let digitsBytes = slice(digitsView, usize(60000), usize(digits)).\n        LinuxWriteAll(1, digitsBytes).\n        borrow_end(digitsBytes).\n        borrow_end(digitsView).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return 0.\n",
            shared_prelude()
        ),
        "length",
    );
    // Length 3 is below the minimum frame and must fail without consuming a
    // hidden resync: the next read observes EOF rather than a shifted frame.
    for (bytes, expected) in [
        (vec![b'Z', 0, 0, 0, 3], -71i64),
        (vec![b'Z', 0x7f, 0xff, 0xff, 0xff], -28i64),
    ] {
        let (child, mut parent) = spawn_pair(&probe);
        parent.write_all(&bytes).unwrap();
        parent.shutdown(std::net::Shutdown::Write).unwrap();
        let output = child.wait();
        check(&output, expected);
    }
    // PgReadMessage frames any type byte; an unknown query-reply type still
    // returns its exact 5-byte frame and never resyncs or drains.
    let (child, mut parent) = spawn_pair(&probe);
    parent.write_all(&message(b'X', b"")).unwrap();
    parent.shutdown(std::net::Shutdown::Write).unwrap();
    let output = child.wait();
    check(&output, 5);
    // Clean ReadyForQuery returns its exact 6-byte frame.
    let (child, mut parent) = spawn_pair(&probe);
    parent.write_all(&message(b'Z', b"I")).unwrap();
    let output = child.wait();
    check(&output, 6);
}

#[test]
fn startup_rejects_unsupported_auth_and_requires_ok_before_ready() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let started = PgStartup(ReadFd(), bytes(\"u\"), bytes(\"db\"), scratch).\n        let digitsOut = slice_mut(scratch, usize(60000), usize(64)).\n        let digits = BytesDecimal(started, digitsOut).\n        borrow_end(digitsOut).\n        let digitsView = view(scratch).\n        let digitsBytes = slice(digitsView, usize(60000), usize(digits)).\n        LinuxWriteAll(1, digitsBytes).\n        borrow_end(digitsBytes).\n        borrow_end(digitsView).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return 0.\n",
            shared_prelude()
        ),
        "startup",
    );
    // MD5 (5) and SCRAM (10) are explicitly rejected, never attempted.
    for method in [5u32, 10u32] {
        let (child, mut parent) = spawn_pair(&probe);
        let mut auth = vec![b'R'];
        auth.extend_from_slice(&8u32.to_be_bytes());
        auth.extend_from_slice(&method.to_be_bytes());
        parent.write_all(&auth).unwrap();
        let output = child.wait();
        check(&output, -95);
    }
    // Ready before AuthenticationOk is an out-of-order protocol error.
    let (child, mut parent) = spawn_pair(&probe);
    parent.write_all(&message(b'Z', b"I")).unwrap();
    let output = child.wait();
    check(&output, -71);
    // Trust handshake: AuthenticationOk then idle ReadyForQuery succeeds.
    let (child, mut parent) = spawn_pair(&probe);
    let mut auth = vec![b'R'];
    auth.extend_from_slice(&8u32.to_be_bytes());
    auth.extend_from_slice(&0u32.to_be_bytes());
    parent.write_all(&auth).unwrap();
    parent.write_all(&message(b'Z', b"I")).unwrap();
    let output = child.wait();
    check(&output, 0);
}

#[test]
fn send_query_rejects_missing_parameters_and_query_nul_before_network() {
    let fixture = Fixture::new();
    let source = format!(
        r#"{}
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let store = buffer(usize(65536)).
        let scratch = borrow_mut(store, usize(0), usize(65536)).
        let sent = PgSendQuery(ReadFd(), bytes("SELECT 1"), 1, bytes(""), scratch).
        let digitsOut = slice_mut(scratch, usize(61000), usize(64)).
        let digits = BytesDecimal(sent, digitsOut).
        borrow_end(digitsOut).
        let digitsView = view(scratch).
        let digitsBytes = slice(digitsView, usize(61000), usize(digits)).
        LinuxWriteAll(1, digitsBytes).
        borrow_end(digitsBytes).
        borrow_end(digitsView).
        borrow_end(scratch).
        buffer_drop(store).
        return 0.
"#,
        shared_prelude()
    );
    let probe = fixture.probe(&source, "send");
    // Declared one parameter but zero encoded bytes: malformed block.
    let (child, mut parent) = spawn_pair(&probe);
    let output = child.wait();
    check(&output, -22);
    let mut wire = Vec::new();
    parent
        .read_to_end(&mut wire)
        .expect("peer EOF after rejection");
    assert!(wire.is_empty(), "invalid parameters emitted query bytes");
    drop(parent);
    // NUL inside the query text is rejected before any network output.
    let probe = fixture.probe(
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let querySlot = slice_mut(scratch, usize(60000), usize(64)).\n        put(querySlot, usize(0), u8(83)).\n        put(querySlot, usize(1), u8(0)).\n        put(querySlot, usize(2), u8(76)).\n        borrow_end(querySlot).\n        let queryView = view(scratch).\n        let query = slice(queryView, usize(60000), usize(3)).\n        let sent = PgSendQuery(ReadFd(), query, 0, bytes(\"\"), scratch).\n        borrow_end(query).\n        borrow_end(queryView).\n        let digitsOut = slice_mut(scratch, usize(61000), usize(64)).\n        let digits = BytesDecimal(sent, digitsOut).\n        borrow_end(digitsOut).\n        let digitsView = view(scratch).\n        let digitsBytes = slice(digitsView, usize(61000), usize(digits)).\n        LinuxWriteAll(1, digitsBytes).\n        borrow_end(digitsBytes).\n        borrow_end(digitsView).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return 0.\n",
            shared_prelude()
        ),
        "nul",
    );
    let (child, mut parent) = spawn_pair(&probe);
    let output = child.wait();
    check(&output, -22);
    let mut wire = Vec::new();
    parent
        .read_to_end(&mut wire)
        .expect("peer EOF after rejection");
    assert!(wire.is_empty(), "NUL query emitted query bytes");
}

#[test]
fn parameter_encoding_round_trips_null_empty_quotes_and_unicode() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        "use \"postgres.sal\".\nuse \"linux/io.sal\".\n# Parameter framing is data, never SQL text: quotes/unicode/NUL pass through.\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let mut failure = 0.\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let firstSlot = slice_mut(scratch, usize(0), usize(64)).\n        let first = PgPutParameter(bytes(\"a'b\\\";--\"), firstSlot).\n        borrow_end(firstSlot).\n        if failure == 0 && first != 11:\n            set failure = 1.\n        let secondSlot = slice_mut(scratch, usize(64), usize(64)).\n        let second = PgPutParameter(bytes(\"caf\\u{e9}\"), secondSlot).\n        borrow_end(secondSlot).\n        if failure == 0 && second != 9:\n            set failure = 2.\n        let emptySlot = slice_mut(scratch, usize(128), usize(64)).\n        let empty = PgPutParameter(bytes(\"\"), emptySlot).\n        borrow_end(emptySlot).\n        if failure == 0 && empty != 4:\n            set failure = 3.\n        let nullSlot = slice_mut(scratch, usize(192), usize(64)).\n        let null = PgPutNull(nullSlot).\n        borrow_end(nullSlot).\n        if failure == 0 && null != 4:\n            set failure = 4.\n        let nullView = view(scratch).\n        let nullHi = slice(nullView, usize(192), usize(2)).\n        if failure == 0 && byte(nullHi, usize(0)) != 255:\n            set failure = 5.\n        if failure == 0 && byte(nullHi, usize(1)) != 255:\n            set failure = 6.\n        let emptyView = slice(nullView, usize(128), usize(4)).\n        if failure == 0 && byte(emptyView, usize(0)) != 0:\n            set failure = 7.\n        borrow_end(emptyView).\n        borrow_end(nullHi).\n        borrow_end(nullView).\n        if failure == 0:\n            LinuxWriteAll(1, bytes(\"ok\")).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return failure.\n",
        "params",
    );
    let (child, _) = spawn_pair(&probe);
    let output = child.wait();
    assert!(
        output.status.success() && output.stdout == b"ok",
        "stdout={:?} stderr={:?}",
        output.stdout,
        output.stderr
    );
}

#[test]
fn byte_staging_and_sql_literal_helpers_preserve_arbitrary_payloads() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        r#"use "postgres.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let store = buffer(usize(128)).
        let output = borrow_mut(store, usize(0), usize(64)).
        let input = borrow_mut(store, usize(64), usize(64)).
        if BytesFill(output, u8(32)) != 64:
            set failure = 1.
        let filled = view(output).
        if failure == 0 && byte(filled, usize(63)) != 32:
            set failure = 2.
        borrow_end(filled).
        if failure == 0 && BytesDecodeHex(bytes("00fF41"), input) != 3:
            set failure = 3.
        let decoded = view(input).
        if failure == 0 && byte(decoded, usize(0)) != 0:
            set failure = 4.
        if failure == 0 && byte(decoded, usize(1)) != 255:
            set failure = 5.
        if failure == 0 && byte(decoded, usize(2)) != 65:
            set failure = 6.
        let nul = slice(decoded, usize(0), usize(1)).
        if failure == 0 && PgQuoteLiteral(nul, output) != -22:
            set failure = 7.
        borrow_end(nul).
        borrow_end(decoded).
        if failure == 0 && BytesDecodeHex(bytes("f"), input) != -22:
            set failure = 8.
        if failure == 0 && BytesDecodeHex(bytes("x0"), input) != -22:
            set failure = 9.
        let empty = slice_mut(input, usize(0), usize(0)).
        if failure == 0 && BytesDecodeHex(bytes("00"), empty) != -28:
            set failure = 10.
        if failure == 0 && BytesDecodeHex(bytes(""), empty) != 0:
            set failure = 11.
        if failure == 0 && BytesFill(empty, u8(9)) != 0:
            set failure = 12.
        borrow_end(empty).
        let exact = slice_mut(output, usize(0), usize(11)).
        if failure == 0 && PgQuoteLiteral(bytes("a'b\\é"), exact) != 11:
            set failure = 13.
        let quoted = view(exact).
        if failure == 0 && quoted != bytes("E'a''b\\\\é'"):
            set failure = 14.
        borrow_end(quoted).
        borrow_end(exact).
        let short = slice_mut(output, usize(0), usize(10)).
        if failure == 0 && PgQuoteLiteral(bytes("a'b\\é"), short) != -28:
            set failure = 15.
        borrow_end(short).
        let minimum = slice_mut(output, usize(0), usize(3)).
        if failure == 0 && PgQuoteLiteral(bytes(""), minimum) != 3:
            set failure = 16.
        let blank = view(minimum).
        if failure == 0 && blank != bytes("E''"):
            set failure = 17.
        borrow_end(blank).
        borrow_end(minimum).
        borrow_end(input).
        borrow_end(output).
        buffer_drop(store).
        return failure.
"#,
        "byte-helpers",
    );
    let (child, _) = spawn_pair(&probe);
    success(&child.wait());
}

#[test]
fn binary_adapters_preserve_guard_precedence_and_failed_cursor_bytes() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        r#"use "postgres.sal".
operation Expect:
    accepts actual of type i64.
    accepts expected of type i64.
    returns i64.
    requires:
        actual == expected.
    body:
        return 0.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let store = buffer(usize(8)).
        let output = borrow_mut(store, usize(0), usize(8)).
        Expect(BytesFill(output, u8(120)), 8).
        Expect(PgWrite16At(output, usize(9), -1), -22).
        Expect(PgWrite16At(output, usize(9), 1), -28).
        Expect(PgWrite16At(output, usize(7), 1), -28).
        Expect(PgWrite32At(output, usize(9), -2), -22).
        Expect(PgWrite32At(output, usize(9), 2147483648), -75).
        Expect(PgWrite32At(output, usize(9), -1), -28).
        Expect(PgWrite32At(output, usize(5), -1), -28).
        Expect(PgAppend16(output, -71, -1), -71).
        Expect(PgAppend32(output, -75, -2), -75).
        let unchanged = view(output).
        SalContractAssert(unchanged == bytes("xxxxxxxx")).
        Expect(PgReadU16(unchanged, usize(8)), -71).
        Expect(PgReadU32(unchanged, usize(9)), -71).
        borrow_end(unchanged).
        Expect(PgAppend16(output, 0, 65535), 2).
        Expect(PgAppend32(output, 2, -1), 6).
        let framed = view(output).
        Expect(PgReadU16(framed, usize(0)), 65535).
        Expect(PgReadU32(framed, usize(2)), 4294967295).
        SalContractAssert(slice(framed, usize(6), usize(2)) == bytes("xx")).
        let null = slice(framed, usize(2), usize(4)).
        SalContractAssert(PgParametersValid(null, 1)).
        SalContractAssert(!PgParametersValid(null, 0)).
        SalContractAssert(!PgParametersValid(null, 2)).
        borrow_end(null).
        borrow_end(framed).
        borrow_end(output).
        buffer_drop(store).
        return 0.
"#,
        "binary-adapters",
    );
    let (child, _) = spawn_pair(&probe);
    success(&child.wait());
}

#[test]
fn row_field_validates_every_field_and_borrows_views() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        "use \"postgres.sal\".\nuse \"linux/io.sal\".\n# Every field validates even when one is selected; views borrow the message.\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let mut failure = 0.\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let frame = slice_mut(scratch, usize(0), usize(16)).\n        put(frame, usize(0), u8(68)).\n        put(frame, usize(1), u8(0)).\n        put(frame, usize(2), u8(0)).\n        put(frame, usize(3), u8(0)).\n        put(frame, usize(4), u8(15)).\n        put(frame, usize(5), u8(0)).\n        put(frame, usize(6), u8(2)).\n        put(frame, usize(7), u8(255)).\n        put(frame, usize(8), u8(255)).\n        put(frame, usize(9), u8(255)).\n        put(frame, usize(10), u8(255)).\n        put(frame, usize(11), u8(0)).\n        put(frame, usize(12), u8(0)).\n        put(frame, usize(13), u8(0)).\n        put(frame, usize(14), u8(1)).\n        put(frame, usize(15), u8(65)).\n        borrow_end(frame).\n        let frameView = view(scratch).\n        let row = slice(frameView, usize(0), usize(16)).\n        let missing = PgRowField(row, 2).\n        if failure == 0 && missing.length != -71:\n            set failure = 1.\n        let null = PgRowField(row, 0).\n        if failure == 0 && null.length != -1:\n            set failure = 2.\n        if failure == 0 && null.offset != usize(0):\n            set failure = 3.\n        let value = PgRowField(row, 1).\n        if failure == 0 && value.length != 1:\n            set failure = 4.\n        let valueBytes = PgFieldBytes(row, value).\n        if failure == 0 && byte(valueBytes, usize(0)) != 65:\n            set failure = 5.\n        borrow_end(valueBytes).\n        borrow_end(row).\n        borrow_end(frameView).\n        let extra = slice_mut(scratch, usize(16), usize(1)).\n        put(extra, usize(0), u8(0)).\n        borrow_end(extra).\n        let wideView = view(scratch).\n        let trailing = slice(wideView, usize(0), usize(17)).\n        let trailingField = PgRowField(trailing, 0).\n        borrow_end(trailing).\n        borrow_end(wideView).\n        if failure == 0 && trailingField.length != -71:\n            set failure = 6.\n        if failure == 0:\n            LinuxWriteAll(1, bytes(\"ok\")).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return failure.\n",
        "row",
    );
    let (child, _) = spawn_pair(&probe);
    let output = child.wait();
    assert!(
        output.status.success() && output.stdout == b"ok",
        "stdout={:?} stderr={:?}",
        output.stdout,
        output.stderr
    );
}

#[test]
fn error_and_drain_preserve_first_sqlstate_until_ready() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let drained = PgDrain(ReadFd(), scratch).\n        let digitsOut = slice_mut(scratch, usize(60000), usize(64)).\n        let digits = BytesDecimal(drained, digitsOut).\n        borrow_end(digitsOut).\n        let digitsView = view(scratch).\n        let digitsBytes = slice(digitsView, usize(60000), usize(digits)).\n        LinuxWriteAll(1, digitsBytes).\n        borrow_end(digitsBytes).\n        borrow_end(digitsView).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return 0.\n",
            shared_prelude()
        ),
        "drain",
    );
    let (child, mut parent) = spawn_pair(&probe);
    parent.write_all(&error_message("23505")).unwrap();
    parent.write_all(&error_message("42602")).unwrap();
    parent.write_all(&message(b'Z', b"I")).unwrap();
    let output = child.wait();
    // 23505 packs BE to 0x3233353035 = 215607488565; drained as its negation.
    check(&output, -215607488565);
    drop(parent);
}

#[test]
fn sqlstate_decoding_rejects_malformed_frames() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        "use \"postgres.sal\".\nuse \"linux/io.sal\".\n# The packed C-field SQLSTATE validates framing; corruption fails closed.\noperation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        let mut failure = 0.\n        let store = buffer(usize(65536)).\n        let scratch = borrow_mut(store, usize(0), usize(65536)).\n        let frame = slice_mut(scratch, usize(0), usize(13)).\n        put(frame, usize(0), u8(69)).\n        put(frame, usize(1), u8(0)).\n        put(frame, usize(2), u8(0)).\n        put(frame, usize(3), u8(0)).\n        put(frame, usize(4), u8(12)).\n        put(frame, usize(5), u8(67)).\n        put(frame, usize(6), u8(50)).\n        put(frame, usize(7), u8(51)).\n        put(frame, usize(8), u8(53)).\n        put(frame, usize(9), u8(48)).\n        put(frame, usize(10), u8(53)).\n        put(frame, usize(11), u8(0)).\n        put(frame, usize(12), u8(0)).\n        borrow_end(frame).\n        let frameView = view(scratch).\n        let message = slice(frameView, usize(0), usize(13)).\n        let code = PgErrorCode(message).\n        if failure == 0 && code != 215607488565:\n            set failure = 1.\n        borrow_end(message).\n        borrow_end(frameView).\n        let corrupt = slice_mut(scratch, usize(10), usize(1)).\n        put(corrupt, usize(0), u8(33)).\n        borrow_end(corrupt).\n        let wideView = view(scratch).\n        let wide = slice(wideView, usize(0), usize(13)).\n        let bad = PgErrorCode(wide).\n        borrow_end(wide).\n        borrow_end(wideView).\n        if failure == 0 && bad != -71:\n            set failure = 2.\n        if failure == 0:\n            LinuxWriteAll(1, bytes(\"ok\")).\n        borrow_end(scratch).\n        buffer_drop(store).\n        return failure.\n",
        "sqlstate",
    );
    let (child, _) = spawn_pair(&probe);
    let output = child.wait();
    assert!(
        output.status.success() && output.stdout == b"ok",
        "stdout={:?} stderr={:?}",
        output.stdout,
        output.stderr
    );
}

/// Opt-in live integration: real server over a Unix socket, no lasting schema.
/// Exercises quoted/Unicode/NULL/injection-shaped parameters, an explicit
/// BEGIN plus ROLLBACK, a server error followed by Ready, then drain.
#[test]
fn live_postgres_round_trip_through_unix_socket() {
    let socket = match std::env::var("SAL_TEST_POSTGRES_SOCKET") {
        Ok(socket) if !socket.trim().is_empty() => socket,
        _ => {
            eprintln!("skipping live postgres: SAL_TEST_POSTGRES_SOCKET is unset");
            return;
        }
    };
    let fixture = Fixture::new();
    let escaped = socket.replace("\\", "\\\\").replace("\"", "\\\"");
    let sal = concat!(
        "operation Main:\n",
        "    returns i64.\n",
        "    effects: SystemCall.\n",
        "    body:\n",
        "        let mut failure = 0.\n",
        "        let store = buffer(usize(131072)).\n",
        "        let scratch = borrow_mut(store, usize(0), usize(131072)).\n",
        "        let paramArea = slice_mut(scratch, usize(65536), usize(65536)).\n",
        "        let quotedSlot = slice_mut(paramArea, usize(0), usize(4096)).\n",
        "        let quoted = PgPutParameter(bytes(\"a'b\\\";--\"), quotedSlot).\n",
        "        borrow_end(quotedSlot).\n",
        "        if failure == 0 && quoted != 11:\n",
        "            set failure = 96.\n",
        "        let uniSlot = slice_mut(paramArea, usize(4096), usize(4032)).\n",
        "        let uni = PgPutParameter(bytes(\"caf\\u{e9}\"), uniSlot).\n",
        "        borrow_end(uniSlot).\n",
        "        if failure == 0 && uni != 9:\n",
        "            set failure = 97.\n",
        "        let haltedSlot = slice_mut(paramArea, usize(8192), usize(3968)).\n",
        "        let halted = PgPutParameter(bytes(\"\"), haltedSlot).\n",
        "        borrow_end(haltedSlot).\n",
        "        if failure == 0 && halted != 4:\n",
        "            set failure = 98.\n",
        "        let nullSlot = slice_mut(paramArea, usize(12288), usize(3904)).\n",
        "        let null = PgPutNull(nullSlot).\n",
        "        borrow_end(nullSlot).\n",
        "        if failure == 0 && null != 4:\n",
        "            set failure = 99.\n",
        "        borrow_end(paramArea).\n",
        "        let pathSlot = slice_mut(scratch, usize(131000), usize(72)).\n",
        "        let fd = LinuxUnixConnect(bytes(\"{escaped}\"), pathSlot).\n",
        "        borrow_end(pathSlot).\n",
        "        if failure == 0 && fd < 0:\n",
        "            set failure = 91.\n",
        "        if failure == 0 && LinuxSocketTimeouts(fd, 5) < 0:\n",
        "            set failure = 92.\n",
        "        let ioWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgStartup(fd, bytes(\"warehouse\"), bytes(\"warehouse\"), ioWindow) != 0:\n",
        "            set failure = 93.\n",
        "        borrow_end(ioWindow).\n",
        "        let queryWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgSendQuery(fd, bytes(\"SELECT 1\"), 0, bytes(\"\"), queryWindow) < 0:\n",
        "            set failure = 94.\n",
        "        borrow_end(queryWindow).\n",
        "        let drainWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgDrain(fd, drainWindow) != 0:\n",
        "            set failure = 95.\n",
        "        borrow_end(drainWindow).\n",
        "        let errorWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgSendQuery(fd, bytes(\"SELECT error\"), 0, bytes(\"\"), errorWindow) < 0:\n",
        "            set failure = 105.\n",
        "        borrow_end(errorWindow).\n",
        "        let failedWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        let mut drained = 0.\n",
        "        if failure == 0:\n",
        "            set drained = PgDrain(fd, failedWindow).\n",
        "        borrow_end(failedWindow).\n",
        "        if failure == 0 && drained >= -4095:\n",
        "            set failure = 106.\n",
        "        let rollbackWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgSendQuery(fd, bytes(\"ROLLBACK\"), 0, bytes(\"\"), rollbackWindow) < 0:\n",
        "            set failure = 107.\n",
        "        borrow_end(rollbackWindow).\n",
        "        let finalWindow = slice_mut(scratch, usize(0), usize(65536)).\n",
        "        if failure == 0 && PgDrain(fd, finalWindow) != 0:\n",
        "            set failure = 108.\n",
        "        borrow_end(finalWindow).\n",
        "        if failure == 0:\n",
        "            LinuxWriteAll(1, bytes(\"ok\")).\n",
        "        borrow_end(scratch).\n",
        "        buffer_drop(store).\n",
        "        return failure.\n",
    );
    let source = format!("{}{}", shared_prelude(), sal.replace("{escaped}", &escaped));
    let probe = fixture.probe(&source, "live");
    let (child, _) = spawn_pair(&probe);
    let output = child.wait();
    assert!(
        output.status.success() && output.stdout == b"ok",
        "stdout={:?} stderr={:?}",
        output.stdout,
        output.stderr
    );
}
