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
        "use \"linux/memory.sal\".\n",
        "use \"linux/net.sal\".\n",
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
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        let probe = PgReadMessage(ReadFd(), scratch, usize(65536)).\n        let digits = BytesDecimal(probe, scratch + 60000, usize(64)).\n        LinuxWriteAll(1, bytes_at(scratch + 60000, usize(digits))).\n        return 0.\n",
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
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        let started = PgStartup(ReadFd(), bytes(\"u\"), bytes(\"db\"), scratch, usize(65536)).\n        let digits = BytesDecimal(started, scratch + 60000, usize(64)).\n        LinuxWriteAll(1, bytes_at(scratch + 60000, usize(digits))).\n        return 0.\n",
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
    effects: SystemCall, UnsafeMemory.
    body:
        let mapping = LinuxMapMemory(usize(65536)).
        if mapping < 0:
            return 90.
        let scratch = usize(mapping).
        let sent = PgSendQuery(ReadFd(), bytes("SELECT 1"), 1, bytes(""), scratch, usize(65536)).
        let digits = BytesDecimal(sent, scratch + 61000, usize(64)).
        LinuxWriteAll(1, bytes_at(scratch + 61000, usize(digits))).
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
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        store8(scratch + 60000, u8(83)).\n        store8(scratch + 60001, u8(0)).\n        store8(scratch + 60002, u8(76)).\n        let sent = PgSendQuery(ReadFd(), bytes_at(scratch + 60000, usize(3)), 0, bytes(\"\"), scratch, usize(65536)).\n        let digits = BytesDecimal(sent, scratch + 61000, usize(64)).\n        LinuxWriteAll(1, bytes_at(scratch + 61000, usize(digits))).\n        return 0.\n",
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
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        let first = PgPutParameter(bytes(\"a'b\\\";--\"), scratch, usize(64)).\n        if first != 11:\n            return 1.\n        let second = PgPutParameter(bytes(\"caf\\u{{e9}}\"), scratch + 64, usize(64)).\n        if second != 9:\n            return 2.\n        let empty = PgPutParameter(bytes(\"\"), scratch + 128, usize(64)).\n        if empty != 4:\n            return 3.\n        let null = PgPutNull(scratch + 192, usize(64)).\n        if null != 4:\n            return 4.\n        if load8(scratch + 192) != 255:\n            return 5.\n        if load8(scratch + 193) != 255:\n            return 6.\n        if load8(scratch + 128) != 0:\n            return 7.\n        # Exact self placement writes only the length prefix in place.\n        let decoded = usize(scratch + 1024).\n        store8(decoded + 4, u8(120)).\n        let placed = PgPutParameter(bytes_at(decoded + 4, usize(1)), decoded, usize(64)).\n        if placed != 5:\n            return 8.\n        if load8(decoded) != 0:\n            return 9.\n        if load8(decoded + 4) != 120:\n            return 10.\n        LinuxWriteAll(1, bytes(\"ok\")).\n        return 0.\n",
            shared_prelude()
        ),
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
fn row_field_validates_every_field_and_borrows_views() {
    let fixture = Fixture::new();
    let probe = fixture.probe(
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        store8(scratch, u8(68)).\n        store8(scratch + 1, u8(0)).\n        store8(scratch + 2, u8(0)).\n        store8(scratch + 3, u8(0)).\n        store8(scratch + 4, u8(15)).\n        store8(scratch + 5, u8(0)).\n        store8(scratch + 6, u8(2)).\n        store8(scratch + 7, u8(255)).\n        store8(scratch + 8, u8(255)).\n        store8(scratch + 9, u8(255)).\n        store8(scratch + 10, u8(255)).\n        store8(scratch + 11, u8(0)).\n        store8(scratch + 12, u8(0)).\n        store8(scratch + 13, u8(0)).\n        store8(scratch + 14, u8(1)).\n        store8(scratch + 15, u8(65)).\n        let row = bytes_at(scratch, usize(16)).\n        let missing = PgRowField(row, 2).\n        if missing.length != -71:\n            return 1.\n        let null = PgRowField(row, 0).\n        if null.length != -1:\n            return 2.\n        if null.pointer != usize(0):\n            return 3.\n        let value = PgRowField(row, 1).\n        if value.length != 1:\n            return 4.\n        if load8(value.pointer) != 65:\n            return 5.\n        # Trailing byte after the declared fields fails closed.\n        store8(scratch + 16, u8(0)).\n        let trailing = PgRowField(bytes_at(scratch, usize(17)), 0).\n        if trailing.length != -71:\n            return 6.\n        LinuxWriteAll(1, bytes(\"ok\")).\n        return 0.\n",
            shared_prelude()
        ),
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
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        let drained = PgDrain(ReadFd(), scratch, usize(65536)).\n        let digits = BytesDecimal(drained, scratch + 60000, usize(64)).\n        LinuxWriteAll(1, bytes_at(scratch + 60000, usize(digits))).\n        return 0.\n",
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
        &format!(
            "{}\noperation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n        let mapping = LinuxMapMemory(usize(65536)).\n        if mapping < 0:\n            return 90.\n        let scratch = usize(mapping).\n        store8(scratch, u8(69)).\n        store8(scratch + 1, u8(0)).\n        store8(scratch + 2, u8(0)).\n        store8(scratch + 3, u8(0)).\n        store8(scratch + 4, u8(12)).\n        store8(scratch + 5, u8(67)).\n        store8(scratch + 6, u8(50)).\n        store8(scratch + 7, u8(51)).\n        store8(scratch + 8, u8(53)).\n        store8(scratch + 9, u8(48)).\n        store8(scratch + 10, u8(53)).\n        store8(scratch + 11, u8(0)).\n        store8(scratch + 12, u8(0)).\n        let code = PgErrorCode(bytes_at(scratch, usize(13))).\n        if code != 215607488565:\n            return 1.\n        store8(scratch + 10, u8(33)).\n        let bad = PgErrorCode(bytes_at(scratch, usize(13))).\n        if bad != -71:\n            return 2.\n        LinuxWriteAll(1, bytes(\"ok\")).\n        return 0.\n",
            shared_prelude()
        ),
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
        "    effects: SystemCall, UnsafeMemory.\n",
        "    body:\n",
        "        let mapping = LinuxMapMemory(usize(131072)).\n",
        "        if mapping < 0:\n",
        "            return 90.\n",
        "        let scratch = usize(mapping).\n",
        "        let output = scratch + 65536.\n",
        "        let quoted = PgPutParameter(bytes(\"a'b\\\";--\"), output, usize(4096)).\n",
        "        if quoted != 11:\n",
        "            return 96.\n",
        "        let uni = PgPutParameter(bytes(\"caf\\u{e9}\"), output + 64, usize(4032)).\n",
        "        if uni != 9:\n",
        "            return 97.\n",
        "        let halted = PgPutParameter(bytes(\"\"), output + 128, usize(3968)).\n",
        "        if halted != 4:\n",
        "            return 98.\n",
        "        let null = PgPutNull(output + 192, usize(3904)).\n",
        "        if null != 4:\n",
        "            return 99.\n",
        "        let fd = LinuxUnixConnect(bytes(\"{escaped}\"), scratch + 131000).\n",
        "        if fd < 0:\n",
        "            return 91.\n",
        "        if LinuxSocketTimeouts(fd, 5) < 0:\n",
        "            return 92.\n",
        "        if PgStartup(fd, bytes(\"warehouse\"), bytes(\"warehouse\"), scratch, usize(65536)) != 0:\n",
        "            return 93.\n",
        "        if PgSendQuery(fd, bytes(\"SELECT 1\"), 0, bytes(\"\"), scratch, usize(65536)) < 0:\n",
        "            return 94.\n",
        "        if PgDrain(fd, scratch, usize(65536)) != 0:\n",
        "            return 95.\n",
        "        if PgSendQuery(fd, bytes(\"SELECT error\"), 0, bytes(\"\"), scratch, usize(65536)) < 0:\n",
        "            return 105.\n",
        "        let drained = PgDrain(fd, scratch, usize(65536)).\n",
        "        if drained >= -4095:\n",
        "            return 106.\n",
        "        if PgSendQuery(fd, bytes(\"ROLLBACK\"), 0, bytes(\"\"), scratch, usize(65536)) < 0:\n",
        "            return 107.\n",
        "        if PgDrain(fd, scratch, usize(65536)) != 0:\n",
        "            return 108.\n",
        "        LinuxWriteAll(1, bytes(\"ok\")).\n",
        "        return 0.\n",
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
