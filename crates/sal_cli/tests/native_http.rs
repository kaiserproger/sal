#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const DEADLINE: Duration = Duration::from_secs(10);

struct Fixture(PathBuf);

impl Fixture {
    fn build(source: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "sal-http-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let fixture = Self(root);
        std::fs::create_dir_all(fixture.0.join("linux")).expect("fixture directory");
        let stdlib = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in ["http.sal", "bytes.sal", "linux/io.sal"] {
            std::fs::copy(stdlib.join(name), fixture.0.join(name)).expect("copy real SAL library");
        }
        std::fs::write(fixture.0.join("probe.sal"), source).expect("write probe");
        let output = Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(fixture.0.join("probe.sal"))
            .arg("--out")
            .arg(fixture.0.join("out"))
            .output()
            .expect("compile native HTTP probe");
        assert!(
            output.status.success(),
            "SAL compilation failed: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        fixture
    }

    fn spawn(&self) -> NativeChild {
        NativeChild(
            Command::new(self.0.join("out/probe"))
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("start native HTTP probe"),
        )
    }

    fn run(&self, input: &[u8]) -> Vec<u8> {
        let mut child = self.spawn();
        if let Err(error) = child.0.stdin.take().unwrap().write_all(input) {
            assert_eq!(
                error.kind(),
                std::io::ErrorKind::BrokenPipe,
                "input: {error}"
            );
        }
        child.finish()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct NativeChild(Child);

impl NativeChild {
    fn finish(mut self) -> Vec<u8> {
        drop(self.0.stdin.take());
        let deadline = Instant::now() + DEADLINE;
        let status = loop {
            if let Some(status) = self.0.try_wait().expect("poll native child") {
                break status;
            }
            assert!(Instant::now() < deadline, "native HTTP probe timed out");
            std::thread::sleep(Duration::from_millis(1));
        };
        let mut stdout = Vec::new();
        self.0
            .stdout
            .take()
            .unwrap()
            .read_to_end(&mut stdout)
            .unwrap();
        let mut stderr = String::new();
        self.0
            .stderr
            .take()
            .unwrap()
            .read_to_string(&mut stderr)
            .unwrap();
        assert!(
            status.success(),
            "status={status}, stderr={stderr}, stdout={stdout:?}"
        );
        stdout
    }

    // Synchronize with a real blocked read, not sleeps or a mocked I/O wrapper.
    // The next fragment is sent only after the preceding read has completed.
    fn wait_for_read(&mut self, count: usize) {
        let deadline = Instant::now() + DEADLINE;
        loop {
            let syscall = std::fs::read_to_string(format!("/proc/{}/syscall", self.0.id()))
                .expect("Linux parent must be able to observe its child's blocked syscall");
            let fields: Vec<_> = syscall.split_whitespace().collect();
            if fields.len() >= 4 && fields[0] == "0" && fields[1] == "0x0" {
                let pending = usize::from_str_radix(fields[3].trim_start_matches("0x"), 16)
                    .expect("read byte count");
                if pending == count {
                    return;
                }
            }
            assert!(
                self.0.try_wait().unwrap().is_none(),
                "child exited before read: {syscall}"
            );
            assert!(
                Instant::now() < deadline,
                "expected read({count}), observed {syscall}"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
    }
}

impl Drop for NativeChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn reader(capacity: usize) -> Fixture {
    Fixture::build(&format!(
        r#"use "http.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = syscall(9, 0, 65536, 3, 34, -1, 0).
        if mapped < 0:
            return 90.
        let buffer = usize(mapped).
        let scratch = buffer + 32768.
        let result = HttpReadRequest(0, buffer, usize({capacity})).
        let digits = BytesDecimal(result, scratch, usize(64)).
        LinuxWriteAll(1, bytes_at(scratch, usize(digits))).
        LinuxWriteAll(1, bytes("\n")).
        if result >= 0:
            let request = bytes_at(buffer, usize(result)).
            LinuxWriteAll(1, HttpMethod(request)).
            LinuxWriteAll(1, bytes("\n")).
            LinuxWriteAll(1, HttpPath(request)).
            LinuxWriteAll(1, bytes("\n")).
            let offset = usize(HttpBodyOffset(request)).
            LinuxWriteAll(1, slice(request, offset, len(request) - offset)).
        return 0.
"#
    ))
}

fn accepted(request: &[u8], method: &str, path: &str, body: &[u8]) -> Vec<u8> {
    let mut output = format!("{}\n{method}\n{path}\n", request.len()).into_bytes();
    output.extend_from_slice(body);
    output
}

#[test]
fn fragmented_headers_and_binary_body_are_framed_without_waiting_for_eof() {
    let fixture = reader(20000);
    let mut child = fixture.spawn();
    child.wait_for_read(16384);
    let pieces: [&[u8]; 4] = [
        b"POST /items?q=ignored HTTP/1.1\r\nCont",
        b"ent-Length: 5\r\nX-Test: yes\r",
        b"\n\r",
        b"\n\0",
    ];
    let mut request = Vec::new();
    for (index, piece) in pieces.iter().enumerate() {
        child.0.stdin.as_mut().unwrap().write_all(piece).unwrap();
        request.extend_from_slice(piece);
        if index + 1 < pieces.len() {
            child.wait_for_read(16384 - request.len());
        }
    }
    child.wait_for_read(4);
    child
        .0
        .stdin
        .as_mut()
        .unwrap()
        .write_all(&[255, 13])
        .unwrap();
    request.extend_from_slice(&[255, 13]);
    child.wait_for_read(2);
    child
        .0
        .stdin
        .as_mut()
        .unwrap()
        .write_all(&[10, 128])
        .unwrap();
    request.extend_from_slice(&[10, 128]);
    // Keep the input open until exit: Content-Length, not EOF, completes the read.
    let input = child.0.stdin.take().unwrap();
    assert_eq!(
        child.finish(),
        accepted(&request, "POST", "/items", &[0, 255, 13, 10, 128])
    );
    drop(input);
}

#[test]
fn strict_request_lines_headers_and_lengths_reject_ambiguous_framing() {
    let fixture = reader(20000);
    let malformed: &[&[u8]] = &[
        b"",
        b"G",
        b"GET / HTTP/1.1\r\n",
        b"GET / HTTP/2.0\r\n\r\n",
        b"GET / HTTP/1.2\r\n\r\n",
        b"GET / HTTP/1.10\r\n\r\n",
        b"GET / HTTP/1.1 extra\r\n\r\n",
        b"GET / HTTP/1.\r\n\r\n",
        b"GET / http/1.1\r\n\r\n",
        b" / HTTP/1.1\r\n\r\n",
        b"GE(T / HTTP/1.1\r\n\r\n",
        b"GET  HTTP/1.1\r\n\r\n",
        b"GET http://example/ HTTP/1.1\r\n\r\n",
        b"GET /#fragment HTTP/1.1\r\n\r\n",
        b"GET /\x01 HTTP/1.1\r\n\r\n",
        b"GET / HTTP/1.1\r\n folded: value\r\n\r\n",
        b"GET / HTTP/1.1\r\n\tfolded\r\n\r\n",
        b"GET / HTTP/1.1\r\nBad Name: value\r\n\r\n",
        b"GET / HTTP/1.1\r\n: value\r\n\r\n",
        b"GET / HTTP/1.1\r\nMissing-Colon\r\n\r\n",
        b"GET / HTTP/1.1\r\nX: value\x00\r\n\r\n",
        b"GET / HTTP/1.1\r\nX: value\x7f\r\n\r\n",
        b"GET / HTTP/1.1\r\nX: value\nother\r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length: 1\r\ncontent-length: 1\r\n\r\nx",
        b"POST / HTTP/1.1\r\nContent-Length: 1\r\nContent-Length: 2\r\n\r\nxx",
        b"POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n",
        b"POST / HTTP/1.1\r\ntRaNsFeR-EnCoDiNg: identity\r\nContent-Length: 0\r\n\r\n",
        b"POST / HTTP/1.1\r\nTransfer-Encoding:\r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length:\r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length: \t \r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length: +1\r\n\r\nx",
        b"POST / HTTP/1.1\r\nContent-Length: -1\r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length: 1, 1\r\n\r\nx",
        b"POST / HTTP/1.1\r\nContent-Length: 1 0\r\n\r\n",
        b"POST / HTTP/1.1\r\nContent-Length: 0x1\r\n\r\nx",
        b"POST / HTTP/1.1\r\nContent-Length: 3\r\n\r\nab",
    ];
    for request in malformed {
        assert_eq!(fixture.run(request), b"-400\n", "request={request:?}");
    }
    for length in [
        "9223372036854775807",
        "9223372036854775808",
        "18446744073709551616",
        "999999999999999999999999999999999999999",
    ] {
        let request = format!("POST / HTTP/1.1\r\nContent-Length: {length}\r\n\r\n");
        // Do not close stdin: overflow/capacity must be rejected before body read.
        let mut child = fixture.spawn();
        child
            .0
            .stdin
            .as_mut()
            .unwrap()
            .write_all(request.as_bytes())
            .unwrap();
        let input = child.0.stdin.take().unwrap();
        assert_eq!(child.finish(), b"-413\n", "length={length}");
        drop(input);
    }
}

#[test]
fn valid_versions_case_insensitive_lengths_and_pipelined_bytes() {
    let fixture = reader(20000);
    for version in ["HTTP/1.0", "HTTP/1.1"] {
        let request = format!("PATCH /a/b?x=y {version}\r\ncOnTeNt-LeNgTh:\t0003 \t\r\nX-Empty:\r\nX-Tab: a\tb\r\n\r\nabc").into_bytes();
        let mut pipeline = request.clone();
        pipeline.extend_from_slice(b"GET /second HTTP/1.1\r\n\r\n");
        assert_eq!(
            fixture.run(&pipeline),
            accepted(&request, "PATCH", "/a/b", b"abc")
        );
    }
    let request = b"GET /?x HTTP/1.1\r\nX-Byte: \xff\r\n\r\n";
    let mut extra = request.to_vec();
    extra.extend_from_slice(b"not a body without content length");
    assert_eq!(fixture.run(&extra), accepted(request, "GET", "/", b""));
}

#[test]
fn header_and_total_capacity_boundaries_are_distinct() {
    let fixture = reader(20000);
    let prefix = b"GET / HTTP/1.1\r\nX-Pad: ";
    let mut request = prefix.to_vec();
    request.resize(16384 - 4, b'a');
    request.extend_from_slice(b"\r\n\r\n");
    assert_eq!(fixture.run(&request), accepted(&request, "GET", "/", b""));
    request.insert(prefix.len(), b'a');
    assert_eq!(fixture.run(&request), b"-431\n");

    let small = reader(96);
    let header = b"POST / HTTP/1.1\r\nContent-Length: 57\r\n\r\n";
    assert_eq!(header.len(), 39);
    let mut exact = header.to_vec();
    exact.extend_from_slice(&[b'x'; 57]);
    assert_eq!(
        small.run(&exact),
        accepted(&exact, "POST", "/", &[b'x'; 57])
    );
    assert_eq!(
        small.run(b"POST / HTTP/1.1\r\nContent-Length: 58\r\n\r\n"),
        b"-413\n"
    );
    let mut header_overflow = prefix.to_vec();
    header_overflow.resize(96, b'a');
    assert_eq!(small.run(&header_overflow), b"-413\n");
}

#[test]
fn pure_helpers_handle_short_malformed_slices_and_query_paths() {
    let fixture = Fixture::build(
        r#"use "http.sal".
operation Main:
    returns i64.
    body:
        let valid = bytes("GET /a?query HTTP/1.1\r\n\r\n").
        let mut count = usize(0).
        while count < 23:
            let part = slice(valid, usize(0), count).
            if len(HttpMethod(part)) != 0:
                return 1.
            if len(HttpPath(part)) != 0:
                return 2.
            if HttpBodyOffset(part) != -400:
                return 3.
            set count = count + 1.
        if HttpMethod(valid) != bytes("GET"):
            return 4.
        if HttpPath(valid) != bytes("/a"):
            return 5.
        if HttpBodyOffset(valid) != i64(len(valid)):
            return 6.
        if len(HttpMethod(bytes("GET / HTTP/9.9\r\n"))) != 0:
            return 7.
        if len(HttpPath(bytes("GET x HTTP/1.1\r\n"))) != 0:
            return 8.
        return 0.
"#,
    );
    assert_eq!(fixture.run(b""), b"");
}

fn response_probe(status: i64, body: &str, capacity: usize, expected: i64) -> Fixture {
    Fixture::build(&format!(
        r#"use "http.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = syscall(9, 0, 4096, 3, 34, -1, 0).
        if mapped < 0:
            return 90.
        let result = HttpWriteResponse(1, {status}, bytes("{body}"), usize(mapped), usize({capacity})).
        if result != {expected}:
            return 91.
        return 0.
"#
    ))
}

#[test]
fn responses_have_exact_status_json_headers_byte_lengths_and_bodies() {
    fn assert_response(output: &[u8], status: u16, expected_body: &str) -> usize {
        let response = std::str::from_utf8(output).expect("UTF-8 JSON response");
        let (header, body) = response
            .split_once("\r\n\r\n")
            .expect("HTTP header boundary");
        let mut lines = header.split("\r\n");
        let mut status_line = lines.next().expect("status line").split_ascii_whitespace();
        assert_eq!(status_line.next(), Some("HTTP/1.1"));
        assert_eq!(
            status_line
                .next()
                .expect("status code")
                .parse::<u16>()
                .unwrap(),
            status
        );
        let fields: Vec<_> = lines
            .map(|line| {
                let (name, value) = line.split_once(':').expect("HTTP header field");
                (name, value.trim())
            })
            .collect();
        let length = expected_body.len().to_string();
        for (name, expected) in [
            ("content-type", "application/json"),
            ("content-length", length.as_str()),
            ("connection", "close"),
        ] {
            let mut matching = fields
                .iter()
                .filter(|(field, _)| field.eq_ignore_ascii_case(name));
            assert_eq!(matching.next().map(|(_, value)| *value), Some(expected));
            assert!(matching.next().is_none(), "duplicate {name}");
        }
        assert_eq!(body, expected_body);
        header.len() + 4
    }

    let body = r#"{"message":"é"}"#;
    for status in [200, 400, 404, 405, 409, 413, 415, 431, 500, 503] {
        let fixture = response_probe(status, r#"{\"message\":\"é\"}"#, 256, 0);
        assert_response(&fixture.run(b""), status as u16, body);
    }
    let empty = response_probe(200, "", 256, 0);
    assert_response(&empty.run(b""), 200, "");
    let reference = response_probe(200, "{}", 256, 0);
    let header_size = assert_response(&reference.run(b""), 200, "{}");
    let exact = response_probe(200, "{}", header_size, 0);
    assert_response(&exact.run(b""), 200, "{}");
    let short = response_probe(200, "{}", header_size - 1, -28);
    assert_eq!(short.run(b""), b"", "no header prefix may escape preflight");
    let unsupported = response_probe(201, "{}", 256, -22);
    assert_eq!(unsupported.run(b""), b"");
}

#[test]
fn io_errors_propagate_without_http_remapping() {
    let fixture = Fixture::build(
        r#"use "http.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = syscall(9, 0, 4096, 3, 34, -1, 0).
        if mapped < 0:
            return 90.
        if HttpReadRequest(-1, usize(mapped), usize(4096)) != -9:
            return 1.
        if HttpWriteResponse(-1, 200, bytes("{}"), usize(mapped), usize(4096)) != -9:
            return 2.
        return 0.
"#,
    );
    assert_eq!(fixture.run(b""), b"");
}
