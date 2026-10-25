//! End-to-end server sugar: actual CLI, embedded SAL stdlib, native ELF and TCP.
//! Every spawned process has a deadline and an owned process group; no host server
//! or copied stdlib stands in for the executable under test.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::fs::File;
use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpListener, TcpStream};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Once;
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
static SUBREAPER: Once = Once::new();
const PROCESS_DEADLINE: Duration = Duration::from_secs(60);
const NETWORK_DEADLINE: Duration = Duration::from_secs(10);

extern "C" {
    fn kill(pid: i32, signal: i32) -> i32;
    fn prctl(option: i32, a: usize, b: usize, c: usize, d: usize) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
}

struct OwnedProcess(Child);

impl OwnedProcess {
    fn spawn(command: &mut Command) -> Self {
        SUBREAPER.call_once(|| {
            // SAFETY: PR_SET_CHILD_SUBREAPER accepts only integer arguments.
            // Workers are reaped by their owned group, never with waitpid(-1).
            assert_eq!(unsafe { prctl(36, 1, 0, 0, 0) }, 0);
        });
        Self(
            command
                .process_group(0)
                .spawn()
                .expect("spawn owned process"),
        )
    }

    fn finish(&mut self) -> ExitStatus {
        let deadline = Instant::now() + PROCESS_DEADLINE;
        loop {
            if let Some(status) = self.0.try_wait().expect("poll owned process") {
                return status;
            }
            assert!(Instant::now() < deadline, "owned process deadline");
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    fn assert_running(&mut self) {
        assert!(
            self.0.try_wait().expect("poll server").is_none(),
            "native server exited before completing its requests"
        );
    }
}

impl Drop for OwnedProcess {
    fn drop(&mut self) {
        let group = -(self.0.id() as i32);
        // Stop the parent before reaping or killing workers, preventing forks
        // during cleanup. The live Child handle protects against reused PIDs.
        let _ = self.0.kill();
        let _ = self.0.wait();
        let deadline = Instant::now() + NETWORK_DEADLINE;
        loop {
            let mut status = 0;
            // SAFETY: writable status and only our isolated process group.
            let result = unsafe { waitpid(group, &mut status, 1) };
            if result < 0 {
                let error = std::io::Error::last_os_error();
                if error.raw_os_error() == Some(4) {
                    continue;
                }
                if !std::thread::panicking() {
                    assert_eq!(error.raw_os_error(), Some(10), "reap workers: {error}");
                }
                return;
            }
            if result > 0 {
                continue;
            }
            // A live child proves that this process group still belongs to us.
            // SAFETY: process_group(0) isolates it from other tests and the runner.
            unsafe { kill(group, 9) };
            if Instant::now() >= deadline {
                assert!(std::thread::panicking(), "owned worker cleanup deadline");
                return;
            }
            std::thread::sleep(Duration::from_millis(1));
        }
    }
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let fixture = Self(std::env::temp_dir().join(format!(
            "sal-frontend-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )));
        std::fs::create_dir_all(&fixture.0).expect("create fixture");
        fixture
    }

    fn run(&self, command: &mut Command) -> Output {
        let stdout_path = self.0.join("stdout.log");
        let stderr_path = self.0.join("stderr.log");
        let mut child = OwnedProcess::spawn(
            command
                .stdin(Stdio::null())
                .stdout(File::create(&stdout_path).expect("create stdout log"))
                .stderr(File::create(&stderr_path).expect("create stderr log")),
        );
        let status = child.finish();
        drop(child);
        Output {
            status,
            stdout: std::fs::read(stdout_path).expect("read stdout log"),
            stderr: std::fs::read(stderr_path).expect("read stderr log"),
        }
    }

    fn build(&self, source: &str, anglish: bool) -> Output {
        let name = if anglish { "probe.ang" } else { "probe.sal" };
        let input = self.0.join(name);
        std::fs::write(&input, source).expect("write frontend source");
        let mut command = Command::new(env!("CARGO_BIN_EXE_sal"));
        command.arg("build-exe");
        if anglish {
            command.arg("--ang");
        }
        // No backend override: exercise the default standalone native backend.
        self.run(command.arg(input).arg("--out").arg(self.0.join("out")))
    }

    fn executable(&self) -> PathBuf {
        self.0.join("out/probe")
    }

    fn assert_standalone(&self) {
        let headers = self.run(Command::new("readelf").arg("-lW").arg(self.executable()));
        success(&headers);
        assert!(!String::from_utf8_lossy(&headers.stdout).contains("INTERP"));
        let dynamic = self.run(Command::new("readelf").arg("-dW").arg(self.executable()));
        success(&dynamic);
        assert!(!String::from_utf8_lossy(&dynamic.stdout).contains("NEEDED"));
    }

    fn serve(&self, reservation: TcpListener) -> (OwnedProcess, SocketAddr) {
        let address = reservation.local_addr().expect("reserved address");
        drop(reservation);
        let mut server = OwnedProcess::spawn(
            Command::new(self.executable())
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(Stdio::null()),
        );
        let deadline = Instant::now() + NETWORK_DEADLINE;
        loop {
            server.assert_running();
            match TcpStream::connect_timeout(&address, Duration::from_millis(100)) {
                Ok(stream) => {
                    drop(stream);
                    server.assert_running();
                    return (server, address);
                }
                Err(error) => {
                    assert!(
                        matches!(
                            error.kind(),
                            std::io::ErrorKind::ConnectionRefused | std::io::ErrorKind::TimedOut
                        ),
                        "connect readiness: {error}"
                    );
                }
            }
            assert!(Instant::now() < deadline, "server readiness deadline");
            std::thread::sleep(Duration::from_millis(5));
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn success(output: &Output) {
    assert!(
        output.status.success(),
        "status={} stdout={} stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn reservation() -> TcpListener {
    TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).expect("reserve ephemeral loopback port")
}

fn server_source(port: u16) -> String {
    format!("server Frontend:\n    listens on port {port}.\n    speaks HTTP/1.\n")
}

fn connect(address: SocketAddr) -> TcpStream {
    let stream =
        TcpStream::connect_timeout(&address, NETWORK_DEADLINE).expect("connect native server");
    stream.set_write_timeout(Some(NETWORK_DEADLINE)).unwrap();
    stream
}

fn response(mut stream: TcpStream) -> Vec<u8> {
    let deadline = Instant::now() + NETWORK_DEADLINE;
    let mut response = Vec::new();
    loop {
        let remaining = deadline
            .checked_duration_since(Instant::now())
            .expect("HTTP response deadline");
        stream.set_read_timeout(Some(remaining)).unwrap();
        let mut buffer = [0; 4096];
        let count = stream.read(&mut buffer).expect("read native response");
        if count == 0 {
            return response;
        }
        response.extend_from_slice(&buffer[..count]);
        assert!(response.len() <= 262144, "bounded HTTP response");
    }
}

fn request(address: SocketAddr, wire: &[u8]) -> Vec<u8> {
    let mut stream = connect(address);
    stream.write_all(wire).expect("write native request");
    response(stream)
}

fn get(address: SocketAddr, path: &str) -> Vec<u8> {
    request(
        address,
        format!("GET {path} HTTP/1.1\r\nHost: localhost\r\n\r\n").as_bytes(),
    )
}

fn assert_response(wire: &[u8], status: &str, body: &[u8]) {
    let split = wire
        .windows(4)
        .position(|part| part == b"\r\n\r\n")
        .expect("response header");
    let headers = std::str::from_utf8(&wire[..split]).expect("ASCII headers");
    assert!(
        headers.starts_with(&format!("HTTP/1.1 {status}\r\n")),
        "{headers}"
    );
    let lines: Vec<_> = headers.split("\r\n").collect();
    assert!(
        lines.contains(&"Content-Type: text/plain; charset=utf-8"),
        "{headers}"
    );
    assert!(lines.contains(&"Connection: close"), "{headers}");
    let lengths: Vec<_> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("Content-Length: "))
        .collect();
    assert_eq!(lengths, [body.len().to_string()]);
    assert_eq!(&wire[split + 4..], body);
}

#[test]
fn canonical_routes_execute_real_sal_libraries() {
    let fixture = Fixture::new();
    let reservation = reservation();
    let mut source = server_source(reservation.local_addr().unwrap().port());
    // Deliberately put Zebra first: lexicographic route names, not source order,
    // decide the winner. Repeated capture names must return the last segment.
    source.push_str(
        r#"
operation Kept:
    returns i64.
    body:
        return 7.
route Zebra:
    handles GET /order/:value.
    responds with "wrong".
route Alpha:
    handles GET /order/:value.
    responds with param value.
route Say:
    handles GET /say/:what.
    responds with param what.
route Repeat:
    handles GET /repeat/:what/:what.
    responds with param what.
route Literal:
    handles GET /literal.
    responds with "Привет \"SAL\"\\\n\t\u{0}".
route Empty:
    handles GET /empty.
    responds with Text.
route Root:
    handles GET /.
    responds with "root".
route Raw:
    handles GET /raw/%41.
    responds with "raw".
route Trailing:
    handles GET /trail/.
    responds with "trailing".
"#,
    );
    success(&fixture.build(&source, false));
    fixture.assert_standalone();
    let (mut server, address) = fixture.serve(reservation);
    for (path, body) in [
        (
            "/say/%D0%9F%D1%80%D0%B8%D0%B2%D0%B5%D1%82?ignored=bad%",
            "Привет".as_bytes(),
        ),
        ("/say/a+b%2Fc%00d", b"a+b/c\0d".as_slice()),
        ("/say/%f0%90%90%80", "\u{10400}".as_bytes()),
        ("/repeat/first/last%21", b"last!".as_slice()),
        ("/order/chosen", b"chosen".as_slice()),
        ("/literal", "Привет \"SAL\"\\\n\t\0".as_bytes()),
        ("/empty", b"".as_slice()),
        ("/?ignored=yes", b"root".as_slice()),
        ("/raw/%41", b"raw".as_slice()),
        ("/trail/", b"trailing".as_slice()),
    ] {
        assert_response(&get(address, path), "200 OK", body);
    }
    for path in [
        "/unknown", "/say/", "/say/a/b", "/say/a/", "/raw/A", "/trail",
    ] {
        assert_response(&get(address, path), "404 Not Found", b"");
    }
    for path in [
        "/say/%",
        "/say/%0",
        "/say/%GG",
        "/say/%80",
        "/say/%C0%AF",
        "/say/%ED%A0%80",
        "/say/%F4%90%80%80",
        "/say/%E2%82",
        "/say/rawUTF8é",
    ] {
        assert_response(&get(address, path), "400 Bad Request", b"");
    }
    for method in ["POST", "PATCH", "UNKNOWN"] {
        assert_response(
            &request(
                address,
                format!("{method} /literal HTTP/1.1\r\nContent-Length: 0\r\n\r\n").as_bytes(),
            ),
            "404 Not Found",
            b"",
        );
    }
    assert_response(
        &request(
            address,
            b"GET /literal HTTP/1.1\r\nContent-Length: 0\r\nContent-Length: 0\r\n\r\n",
        ),
        "400 Bad Request",
        b"",
    );
    assert_response(
        &request(
            address,
            b"POST /literal HTTP/1.1\r\nContent-Length: 262144\r\n\r\n",
        ),
        "413 Payload Too Large",
        b"",
    );
    let mut oversized_header = b"GET /literal HTTP/1.1\r\nX-Fill: ".to_vec();
    oversized_header.resize(16384, b'a');
    assert_response(
        &request(address, &oversized_header),
        "431 Request Header Fields Too Large",
        b"",
    );
    // A real accepted socket times out in the real SAL server (five seconds).
    assert_response(&response(connect(address)), "408 Request Timeout", b"");
    server.assert_running();
}

#[test]
fn anglish_tupoi_builds_and_serves_without_a_foreign_runtime() {
    let fixture = Fixture::new();
    let reservation = reservation();
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/ang/tupoi.ang");
    let source = std::fs::read_to_string(example).expect("read real Tupoi example");
    let source = source.replace(
        "8081",
        &reservation.local_addr().unwrap().port().to_string(),
    );
    success(&fixture.build(&source, true));
    fixture.assert_standalone();
    let (mut server, address) = fixture.serve(reservation);
    assert_response(
        &get(address, "/say/%D0%AF+%2F%00?query=not-body"),
        "200 OK",
        "Я+/\0".as_bytes(),
    );
    assert_response(&get(address, "/say/%C0%80"), "400 Bad Request", b"");
    assert_response(&get(address, "/absent"), "404 Not Found", b"");
    server.assert_running();
}

#[test]
fn caller_entry_points_are_rejected_instead_of_replaced() {
    let fixture = Fixture::new();
    for name in ["Main", "ServerDispatch"] {
        let source = format!(
            "{}route Hello:\n    handles GET /.\n    responds with Text.\noperation {name}:\n    returns i64.\n    body:\n        return 23.\n",
            server_source(8081)
        );
        let output = fixture.build(&source, false);
        assert!(
            !output.status.success(),
            "caller {name} was silently replaced"
        );
        let diagnostics = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            diagnostics.contains("X109") && diagnostics.contains(name),
            "{diagnostics}"
        );
    }
}

#[test]
fn original_imported_operations_are_still_checked() {
    let fixture = Fixture::new();
    std::fs::write(
        fixture.0.join("caller.sal"),
        "operation CallerDefinition:\n    returns i64.\n    body:\n        return MissingCallerDependency().\n",
    ).expect("write imported caller definition");
    let source = format!(
        "use \"caller.sal\".\n{}route Hello:\n    handles GET /.\n    responds with Text.\n",
        server_source(8081)
    );
    let output = fixture.build(&source, false);
    assert!(
        !output.status.success(),
        "original caller definitions were discarded"
    );
    let diagnostics = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        diagnostics.contains("MissingCallerDependency"),
        "{diagnostics}"
    );
}

#[test]
fn lowering_does_not_hide_duplicate_or_cross_kind_names() {
    let fixture = Fixture::new();
    for conflicting in [
        "route Hello:\n    handles GET /other.\n    responds with Text.\n",
        "operation Hello:\n    returns i64.\n    body:\n        return 1.\n",
    ] {
        let source = format!(
            "{}route Hello:\n    handles GET /.\n    responds with Text.\n{conflicting}",
            server_source(8081)
        );
        let output = fixture.build(&source, false);
        assert!(
            !output.status.success(),
            "lowering hid an original declaration"
        );
        let diagnostics = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(diagnostics.contains("E1001"), "{diagnostics}");
    }
}
