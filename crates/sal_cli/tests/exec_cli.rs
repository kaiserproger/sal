//! Integration test: `sal build-exe examples/native/hello.sal` compiles to a
//! runnable binary printing exactly `Hello, world!` with exit 0.
//!
//! Drives the built `sal` binary via `CARGO_BIN_EXE_sal`; std only. The output
//! directory is a pid-unique subdir of `std::env::temp_dir()` (created with
//! `create_dir_all`, no external crates).

use std::path::PathBuf;
use std::process::{Command, Output};

fn sal_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_sal"))
}

fn root_path(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../")
        .join(rel)
}

fn unique_out_dir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "sal-hello-exec-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    std::fs::create_dir_all(&dir).expect("failed to create temp out dir");
    dir
}

fn run(cmd: &mut Command) -> Output {
    cmd.output().expect("failed to spawn child process")
}

#[test]
fn hello_builds_and_prints() {
    let sal = root_path("examples/native/hello.sal");
    assert!(sal.is_file(), "missing fixture: {}", sal.display());
    let out_dir = unique_out_dir();

    let build: Output = run(Command::new(sal_bin())
        .arg("build-exe")
        .arg(&sal)
        .arg("--out")
        .arg(&out_dir));
    assert!(
        build.status.success(),
        "build-exe failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );

    let bin: PathBuf = out_dir.join("hello");
    assert!(bin.is_file(), "missing binary: {}", bin.display());

    let executed: Output = run(&mut Command::new(&bin));
    assert!(
        executed.status.success(),
        "hello binary failed: status={} stdout={} stderr={}",
        executed.status,
        String::from_utf8_lossy(&executed.stdout),
        String::from_utf8_lossy(&executed.stderr)
    );
    assert_eq!(executed.stdout, b"Hello, world!\n");
    assert!(
        executed.stderr.is_empty(),
        "unexpected stderr: {}",
        String::from_utf8_lossy(&executed.stderr)
    );
}

fn raw_request(port: u16, version: &str) -> String {
    use std::io::{BufRead, BufReader, Write};
    let mut stream = std::net::TcpStream::connect(("127.0.0.1", port))
        .expect("failed to connect to test server");
    stream
        .set_read_timeout(Some(std::time::Duration::from_secs(3)))
        .expect("failed to set timeout");
    let request = format!("GET /say/hi {version}\r\nHost: x\r\n\r\n");
    stream
        .write_all(request.as_bytes())
        .expect("failed to send request");
    let mut status = String::new();
    BufReader::new(stream)
        .read_line(&mut status)
        .expect("read response status");
    status.trim_end().to_owned()
}

#[test]
fn server_rejects_non_http1_versions() {
    // Reserve an ephemeral port rather than accidentally probing a stale process.
    let reservation = std::net::TcpListener::bind(("127.0.0.1", 0)).expect("reserve port");
    let port = reservation.local_addr().unwrap().port();
    let out_dir = unique_out_dir();
    let tupoi = out_dir.join("tupoi.sal");
    std::fs::write(
        &tupoi,
        include_str!("../../../examples/native/tupoi.sal").replace("8081", &port.to_string()),
    )
    .expect("write server fixture");
    let build = run(Command::new(sal_bin())
        .arg("build-exe")
        .arg(&tupoi)
        .arg("--backend")
        .arg("rust-std")
        .arg("--out")
        .arg(&out_dir));
    assert!(build.status.success(), "build-exe failed: {build:?}");
    drop(reservation);
    struct Server(std::process::Child);
    impl Drop for Server {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut server = Server(
        Command::new(out_dir.join("tupoi"))
            .spawn()
            .expect("start server"),
    );
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(3);
    loop {
        assert!(
            server.0.try_wait().expect("child status").is_none(),
            "server exited before readiness"
        );
        if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
            break;
        }
        assert!(
            std::time::Instant::now() < deadline,
            "server readiness timeout"
        );
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    for version in ["HTTP/1.0", "HTTP/1.1"] {
        assert_eq!(raw_request(port, version), "HTTP/1.0 200 OK");
    }
    for version in ["HTTP/2", "HTTP/2.0", "GARBAGE", "HTTP/3"] {
        assert_eq!(raw_request(port, version), "HTTP/1.0 400 Bad Request");
    }
}

fn build_sal_source(name: &str, source: &str) -> (PathBuf, PathBuf) {
    let dir = unique_out_dir();
    let sal = dir.join(format!("{name}.sal"));
    std::fs::write(&sal, source).expect("failed to write sal fixture");
    (dir, sal)
}

fn build_and_run(dir: &PathBuf, sal: &PathBuf) -> Output {
    let build = run(Command::new(sal_bin())
        .arg("build-exe")
        .arg(sal)
        .arg("--out")
        .arg(dir));
    assert!(
        build.status.success(),
        "build-exe failed: {} {}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let bin = dir.join(
        sal.file_stem()
            .expect("sal fixture has no stem")
            .to_string_lossy()
            .into_owned(),
    );
    assert!(bin.is_file(), "missing binary: {}", bin.display());
    run(&mut std::process::Command::new(&bin))
}

#[test]
fn literal_with_braces_prints_verbatim() {
    let (dir, sal) = build_sal_source(
        "braces",
        "operation Braces:\n  returns Text.\n  responds with \"{}\".\n",
    );
    let executed = build_and_run(&dir, &sal);
    assert!(
        executed.status.success(),
        "braces binary failed: {executed:?}"
    );
    assert_eq!(executed.stdout, b"{}\n");
}

#[test]
fn json_literal_in_multistatement_body_prints_verbatim() {
    let (dir, sal) = build_sal_source(
        "jsonbody",
        "operation JsonBody:\n  returns Text.\n  body:\n    let kind = \"item\".\n    return \"{\\\"code\\\": 7}\".\n",
    );
    let executed = build_and_run(&dir, &sal);
    assert!(
        executed.status.success(),
        "json body binary failed: {executed:?}"
    );
    assert_eq!(executed.stdout, b"{\"code\": 7}\n");
}
