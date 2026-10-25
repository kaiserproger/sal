#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::io::{Read, Write};
use std::net::{Ipv4Addr, SocketAddr, TcpStream};
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::PathBuf;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Once;
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);
static SUBREAPER: Once = Once::new();
const DEADLINE: Duration = Duration::from_secs(10);
const RESPONSE_DEADLINE: Duration = Duration::from_secs(2);

extern "C" {
    fn kill(pid: i32, signal: i32) -> i32;
    fn prctl(option: i32, a: usize, b: usize, c: usize, d: usize) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn close_range(first: u32, last: u32, flags: i32) -> i32;
}

struct Fixture(PathBuf);

impl Fixture {
    fn build(source: &str) -> Self {
        let fixture = Self(std::env::temp_dir().join(format!(
            "sal-server-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        )));
        std::fs::create_dir_all(fixture.0.join("linux")).expect("fixture directory");
        let stdlib = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in [
            "server.sal",
            "http.sal",
            "bytes.sal",
            "linux/net.sal",
            "linux/io.sal",
            "linux/memory.sal",
            "linux/process.sal",
        ] {
            std::fs::copy(stdlib.join(name), fixture.0.join(name)).expect("copy real SAL library");
        }
        std::fs::write(fixture.0.join("probe.sal"), source).expect("write SAL probe");
        let output = Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(fixture.0.join("probe.sal"))
            .arg("--out")
            .arg(fixture.0.join("out"))
            .output()
            .expect("compile native SAL server");
        assert!(
            output.status.success(),
            "SAL compilation failed: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        fixture
    }

    fn spawn(&self, stdout: Stdio, stdin: Stdio) -> NativeChild {
        SUBREAPER.call_once(|| {
            // SAFETY: PR_SET_CHILD_SUBREAPER takes integers, not pointers. The
            // harness adopts orphaned workers; cleanup waits ONLY on its own
            // process group, never on another concurrently running test.
            assert_eq!(
                unsafe { prctl(36, 1, 0, 0, 0) },
                0,
                "enable owned-worker reaping"
            );
        });
        let mut command = Command::new(self.0.join("out/probe"));
        command
            .stdin(stdin)
            .stdout(stdout)
            .stderr(Stdio::null())
            .process_group(0);
        // Concurrent Command launches can temporarily own inheritable stdio
        // duplicates. The fixture owns only 0..=2; retain the exec-error pipe
        // until exec while preventing unrelated descriptors reaching the probe.
        // SAFETY: close_range is async-signal-safe and CLOEXEC changes only
        // this fork child's descriptor table; no Rust allocation occurs here.
        unsafe {
            command.pre_exec(|| {
                if close_range(3, u32::MAX, 4) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        NativeChild(command.spawn().expect("start native SAL server"))
    }

    fn serve(&self) -> (NativeChild, UnixStream, SocketAddr) {
        // A socket rather than a blocking pipe gives readiness a real deadline.
        let (mut events, output) = UnixStream::pair().expect("readiness socketpair");
        events.set_read_timeout(Some(DEADLINE)).unwrap();
        let child = self.spawn(Stdio::from(OwnedFd::from(output)), Stdio::null());
        let mut port = [0; 2];
        events
            .read_exact(&mut port)
            .expect("bound port announcement");
        let port = u16::from_be_bytes(port);
        assert_ne!(port, 0);
        (child, events, SocketAddr::from((Ipv4Addr::LOCALHOST, port)))
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct NativeChild(Child);

impl NativeChild {
    fn assert_running(&mut self) {
        assert!(self.0.try_wait().unwrap().is_none(), "server exited early");
    }

    fn finish(&mut self) -> ExitStatus {
        let deadline = Instant::now() + DEADLINE;
        loop {
            if let Some(status) = self.0.try_wait().expect("poll native process") {
                return status;
            }
            assert!(Instant::now() < deadline, "native process deadline");
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    fn children(&self) -> Vec<i32> {
        children_of(self.0.id())
    }

    fn wait_for_syscall(&mut self, number: &str) {
        let deadline = Instant::now() + RESPONSE_DEADLINE;
        loop {
            self.assert_running();
            let state = std::fs::read_to_string(format!("/proc/{}/syscall", self.0.id()))
                .expect("observe owned process syscall");
            if state.split_whitespace().next() == Some(number) {
                return;
            }
            assert!(
                Instant::now() < deadline,
                "expected syscall {number}: {state}"
            );
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    fn wait_for_reaped_children(&mut self) {
        let deadline = Instant::now() + RESPONSE_DEADLINE;
        loop {
            self.assert_running();
            if self.children().is_empty() {
                return;
            }
            assert!(Instant::now() < deadline, "children were not reaped");
            std::thread::sleep(Duration::from_millis(1));
        }
    }
}

fn children_of(pid: u32) -> Vec<i32> {
    std::fs::read_to_string(format!("/proc/{pid}/task/{pid}/children"))
        .expect("read owned server's child list")
        .split_whitespace()
        .map(|pid| pid.parse().expect("numeric child pid"))
        .collect()
}

impl Drop for NativeChild {
    fn drop(&mut self) {
        // Stop the parent first so it cannot fork during cleanup. Subreaper
        // adoption lets us reap every worker ourselves rather than leave
        // zombies to pid 1. The Child handle protects against stale parent PIDs.
        let group = -(self.0.id() as i32);
        let _ = self.0.kill();
        let _ = self.0.wait();
        let deadline = Instant::now() + DEADLINE;
        loop {
            let mut status = 0;
            // SAFETY: status is writable and wait is restricted to our group.
            let result = unsafe { waitpid(group, &mut status, 1) };
            if result < 0 {
                let error = std::io::Error::last_os_error();
                if error.raw_os_error() == Some(4) {
                    continue;
                }
                assert_eq!(
                    error.raw_os_error(),
                    Some(10),
                    "reap owned workers: {error}"
                );
                return;
            }
            if result > 0 {
                continue;
            }
            // A live adopted child proves this group still belongs to us.
            // SAFETY: process_group(0) isolated this group from the runner.
            unsafe { kill(group, 9) };
            if Instant::now() >= deadline {
                assert!(std::thread::panicking(), "owned-worker cleanup deadline");
                return;
            }
            std::thread::sleep(Duration::from_millis(1));
        }
    }
}

fn connect(address: SocketAddr) -> TcpStream {
    let socket = TcpStream::connect_timeout(&address, RESPONSE_DEADLINE).expect("connect server");
    socket.set_write_timeout(Some(RESPONSE_DEADLINE)).unwrap();
    socket
}

fn dispatched(events: &mut UnixStream) {
    events.set_read_timeout(Some(RESPONSE_DEADLINE)).unwrap();
    let mut marker = [0];
    events.read_exact(&mut marker).expect("real dispatch entry");
    assert_eq!(marker, *b"D");
}

fn response(socket: &mut TcpStream, timeout: Duration) -> Vec<u8> {
    let deadline = Instant::now() + timeout;
    let mut result = Vec::new();
    loop {
        let remaining = deadline
            .checked_duration_since(Instant::now())
            .expect("response deadline");
        socket.set_read_timeout(Some(remaining)).unwrap();
        let mut bytes = [0; 1024];
        let count = socket.read(&mut bytes).expect("read native HTTP response");
        if count == 0 {
            return result;
        }
        result.extend_from_slice(&bytes[..count]);
        assert!(result.len() <= 16384, "unexpected unbounded response");
    }
}

fn assert_response(response: &[u8], status: &str, body: &[u8]) {
    assert!(
        response.starts_with(format!("HTTP/1.1 {status}\r\n").as_bytes()),
        "{response:?}"
    );
    let end = response
        .windows(4)
        .position(|part| part == b"\r\n\r\n")
        .expect("headers");
    assert_eq!(&response[end + 4..], body);
    let headers = std::str::from_utf8(&response[..end])
        .unwrap()
        .to_ascii_lowercase();
    assert!(headers
        .replace(' ', "")
        .contains("content-type:text/plain;charset=utf-8"));
    assert!(headers.contains(&format!("content-length: {}", body.len())));
}

fn fd_count(pid: u32) -> usize {
    std::fs::read_dir(format!("/proc/{pid}/fd"))
        .unwrap()
        .count()
}

fn map_count(pid: u32) -> usize {
    std::fs::read_to_string(format!("/proc/{pid}/maps"))
        .unwrap()
        .lines()
        .count()
}

// This is an actual application hook: parse a request and echo its path using
// the shared HTTP implementation. Events synchronize tests, not production
// readiness/logging. A high arena byte verifies parent-to-child COW isolation.
const DISPATCH: &str = r#"
operation ProbeTimeout:
    accepts client of type i64.
    accepts option of type i64.
    accepts scratch of type usize.
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        store8(scratch + 16, u8(16)).
        store8(scratch + 17, u8(0)).
        store8(scratch + 18, u8(0)).
        store8(scratch + 19, u8(0)).
        let result = syscall(55, client, 1, option, scratch, scratch + 16, 0).
        if result < 0:
            return result.
        if load8(scratch) != 5:
            return -22.
        let mut index = usize(1).
        while index < 16:
            if load8(scratch + index) != 0:
                return -22.
            set index = index + 1.
        return 0.
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type usize.
    accepts arena_size of type usize.
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        if arena_size != 65536:
            return 81.
        if load8(arena + 65535) != 73:
            return 82.
        store8(arena + 65535, u8(99)).
        if ProbeTimeout(client, 20, arena + 60000) != 0:
            return 83.
        if ProbeTimeout(client, 21, arena + 60000) != 0:
            return 84.
        LinuxWriteAll(1, bytes("D")).
        let length = HttpReadRequest(client, arena, usize(32768)).
        if length == -11:
            HttpWriteTextResponse(client, 408, bytes("timeout"), arena + 32768, usize(16384)).
            return 0.
        if length < 0:
            HttpWriteTextResponse(client, 400, bytes("bad request"), arena + 32768, usize(16384)).
            return 0.
        let path = HttpPath(bytes_at(arena, usize(length))).
        HttpWriteTextResponse(client, 200, path, arena + 32768, usize(16384)).
        return 0.
"#;

fn server_source(max_clients: usize, auto_reap: bool) -> String {
    format!(
        r#"use "server.sal".
use "http.sal".
{DISPATCH}
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = LinuxMapMemory(usize(65536)).
        if mapped < 0:
            return 90.
        let arena = usize(mapped).
        if {auto_reap}:
            # Exercise ECHILD with an explicitly inherited SIGCHLD=SIG_IGN.
            store8(arena, u8(1)).
            let policy = syscall(13, 17, arena, 0, 8, 0, 0).
            if policy < 0:
                LinuxUnmapMemory(arena, usize(65536)).
                return 93.
        LinuxIpv4Address(arena, 2130706433, 0).
        store8(arena + 16, u8(1)).
        let listener = LinuxTcpListen(arena, arena + 16, 16).
        if listener < 0:
            LinuxUnmapMemory(arena, usize(65536)).
            return 91.
        store8(arena + 20, u8(16)).
        let named = syscall(51, listener, arena, arena + 20, 0, 0, 0).
        if named < 0:
            LinuxClose(listener).
            LinuxUnmapMemory(arena, usize(65536)).
            return 92.
        store8(arena + 65535, u8(73)).
        LinuxWriteAll(1, bytes_at(arena + 2, usize(2))).
        return ServerServe(listener, arena, usize(65536), {max_clients}).
"#
    )
}

#[test]
fn incomplete_client_does_not_block_a_second_real_request() {
    let fixture = Fixture::build(&server_source(2, false));
    let (mut child, mut events, address) = fixture.serve();
    let mut first = connect(address);
    first.write_all(b"GET /first HTTP/1.1\r\nHost:").unwrap();
    dispatched(&mut events);
    let workers = child.children();
    assert_eq!(workers.len(), 1);
    // Listener was closed before dispatch; only stdio and the accepted socket
    // remain. The parent promptly closes its copy of that accepted socket.
    assert_eq!(fd_count(workers[0] as u32), 4);
    child.wait_for_syscall("43");
    assert_eq!(fd_count(child.0.id()), 4);

    let second_deadline = Instant::now() + RESPONSE_DEADLINE;
    let mut second = connect(address);
    second.write_all(b"GET /second HTTP/1.1\r\n\r\n").unwrap();
    dispatched(&mut events);
    let remaining = second_deadline
        .checked_duration_since(Instant::now())
        .expect("second request must progress within two seconds");
    assert_response(&response(&mut second, remaining), "200 OK", b"/second");
    // First request is still incomplete when the second has already finished.
    assert!(child.children().contains(&workers[0]));
    first.write_all(b" localhost\r\n\r\n").unwrap();
    assert_response(
        &response(&mut first, RESPONSE_DEADLINE),
        "200 OK",
        b"/first",
    );
    child.assert_running();
}

#[test]
fn child_limit_reaps_and_reuses_parent_resources_across_disconnects() {
    let fixture = Fixture::build(&server_source(1, false));
    let (mut child, mut events, address) = fixture.serve();
    child.wait_for_syscall("43");
    let original_fds = fd_count(child.0.id());
    let original_maps = map_count(child.0.id());
    let mut first = connect(address);
    first.write_all(b"GET /held HTTP/1.1\r\n").unwrap();
    dispatched(&mut events);
    child.wait_for_syscall("61");
    let workers = child.children();
    assert_eq!(workers.len(), 1);

    let mut second = connect(address);
    second.write_all(b"GET /queued HTTP/1.1\r\n\r\n").unwrap();
    second
        .set_read_timeout(Some(Duration::from_millis(150)))
        .unwrap();
    let error = second
        .read(&mut [0])
        .expect_err("second dispatch must wait for a slot");
    assert!(matches!(
        error.kind(),
        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
    ));
    assert_eq!(child.children(), workers);
    first.write_all(b"\r\n").unwrap();
    assert_response(&response(&mut first, RESPONSE_DEADLINE), "200 OK", b"/held");
    dispatched(&mut events);
    assert_response(
        &response(&mut second, RESPONSE_DEADLINE),
        "200 OK",
        b"/queued",
    );
    child.wait_for_reaped_children();

    // Disconnect mid-request. The callback may observe EOF or EPIPE writing its
    // error response, but the parent must survive and recycle the single slot.
    let mut disconnected = connect(address);
    disconnected.write_all(b"GET /gone HTTP/1.1\r\n").unwrap();
    dispatched(&mut events);
    drop(disconnected);
    child.wait_for_reaped_children();
    for index in 0..24 {
        let path = format!("/again/{index}");
        let mut socket = connect(address);
        socket
            .write_all(format!("GET {path} HTTP/1.1\r\n\r\n").as_bytes())
            .unwrap();
        dispatched(&mut events);
        assert_response(
            &response(&mut socket, RESPONSE_DEADLINE),
            "200 OK",
            path.as_bytes(),
        );
        child.wait_for_reaped_children();
    }
    child.wait_for_syscall("43");
    assert_eq!(
        fd_count(child.0.id()),
        original_fds,
        "parent descriptor leak"
    );
    assert_eq!(
        map_count(child.0.id()),
        original_maps,
        "parent mapping leak"
    );
}

#[test]
fn accepted_socket_timeout_returns_408_and_releases_the_slot() {
    let fixture = Fixture::build(&server_source(1, false));
    let (mut child, mut events, address) = fixture.serve();
    let mut stalled = connect(address);
    stalled.write_all(b"GET /stalled HTTP/1.1\r\n").unwrap();
    dispatched(&mut events);
    assert_response(
        &response(&mut stalled, Duration::from_secs(8)),
        "408 Request Timeout",
        b"timeout",
    );
    child.wait_for_reaped_children();
    let mut next = connect(address);
    next.write_all(b"GET /after-timeout HTTP/1.1\r\n\r\n")
        .unwrap();
    dispatched(&mut events);
    assert_response(
        &response(&mut next, RESPONSE_DEADLINE),
        "200 OK",
        b"/after-timeout",
    );
    child.wait_for_reaped_children();
}

#[test]
fn sigpipe_policy_is_explicit_and_returns_epipe_on_a_closed_peer() {
    let fixture = Fixture::build(
        r#"use "linux/process.sal".
use "linux/memory.sal".
use "linux/io.sal".
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = LinuxMapMemory(usize(4096)).
        if mapped < 0:
            return 90.
        let arena = usize(mapped).
        # Reset to SIG_DFL: the test must not depend on the Rust runner's policy.
        if syscall(13, 13, arena, 0, 8, 0, 0) < 0:
            return 91.
        if LinuxReadExact(0, arena + 64, usize(1)) != 1:
            return 92.
        if load8(arena + 64) == 105:
            if LinuxIgnoreBrokenPipe() < 0:
                return 93.
        let result = LinuxWriteAll(1, bytes("closed peer")).
        LinuxUnmapMemory(arena, usize(4096)).
        if result != -32:
            return 94.
        return 0.
"#,
    );
    for (mode, signal) in [(b'd', Some(13)), (b'i', None)] {
        let (peer, output) = UnixStream::pair().unwrap();
        drop(peer);
        let mut child = fixture.spawn(Stdio::from(OwnedFd::from(output)), Stdio::piped());
        child.0.stdin.take().unwrap().write_all(&[mode]).unwrap();
        let status = child.finish();
        assert_eq!(status.signal(), signal, "mode={mode}, status={status}");
        if signal.is_none() {
            assert!(
                status.success(),
                "explicit ignore must expose -32, not SIGPIPE"
            );
        }
    }
}

#[test]
fn validation_retains_ownership_and_runtime_errors_close_and_unmap() {
    let fixture = Fixture::build(
        r#"use "server.sal".
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type usize.
    accepts arena_size of type usize.
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        return LinuxWriteAll(client, bytes("unreachable for a non-listening socket")).
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        if ServerRun(2130706433, 0, usize(4095), 1) != -22:
            return 1.
        if ServerRun(2130706433, 0, usize(4096), 0) != -22:
            return 2.
        if ServerRun(2130706433, 65536, usize(4096), 1) != -22:
            return 3.
        let mapped = LinuxMapMemory(usize(4096)).
        if mapped < 0:
            return 4.
        let arena = usize(mapped).
        let scratch_map = LinuxMapMemory(usize(4096)).
        if scratch_map < 0:
            return 5.
        let scratch = usize(scratch_map).
        let socket = syscall(41, 2, 1, 0, 0, 0, 0).
        if socket < 0:
            return 6.
        if ServerServe(socket, arena, usize(4095), 1) != -22:
            return 7.
        if ServerServe(socket, arena, usize(4096), 0) != -22:
            return 8.
        if ServerServe(-1, arena, usize(4096), 1) != -22:
            return 9.
        if ServerServe(socket, usize(0), usize(4096), 1) != -22:
            return 10.
        # Invalid arguments did not consume either caller-owned resource.
        if syscall(72, socket, 1, 0, 0, 0, 0) < 0:
            return 11.
        if syscall(27, arena, 4096, scratch, 0, 0, 0) != 0:
            return 12.
        # A valid but non-listening socket fails accept with EINVAL after the
        # ownership transfer. fcntl/mincore observe both actual releases.
        if ServerServe(socket, arena, usize(4096), 1) != -22:
            return 13.
        if syscall(72, socket, 1, 0, 0, 0, 0) != -9:
            return 14.
        if syscall(27, arena, 4096, scratch, 0, 0, 0) != -12:
            return 15.
        LinuxUnmapMemory(scratch, usize(4096)).
        return 0.
"#,
    );
    let mut child = fixture.spawn(Stdio::null(), Stdio::null());
    assert!(
        child.finish().success(),
        "SAL ownership/cleanup checks failed"
    );
}

#[test]
fn setup_signal_socket_option_and_fork_failures_release_owned_resources() {
    // A real kernel seccomp filter makes otherwise nondeterministic resource
    // failures reproducible without replacing any SAL lifecycle operation.
    for (syscall_number, errno) in [(13, 1), (54, 1), (57, 11)] {
        let fixture = Fixture::build(&format!(
            r#"use "server.sal".
operation ProbeWord:
    accepts target of type usize.
    accepts value of type usize.
    effects: UnsafeMemory.
    body:
        let mut remaining = value.
        let mut offset = usize(0).
        while offset < 8:
            store8(target + offset, u8(remaining % 256)).
            set remaining = remaining / 256.
            set offset = offset + 1.
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type usize.
    accepts arena_size of type usize.
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        return LinuxWriteAll(client, bytes("unexpected dispatch after injected failure")).
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = LinuxMapMemory(usize(4096)).
        if mapped < 0:
            return 80.
        let arena = usize(mapped).
        let scratch_map = LinuxMapMemory(usize(4096)).
        if scratch_map < 0:
            return 81.
        let scratch = usize(scratch_map).
        LinuxIpv4Address(arena, 2130706433, 0).
        store8(arena + 16, u8(1)).
        let listener = LinuxTcpListen(arena, arena + 16, 4).
        if listener < 0:
            return 82.
        store8(arena + 20, u8(16)).
        if syscall(51, listener, arena, arena + 20, 0, 0, 0) < 0:
            return 83.
        # Four classic BPF instructions: load nr, match nr, errno, allow.
        # The anonymous mapping provides zeroes for untouched instruction bytes.
        store8(scratch, u8(32)).
        store8(scratch + 8, u8(21)).
        store8(scratch + 11, u8(1)).
        store8(scratch + 12, u8({syscall_number})).
        store8(scratch + 16, u8(6)).
        store8(scratch + 20, u8({errno})).
        store8(scratch + 22, u8(5)).
        store8(scratch + 24, u8(6)).
        store8(scratch + 30, u8(255)).
        store8(scratch + 31, u8(127)).
        # sock_fprog: u16 length, six padding bytes, eight-byte filter pointer.
        store8(scratch + 32, u8(4)).
        ProbeWord(scratch + 40, scratch).
        if syscall(157, 38, 1, 0, 0, 0, 0) < 0:
            return 84.
        if syscall(317, 1, 0, scratch + 32, 0, 0, 0) < 0:
            return 85.
        LinuxWriteAll(1, bytes_at(arena + 2, usize(2))).
        if ServerServe(listener, arena, usize(4096), 1) != -{errno}:
            return 86.
        if syscall(72, listener, 1, 0, 0, 0, 0) != -9:
            return 87.
        # No accepted descriptor remains after setsockopt/fork failure either.
        if syscall(72, listener + 1, 1, 0, 0, 0, 0) != -9:
            return 88.
        if syscall(27, arena, 4096, scratch, 0, 0, 0) != -12:
            return 89.
        LinuxUnmapMemory(scratch, usize(4096)).
        return 0.
"#
        ));
        let (mut child, _events, address) = fixture.serve();
        let _connection = (syscall_number != 13).then(|| connect(address));
        let status = child.finish();
        assert!(
            status.success(),
            "syscall={syscall_number}, status={status}"
        );
    }
}

#[test]
fn server_run_bind_and_address_errors_do_not_accumulate_mappings_or_fds() {
    let fixture = Fixture::build(
        r#"use "server.sal".
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type usize.
    accepts arena_size of type usize.
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        return LinuxWriteAll(client, bytes("unexpected dispatch on occupied port")).
operation Main:
    returns i64.
    effects: SystemCall, UnsafeMemory.
    body:
        let mapped = LinuxMapMemory(usize(4096)).
        if mapped < 0:
            return 80.
        let arena = usize(mapped).
        LinuxIpv4Address(arena, 2130706433, 0).
        store8(arena + 16, u8(1)).
        let listener = LinuxTcpListen(arena, arena + 16, 4).
        if listener < 0:
            return 81.
        store8(arena + 20, u8(16)).
        if syscall(51, listener, arena, arena + 20, 0, 0, 0) < 0:
            return 82.
        let port = i64(load8(arena + 2)) * 256 + i64(load8(arena + 3)).
        LinuxWriteAll(1, bytes("B")).
        if LinuxReadExact(0, arena + 64, usize(1)) != 1:
            return 83.
        let mut iteration = 0.
        while iteration < 32:
            if ServerRun(2130706433, port, usize(4096), 1) != -98:
                return 84.
            if ServerRun(2130706433, 65536, usize(4096), 1) != -22:
                return 85.
            set iteration = iteration + 1.
        LinuxWriteAll(1, bytes("A")).
        if LinuxReadExact(0, arena + 64, usize(1)) != 1:
            return 86.
        LinuxClose(listener).
        LinuxUnmapMemory(arena, usize(4096)).
        return 0.
"#,
    );
    let (mut events, output) = UnixStream::pair().unwrap();
    events.set_read_timeout(Some(DEADLINE)).unwrap();
    let mut child = fixture.spawn(Stdio::from(OwnedFd::from(output)), Stdio::piped());
    let mut marker = [0];
    events.read_exact(&mut marker).unwrap();
    assert_eq!(marker, *b"B");
    let fds = fd_count(child.0.id());
    let maps = std::fs::read_to_string(format!("/proc/{}/maps", child.0.id())).unwrap();
    child.0.stdin.as_mut().unwrap().write_all(b"g").unwrap();
    events.read_exact(&mut marker).unwrap();
    assert_eq!(marker, *b"A");
    assert_eq!(fd_count(child.0.id()), fds);
    assert_eq!(
        std::fs::read_to_string(format!("/proc/{}/maps", child.0.id())).unwrap(),
        maps
    );
    child.0.stdin.take().unwrap().write_all(b"x").unwrap();
    assert!(child.finish().success());
}

#[test]
fn inherited_auto_reaping_does_not_underflow_or_stall_the_child_limit() {
    let fixture = Fixture::build(&server_source(1, true));
    let (mut child, mut events, address) = fixture.serve();
    for _ in 0..8 {
        let mut socket = connect(address);
        socket.write_all(b"GET /auto-reap HTTP/1.1\r\n").unwrap();
        dispatched(&mut events);
        // Hold the child until the parent is in a real blocking wait. When
        // SIGCHLD is ignored Linux returns ECHILD after this child exits.
        child.wait_for_syscall("61");
        assert_eq!(child.children().len(), 1);
        socket.write_all(b"\r\n").unwrap();
        assert_response(
            &response(&mut socket, RESPONSE_DEADLINE),
            "200 OK",
            b"/auto-reap",
        );
        child.wait_for_reaped_children();
    }
    child.wait_for_syscall("43");
}
