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
            "net.sal",
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
entity ProbeOptionLength:
    layout "C".
    has value of type u64.
operation ProbeTimeout:
    accepts client of type i64.
    accepts option of type i64.
    returns i64.
    effects: SystemCall.
    body:
        # Kernel output lives in fixed C-layout cells, not raw app byte loops.
        let timeout = LinuxTimeval(i64(0), i64(0)).
        let length = ProbeOptionLength(u64(16)).
        let mut result = 0.
        unsafe:
            set result = syscall(55, client, 1, option, address(timeout), address(length), 0).
        if result < 0:
            return result.
        if timeout.seconds != 5 || timeout.microseconds != 0 || length.value != 16:
            return 1.
        return 0.
operation ProbeHttpStatus:
    accepts length of type i64.
    returns i64.
    requires:
        length != -11 otherwise 408.
        length != -22 && length != -400 && length != -413 && length != -431 otherwise 0 - length.
    body:
        return 400.
operation ProbeHttpErrorBody:
    accepts status of type i64.
    returns Bytes.
    requires:
        status != 408 otherwise bytes("timeout").
    body:
        return bytes("bad request").
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type MutBytes.
    returns i64.
    requires:
        len(arena) == 65536 otherwise 81.
    effects: SystemCall.
    body:
        let head = view(arena).
        let foot = slice(head, usize(65535), usize(1)).
        let sentinel = byte(foot, usize(0)).
        borrow_end(foot).
        borrow_end(head).
        if sentinel != 73:
            return 82.
        put(arena, usize(65535), u8(99)).
        let probeStatus = ProbeTimeout(client, 20).
        if probeStatus != 0:
            return 83.
        let probeStatus2 = ProbeTimeout(client, 21).
        if probeStatus2 != 0:
            return 84.
        LinuxWriteAll(1, bytes("D")).
        let reqWindow = slice_mut(arena, usize(0), usize(32768)).
        let length = HttpReadRequest(client, reqWindow).
        borrow_end(reqWindow).
        if length < 0:
            let badScratch = slice_mut(arena, usize(32768), usize(16384)).
            let status = ProbeHttpStatus(length).
            let badBody = ProbeHttpErrorBody(status).
            let badStatus = HttpWriteTextResponse(client, status, badBody, badScratch).
            borrow_end(badScratch).
            if badStatus < 0:
                return badStatus.
            return 0.
        let requestLoan = slice_mut(arena, usize(0), usize(length)).
        let request = view(requestLoan).
        let path = HttpPath(request).
        let echoScratch = slice_mut(arena, usize(32768), usize(16384)).
        let echoStatus = HttpWriteTextResponse(client, 200, path, echoScratch).
        borrow_end(echoScratch).
        borrow_end(path).
        borrow_end(request).
        borrow_end(requestLoan).
        if echoStatus < 0:
            return echoStatus.
        return 0.
"#;

fn server_source(max_clients: usize, auto_reap: bool) -> String {
    format!(
        r#"use "server.sal".
use "http.sal".
use "linux/io.sal".
use "linux/net.sal".
use "linux/process.sal".
{DISPATCH}
operation ProbeServe:
    accepts pending of type MutBytes.
    returns i64.
    requires:
        len(pending) == usize(65536) otherwise -91.
    effects: SystemCall.
    body:
        let proxy = slice_mut(pending, usize(0), usize(16)).
        let formatted = LinuxIpv4Address(proxy, 2130706433, 0).
        borrow_end(proxy).
        if formatted < 0:
            return -91.
        let head = view(pending).
        let endpointView = slice(head, usize(0), usize(16)).
        let listener = LinuxTcpListen(endpointView, i64(4)).
        borrow_end(endpointView).
        borrow_end(head).
        if listener < 0:
            return listener.
        let mut failure = 0.
        if {auto_reap}:
            let handler = LinuxSignalAction(usize(1), u64(0), usize(0), u64(0)).
            let mut policy = 0.
            unsafe:
                set policy = syscall(13, 17, address(handler), 0, 8, 0, 0).
            if policy < 0:
                set failure = -93.
        let addrLoan = slice_mut(pending, usize(0), usize(16)).
        let addrBytes = view(addrLoan).
        let length = ProbeOptionLength(u64(16)).
        let mut named = 0.
        unsafe:
            set named = syscall(51, listener, address(addrBytes), address(length), 0, 0, 0).
        borrow_end(addrBytes).
        borrow_end(addrLoan).
        if named < 0:
            set failure = -92.
        put(pending, usize(65535), u8(73)).
        let portLoan = slice_mut(pending, usize(2), usize(2)).
        let portBytes = view(portLoan).
        LinuxWriteAll(1, portBytes).
        borrow_end(portBytes).
        borrow_end(portLoan).
        if failure != 0:
            LinuxClose(listener).
            return failure.
        return listener.
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let pending = buffer(usize(65536)).
        let setup = borrow_mut(pending, usize(0), usize(65536)).
        let listener = ProbeServe(setup).
        borrow_end(setup).
        let mut failure = 0.
        if listener >= 0:
            set failure = ServerServe(listener, pending, {max_clients}).
        else:
            set failure = 0 - listener.
            buffer_drop(pending).
        return failure.
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
        r#"use "linux/io.sal".
use "linux/process.sal".
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let store = buffer(usize(4096)).
        let mode = borrow_mut(store, usize(64), usize(1)).
        # 'd' restores SIG_DFL; 'i' checks the explicit EPIPE policy.
        if LinuxReadExact(0, mode) != 1:
            set failure = 92.
        let modeView = view(mode).
        let modeByte = byte(modeView, usize(0)).
        borrow_end(modeView).
        borrow_end(mode).
        if modeByte == 105:
            if LinuxIgnoreBrokenPipe() < 0:
                set failure = 93.
        else:
            let action = LinuxSignalAction(usize(0), u64(0), usize(0), u64(0)).
            let mut reset = 0.
            unsafe:
                set reset = syscall(13, 13, address(action), 0, 8, 0, 0).
            if reset < 0:
                set failure = 93.
        if failure == 0:
            let result = LinuxWriteAll(1, bytes("closed peer")).
            if result != -32:
                set failure = 94.
        buffer_drop(store).
        return failure.
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
fn validation_consumes_arena_and_releases_listener_on_runtime_errors() {
    let fixture = Fixture::build(
        r#"use "server.sal".
use "linux/io.sal".
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type MutBytes.
    returns i64.
    effects: SystemCall.
    body:
        return LinuxWriteAll(client, bytes("unexpected dispatch")).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        if ServerRun(2130706433, 0, usize(4095), 1) != -22:
            set failure = 1.
        if ServerRun(2130706433, 0, usize(4096), 0) != -22:
            if failure == 0:
                set failure = 2.
        if ServerRun(2130706433, 65536, usize(4096), 1) != -22:
            if failure == 0:
                set failure = 3.
        if failure != 0:
            return failure.
        # Validation consumed the arena on every path: fresh Buffers work.
        let store = buffer(usize(4096)).
        let arena = borrow_mut(store, usize(0), usize(4096)).
        let tiny = slice_mut(arena, usize(0), usize(64)).
        borrow_end(tiny).
        borrow_end(arena).
        buffer_drop(store).
        # A listener rejected by validation stays caller-owned. The syscall
        # probes below check the numeric fd, never bypassing owner checking.
        let mut socket = 0.
        unsafe:
            set socket = syscall(41, 2, 1, 0, 0, 0, 0).
        if socket < 0:
            return 4.
        let probeStore = buffer(usize(4096)).
        let probe = borrow_mut(probeStore, usize(0), usize(4096)).
        borrow_end(probe).
        if ServerServe(socket, probeStore, 0) != -22:
            set failure = 5.
        let mut live = 0.
        unsafe:
            set live = syscall(72, socket, 1, 0, 0, 0, 0).
        if live < 0:
            if failure == 0:
                set failure = 6.
        let negStore = buffer(usize(4096)).
        if ServerServe(-1, negStore, 1) != -22:
            if failure == 0:
                set failure = 7.
        # Valid but non-listening sockets fail accept after ownership transfer.
        # Descriptor and mapping release are checked separately below.
        let liveStore = buffer(usize(4096)).
        if ServerServe(socket, liveStore, 1) != -22:
            if failure == 0:
                set failure = 8.
        let mut closed = 0.
        unsafe:
            set closed = syscall(72, socket, 1, 0, 0, 0, 0).
        if closed != -9:
            if failure == 0:
                set failure = 9.
        return failure.
"#,
    );
    let mut child = fixture.spawn(Stdio::null(), Stdio::null());
    assert!(child.finish().success(), "SAL safe ownership checks failed");
}

#[test]
fn setup_signal_socket_option_and_fork_failures_release_owned_resources() {
    // A real kernel seccomp filter makes otherwise nondeterministic resource
    // failures reproducible without replacing any SAL lifecycle operation.
    // Public server/app helpers stay safe SystemCall-only; ONLY this test's
    // OS setup (BPF install, raw bind, fcntl/mincore probes) uses narrow
    // explicit unsafe blocks. The app dispatch boundary is never laundered.
    for (syscall_number, errno) in [(13, 1), (54, 1), (57, 11)] {
        let fixture = Fixture::build(&format!(
            r#"use "server.sal".
use "linux/io.sal".
use "linux/net.sal".
entity ProbeFilter:
    layout "C".
    has load of type u64.
    has compare of type u64.
    has deny of type u64.
    has allow of type u64.
entity ProbeProgram:
    layout "C".
    has length of type u64.
    has instructions of type usize.
entity ProbeCell:
    layout "C".
    has value of type u64.
operation ProbeInstall:
    returns i64.
    effects: SystemCall.
    body:
        # Four classic BPF instructions as fixed C-layout words, not byte loops.
        let filter = ProbeFilter(u64(32), u64(16777237) + u64({syscall_number}) * u64(4294967296), u64(6) + u64(327680 + {errno}) * u64(4294967296), u64(6) + u64(2147418112) * u64(4294967296)).
        let mut pointer = usize(0).
        let mut result = 0.
        unsafe:
            set pointer = address(filter).
            set result = syscall(157, 38, 1, 0, 0, 0, 0).
        if result < 0:
            return result.
        let program = ProbeProgram(u64(4), pointer).
        unsafe:
            set result = syscall(317, 1, 0, address(program), 0, 0, 0).
        return result.
operation ProbeListen:
    accepts arena of type MutBytes.
    returns i64.
    effects: SystemCall.
    body:
        let formatted = LinuxIpv4Address(arena, 2130706433, 0).
        if formatted < 0:
            return formatted.
        let endpoint = view(arena).
        let listener = LinuxTcpListen(endpoint, i64(4)).
        borrow_end(endpoint).
        if listener < 0:
            return listener.
        let endpointView = view(arena).
        let length = ProbeCell(u64(16)).
        let mut named = 0.
        unsafe:
            set named = syscall(51, listener, address(endpointView), address(length), 0, 0, 0).
        borrow_end(endpointView).
        if named < 0:
            LinuxClose(listener).
            return named.
        let head = view(arena).
        let port = slice(head, usize(2), usize(2)).
        LinuxWriteAll(1, port).
        borrow_end(port).
        borrow_end(head).
        return listener.
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type MutBytes.
    returns i64.
    effects: SystemCall.
    body:
        return LinuxWriteAll(client, bytes("unexpected dispatch after injected failure")).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let store = buffer(usize(4096)).
        let arena = borrow_mut(store, usize(0), usize(4096)).
        let listener = ProbeListen(arena).
        let mut arenaAddress = usize(0).
        unsafe:
            set arenaAddress = address(view(arena)).
        borrow_end(arena).
        let installed = ProbeInstall().
        if listener >= 0 && installed == 0:
            if ServerServe(listener, store, 1) != -{errno}:
                set failure = 86.
        else:
            set failure = 85.
            if listener >= 0:
                LinuxClose(listener).
            buffer_drop(store).
        let mut listenerLive = 0.
        let mut siblingLive = 0.
        let mut resident = 0.
        let residency = ProbeCell(u64(0)).
        unsafe:
            set listenerLive = syscall(72, listener, 1, 0, 0, 0, 0).
            set siblingLive = syscall(72, listener + 1, 1, 0, 0, 0, 0).
            set resident = syscall(27, arenaAddress, 4096, address(residency), 0, 0, 0).
        if failure == 0 && listenerLive != -9:
            set failure = 87.
        if failure == 0 && siblingLive != -9:
            set failure = 88.
        if failure == 0 && resident != -12:
            set failure = 89.
        return failure.
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
use "linux/io.sal".
use "linux/net.sal".
use "net.sal".
operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type MutBytes.
    returns i64.
    effects: SystemCall.
    body:
        return LinuxWriteAll(client, bytes("unexpected dispatch")).
operation Main:
    returns i64.
    effects: SystemCall.
    body:
        let mut failure = 0.
        let store = buffer(usize(4096)).
        let listener = NetTcpListen(u64(2130706433), 0, 4).
        let port = NetLocalPort(listener).
        if listener < 0 || port <= 0:
            set failure = 81.
        LinuxWriteAll(1, bytes("B")).
        let marker = borrow_mut(store, usize(64), usize(1)).
        if LinuxReadExact(0, marker) != 1:
            set failure = 83.
        borrow_end(marker).
        let mut iteration = 0.
        while iteration < 32 && failure == 0:
            if ServerRun(2130706433, port, usize(4096), 1) != -98:
                set failure = 84.
            if ServerRun(2130706433, 65536, usize(4096), 1) != -22:
                set failure = 85.
            set iteration = iteration + 1.
        LinuxWriteAll(1, bytes("A")).
        let done = borrow_mut(store, usize(64), usize(1)).
        if LinuxReadExact(0, done) != 1:
            set failure = 86.
        borrow_end(done).
        if listener >= 0:
            LinuxClose(listener).
        buffer_drop(store).
        return failure.
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
