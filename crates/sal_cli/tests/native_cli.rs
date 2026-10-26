#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "sal-native-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("temporary fixture directory");
        Self(path)
    }
    fn source(&self, source: &str) -> PathBuf {
        let path = self.0.join("example.sal");
        std::fs::write(&path, source).expect("write fixture");
        path
    }
    fn build(&self, command: &str, source: &Path) -> Output {
        Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg(command)
            .arg(source)
            .arg("--out")
            .arg(self.0.join("out"))
            .output()
            .expect("run SAL compiler")
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
        "status={}\nstdout={}\nstderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn native_functions_execute_calls_bindings_and_branches_without_dynamic_runtime() {
    let fixture = Fixture::new();
    let source = fixture.source(
        r#"operation Sum:
  accepts a of type i64.
  accepts b of type i64.
  returns i64.
  body:
    let result = a + b.
    return result.
operation Main:
  returns Text.
  body:
    let answer = Sum(20, 22).
    if answer == 42:
      return "{\"answer\": 42}".
    else:
      return "wrong branch".
"#,
    );
    success(&fixture.build("build-exe", &source));
    let artifact = fixture.0.join("out/example");
    let output = Command::new(&artifact)
        .output()
        .expect("run native executable");
    success(&output);
    assert_eq!(output.stdout, b"{\"answer\": 42}\n");
    let headers = Command::new("readelf")
        .arg("-lW")
        .arg(&artifact)
        .output()
        .expect("inspect ELF");
    success(&headers);
    let headers = String::from_utf8_lossy(&headers.stdout);
    assert!(
        !headers.contains("INTERP"),
        "native executable must not request a dynamic loader: {headers}"
    );
    let dynamic = Command::new("readelf")
        .arg("-dW")
        .arg(&artifact)
        .output()
        .expect("inspect dynamic dependencies");
    success(&dynamic);
    assert!(!String::from_utf8_lossy(&dynamic.stdout).contains("NEEDED"));
}

#[test]
fn c_caller_executes_sal_exports_and_internal_helpers() {
    let fixture = Fixture::new();
    let source = fixture.source(
        r#"operation Add:
  accepts a of type i64.
  accepts b of type i64.
  returns i64.
  body:
    return a + b.
operation Total:
  accepts a of type i64.
  accepts b of type i64.
  returns i64.
  exports "C" as "sal_total".
  body:
    return Add(a, b).
operation Equal:
  accepts a of type i64.
  accepts b of type i64.
  returns bool.
  exports "C" as "sal_equal".
  body:
    return a == b.
operation Six:
  accepts a of type i64.
  accepts b of type i64.
  accepts c of type i64.
  accepts d of type i64.
  accepts e of type i64.
  accepts f of type i64.
  returns i64.
  exports "C" as "sal_six".
  body:
    return Add(a, b) + Add(c, d) + Add(e, f).
"#,
    );
    success(&fixture.build("build-lib", &source));
    let out = fixture.0.join("out");
    let c = fixture.0.join("caller.c");
    std::fs::write(
        &c,
        r#"#include "example.h"
int main(void) {
    if (sal_total(-9, 51) != 42) return 1;
    if (!sal_equal(7, 7)) return 2;
    if (sal_equal(7, 8)) return 3;
    if (sal_six(1, 2, 4, 8, 16, 32) != 63) return 4;
    return 0;
}
"#,
    )
    .expect("write C caller");
    let executable = fixture.0.join("caller");
    let compile = Command::new("cc")
        .arg("-Werror")
        .arg("-Wall")
        .arg("-I")
        .arg(&out)
        .arg(&c)
        .arg(out.join("libexample.a"))
        .arg("-o")
        .arg(&executable)
        .output()
        .expect("compile C caller");
    success(&compile);
    success(&Command::new(&executable).output().expect("run C caller"));
    let symbols = Command::new("nm")
        .arg("-u")
        .arg(out.join("main.o"))
        .output()
        .expect("inspect undefined library symbols");
    success(&symbols);
    assert!(
        symbols.stdout.is_empty(),
        "SAL library must not import a host runtime: {}",
        String::from_utf8_lossy(&symbols.stdout)
    );
}

#[test]
fn body_type_mismatch_is_rejected_before_emission() {
    let fixture = Fixture::new();
    let source = fixture.source(
        "operation Main:\n  returns Text.\n  body:\n    let result = true.\n    return result.\n",
    );
    let output = fixture.build("build-exe", &source);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("B102"),
        "{output:?}"
    );
    assert!(!fixture.0.join("out/example").exists());
}

#[test]
fn text_is_not_silently_exported_using_an_unsafe_c_layout() {
    let fixture = Fixture::new();
    let source = fixture.source("operation Greeting:\n  returns Text.\n  exports \"C\" as \"greeting\".\n  body:\n    return \"hello\".\n");
    let output = fixture.build("build-lib", &source);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("N100"),
        "{output:?}"
    );
    assert!(!fixture.0.join("out/libexample.a").exists());
}

#[test]
fn repeated_native_builds_produce_identical_binary_bytes() {
    let fixture = Fixture::new();
    let source = fixture
        .source("operation Main:\n  returns Text.\n  body:\n    return \"deterministic\".\n");
    success(&fixture.build("build-exe", &source));
    let artifact = fixture.0.join("out/example");
    let first = std::fs::read(&artifact).expect("read first executable");
    success(&fixture.build("build-exe", &source));
    assert_eq!(
        first,
        std::fs::read(&artifact).expect("read rebuilt executable")
    );
}

#[test]
fn native_text_calls_preserve_bytes_and_compare_content() {
    let fixture = Fixture::new();
    let source = fixture.source(
        r#"operation Echo:
  accepts value of type Text.
  returns Text.
  body:
    return value.
operation Main:
  returns Text.
  body:
    let text = Echo("ёж {\"x\": 7}").
    if text == "ёж {\"x\": 7}":
      if text != "ёж {\"x\": 8}":
        return text.
      else:
        return "wrong inequality".
    else:
      return "wrong equality".
"#,
    );
    success(&fixture.build("build-exe", &source));
    let output = Command::new(fixture.0.join("out/example"))
        .output()
        .expect("execute text code");
    success(&output);
    assert_eq!(output.stdout, "ёж {\"x\": 7}\n".as_bytes());
}

#[test]
fn canonical_hello_builds_and_prints_without_translation() {
    let fixture = Fixture::new();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/native/hello.sal");
    success(&fixture.build("build-exe", &source));
    let output = Command::new(fixture.0.join("out/hello"))
        .output()
        .expect("run compiled SAL");
    success(&output);
    assert_eq!(output.stdout, b"Hello, world!\n");
}

#[test]
fn sal_library_io_writes_binary_bytes_without_text_coercion() {
    let fixture = Fixture::new();
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/native/binary_io.sal");
    success(&fixture.build("build-exe", &source));
    let output = Command::new(fixture.0.join("out/binary_io"))
        .output()
        .expect("execute SAL-authored I/O");
    success(&output);
    assert_eq!(output.stdout, b"A\0\xff\n");
}

#[test]
fn source_uses_resolve_relative_transitive_diamond_once() {
    let fixture = Fixture::new();
    let library = fixture.0.join("lib");
    std::fs::create_dir(&library).expect("create library");
    std::fs::write(
        library.join("common.sal"),
        "operation Add:\n  accepts a of type i64.\n  accepts b of type i64.\n  returns i64.\n  body:\n    return a + b.\n",
    )
    .expect("write shared dependency");
    std::fs::write(
        library.join("left.sal"),
        "use \"common.sal\".\noperation Left:\n  returns i64.\n  body:\n    return Add(20, 20).\n",
    )
    .expect("write left dependency");
    std::fs::write(
        library.join("right.sal"),
        "use \"./common.sal\".\noperation Right:\n  returns i64.\n  body:\n    return Add(1, 1).\n",
    )
    .expect("write right dependency");
    let source = fixture.source(
        "use \"lib/left.sal\".\nuse \"lib/right.sal\".\noperation Main:\n  returns i64.\n  body:\n    if Left() + Right() == 42:\n      return 0.\n    else:\n      return 1.\n",
    );
    success(&fixture.build("build-exe", &source));
    let output = Command::new(fixture.0.join("out/example"))
        .output()
        .expect("execute imported operations");
    success(&output);
    assert!(output.stdout.is_empty());
}

#[test]
fn source_cycle_is_a_diagnostic_not_unbounded_recursion() {
    let fixture = Fixture::new();
    let source = fixture.source("use \"cycle.sal\".\n");
    std::fs::write(fixture.0.join("cycle.sal"), "use \"example.sal\".\n")
        .expect("write cyclic dependency");
    let output = Command::new(env!("CARGO_BIN_EXE_sal"))
        .arg("check")
        .arg(&source)
        .output()
        .expect("check cyclic sources");
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stdout).contains("SRC100"));
}

#[test]
fn imported_semantic_error_reports_the_original_file() {
    let fixture = Fixture::new();
    let source = fixture.source("use \"imported.sal\".\n");
    std::fs::write(
        fixture.0.join("imported.sal"),
        "operation Bad:\n  returns Text.\n  body:\n    return false.\n",
    )
    .expect("write invalid dependency");
    let output = Command::new(env!("CARGO_BIN_EXE_sal"))
        .arg("check")
        .arg(&source)
        .output()
        .expect("check imported source");
    assert_eq!(output.status.code(), Some(1));
    let diagnostic = String::from_utf8_lossy(&output.stdout);
    assert!(diagnostic.contains("B102"));
    assert!(diagnostic.contains(&format!("{}:", fixture.0.join("imported.sal").display())));
}

#[test]
fn sal_byte_search_handles_overlap_absence_and_empty_needle() {
    let fixture = Fixture::new();
    std::fs::copy(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/bytes.sal"),
        fixture.0.join("bytes.sal"),
    )
    .expect("copy real SAL byte algorithms");
    let source = fixture.source(
        r#"use "bytes.sal".
operation Main:
  returns i64.
  body:
    if BytesFind(bytes("aaba"), bytes("aba")) != 1:
      return 1.
    if BytesFind(bytes("ab"), bytes("ba")) != -1:
      return 2.
    if BytesFind(bytes("ab"), bytes("abc")) != -1:
      return 3.
    if BytesFind(bytes(""), bytes("")) != 0:
      return 4.
    if BytesStartsWith(bytes("abcd"), bytes("ab")) == false:
      return 5.
    if BytesStartsWith(bytes("a"), bytes("ab")):
      return 6.
    return 0.
"#,
    );
    success(&fixture.build("build-exe", &source));
    success(
        &Command::new(fixture.0.join("out/example"))
            .output()
            .expect("execute SAL byte search"),
    );
}

#[test]
fn sal_tcp_library_reads_and_echoes_binary_data_on_its_owned_ephemeral_socket() {
    struct OwnedChild(Child);
    impl Drop for OwnedChild {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }

    let fixture = Fixture::new();
    let source = fixture.source(
        r#"use "std/linux/net.sal".
use "std/net.sal".
use "std/binary.sal".
operation Main:
  returns i64.
  effects: SystemCall.
  body:
    let arena = buffer(usize(64)).
    let endpoint = borrow_mut(arena, usize(0), usize(16)).
    if LinuxIpv4Address(endpoint, u64(2130706433), 0) != 0:
      borrow_end(endpoint).
      buffer_drop(arena).
      return 2.
    let listener = LinuxTcpListen(view(endpoint), 1).
    borrow_end(endpoint).
    if listener < 0:
      buffer_drop(arena).
      return 3.
    let port = NetLocalPort(listener).
    let ready = borrow_mut(arena, usize(16), usize(2)).
    let encoded = BinaryWriteU16Be(ready, usize(0), port).
    let published = LinuxWriteAll(1, view(ready)).
    borrow_end(ready).
    if port < 1 || encoded != 2 || published != 2:
      LinuxClose(listener).
      buffer_drop(arena).
      return 5.
    let client = LinuxTcpAccept(listener).
    LinuxClose(listener).
    if client < 0:
      buffer_drop(arena).
      return 6.
    let echo = borrow_mut(arena, usize(32), usize(4)).
    let received = LinuxReadExact(client, echo).
    let written = LinuxWriteAll(client, view(echo)).
    borrow_end(echo).
    LinuxClose(client).
    buffer_drop(arena).
    if received != 4 || written != 4:
      return 7.
    return 0.
"#,
    );
    success(&fixture.build("build-exe", &source));
    let mut child = OwnedChild(
        Command::new(fixture.0.join("out/example"))
            .stdout(Stdio::piped())
            .spawn()
            .expect("launch native SAL listener"),
    );
    let mut stdout = child.0.stdout.take().expect("listener stdout");
    let (sender, receiver) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut port = [0; 2];
        let result = stdout
            .read_exact(&mut port)
            .map(|()| u16::from_be_bytes(port));
        let _ = sender.send(result);
    });
    let port = receiver
        .recv_timeout(Duration::from_secs(5))
        .expect("native listener must publish its bound port")
        .expect("read bound port");
    reader.join().expect("port reader");
    assert!(
        child
            .0
            .try_wait()
            .expect("inspect owned listener")
            .is_none(),
        "the process publishing readiness must own the live listener"
    );
    let mut client = TcpStream::connect(("127.0.0.1", port)).expect("connect to owned listener");
    client
        .set_read_timeout(Some(Duration::from_secs(5)))
        .expect("bound echo read");
    client
        .set_write_timeout(Some(Duration::from_secs(5)))
        .expect("bound request write");
    client.write_all(b"\0\xff").expect("write first fragment");
    client.write_all(b"A\n").expect("write second fragment");
    let mut echoed = [0; 4];
    client.read_exact(&mut echoed).expect("read native echo");
    assert_eq!(&echoed, b"\0\xffA\n");
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(status) = child.0.try_wait().expect("inspect listener exit") {
            assert!(status.success(), "native listener exit: {status}");
            break;
        }
        assert!(Instant::now() < deadline, "native listener did not exit");
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn sal_decimal_codec_handles_signed_extremes_and_preserves_short_output() {
    let fixture = Fixture::new();
    let source = fixture.source(
        r#"use "std/bytes.sal".
operation Main:
  returns i64.
  effects: SystemCall.
  body:
    if BytesParseDecimal(bytes("9223372036854775807")) != 9223372036854775807:
      return 1.
    if BytesParseDecimal(bytes("9223372036854775808")) != -75:
      return 2.
    if BytesParseDecimal(bytes("100000000000000000000")) != -75:
      return 3.
    if BytesParseDecimal(bytes("")) != -22:
      return 4.
    if BytesParseDecimal(bytes("-1")) != -22:
      return 5.
    if BytesParseDecimal(bytes("1x")) != -22:
      return 6.
    if BytesParseDecimal(bytes("00042")) != 42:
      return 7.
    let arena = buffer(usize(32)).
    let output = borrow_mut(arena, usize(0), usize(32)).
    let mut failure = 0.
    let full = slice_mut(output, usize(0), usize(20)).
    if BytesDecimal(-9223372036854775808, full) != 20 || view(full) != bytes("-9223372036854775808"):
      set failure = 9.
    let none = slice_mut(full, usize(0), usize(0)).
    if BytesDecimal(0, none) != -28:
      set failure = 11.
    borrow_end(none).
    if view(full) != bytes("-9223372036854775808"):
      set failure = 12.
    borrow_end(full).
    let one = slice_mut(output, usize(0), usize(1)).
    if BytesDecimal(0, one) != 1 || byte(one, usize(0)) != u8(48):
      set failure = 13.
    borrow_end(one).
    let max = slice_mut(output, usize(0), usize(19)).
    if BytesDecimal(9223372036854775807, max) != 19 || view(max) != bytes("9223372036854775807"):
      set failure = 15.
    borrow_end(max).
    let short = slice_mut(output, usize(0), usize(3)).
    if BytesCopy(short, bytes("copy")) != -28 || view(short) != bytes("922"):
      set failure = 17.
    borrow_end(short).
    let exact = slice_mut(output, usize(0), usize(4)).
    if BytesCopy(exact, bytes("copy")) != 4 || view(exact) != bytes("copy"):
      set failure = 19.
    borrow_end(exact).
    borrow_end(output).
    buffer_drop(arena).
    return failure.
"#,
    );
    success(&fixture.build("build-exe", &source));
    success(
        &Command::new(fixture.0.join("out/example"))
            .output()
            .expect("execute SAL decimal codecs"),
    );
}

#[test]
fn removed_model_flag_is_rejected_for_sal_builds() {
    let fixture = Fixture::new();
    let source = fixture.source("operation Main:\n  returns i64.\n  body:\n    return 0.\n");
    let output = Command::new(env!("CARGO_BIN_EXE_sal"))
        .arg("build-exe")
        .arg(&source)
        .arg("--out")
        .arg(fixture.0.join("out"))
        .arg("--model-command")
        .arg("sal-nonexistent-model-that-must-never-run")
        .output()
        .expect("reject removed model flag");
    assert_eq!(output.status.code(), Some(2));
    assert!(!fixture.0.join("out").exists());
}

#[test]
fn removed_anglish_command_and_flag_are_rejected() {
    let fixture = Fixture::new();
    let source = fixture.source("operation Main:\n  returns i64.\n  body:\n    return 0.\n");
    for args in [
        vec!["run-ang".to_string(), source.display().to_string()],
        vec![
            "build-exe".to_string(),
            "--ang".to_string(),
            source.display().to_string(),
            "--out".to_string(),
            fixture.0.join("out").display().to_string(),
        ],
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_sal"))
            .args(&args)
            .output()
            .expect("reject removed Anglish entrypoint");
        assert_eq!(output.status.code(), Some(2));
        assert!(!fixture.0.join("out").exists());
    }
}

#[test]
fn standard_package_is_embedded_and_deduplicated_after_normalization() {
    let fixture = Fixture::new();
    std::fs::create_dir_all(fixture.0.join("std/linux")).expect("local shadow package");
    std::fs::write(
        fixture.0.join("std/bytes.sal"),
        "operation BytesHexDigit:\n  accepts value of type u8.\n  returns i64.\n  body:\n    return 99.\n",
    ).expect("local source must not shadow the standard package");
    let source = fixture.source(
        "use \"std/bytes.sal\".\nuse \"std/linux/../bytes.sal\".\noperation Main:\n  returns i64.\n  body:\n    if BytesHexDigit(u8(102)) != 15:\n      return 1.\n    return 0.\n",
    );
    success(&fixture.build("build-exe", &source));
    success(
        &Command::new(fixture.0.join("out/example"))
            .output()
            .expect("run embedded library"),
    );
}

#[test]
fn standard_package_never_falls_back_to_local_or_escaping_sources() {
    let fixture = Fixture::new();
    std::fs::create_dir_all(fixture.0.join("std/linux")).expect("local shadow package");
    for path in ["outside.sal", "std/missing.sal"] {
        std::fs::write(
            fixture.0.join(path),
            "operation Intruder:\n  returns i64.\n  body:\n    return 99.\n",
        )
        .expect("source that must not be loaded");
    }
    for import in ["std/linux/../../outside.sal", "std/missing.sal"] {
        let source = fixture.source(&format!(
            "use \"{import}\".\noperation Main:\n  returns i64.\n  body:\n    return 0.\n"
        ));
        let output = fixture.build("build-exe", &source);
        assert!(!output.status.success(), "{import}");
        assert!(
            String::from_utf8_lossy(&output.stdout).contains("[SRC100]"),
            "{output:?}"
        );
    }
}
