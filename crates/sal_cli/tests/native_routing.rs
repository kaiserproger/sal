#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "sal-native-routing-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(path.join("linux")).expect("fixture directory");
        let library = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in ["bytes.sal", "routing.sal", "linux/memory.sal"] {
            std::fs::copy(library.join(name), path.join(name)).expect("copy real SAL library");
        }
        Self(path)
    }

    fn execute(&self, checks: &Checks) {
        let source = format!(
            "use \"routing.sal\".\nuse \"linux/memory.sal\".\n\
             operation Main:\n    returns i64.\n    effects: SystemCall, UnsafeMemory.\n    body:\n\
             {}        return 0.\n",
            checks.body
        );
        let source_path = self.0.join("case.sal");
        std::fs::write(&source_path, &source).expect("write native fixture");
        let build = Command::new(env!("CARGO_BIN_EXE_sal"))
            .arg("build-exe")
            .arg(&source_path)
            .arg("--out")
            .arg(self.0.join("out"))
            .output()
            .expect("compile routing fixture");
        success(&build);
        let mut child = Running(
            Command::new(self.0.join("out/case"))
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .expect("run native routing fixture"),
        );
        let deadline = Instant::now() + Duration::from_secs(15);
        loop {
            if let Some(status) = child.0.try_wait().expect("native status") {
                assert!(
                    status.success(),
                    "native routing result {status}; checks (exit code, expression): {:?}\n{source}",
                    checks.expressions
                );
                break;
            }
            assert!(
                Instant::now() < deadline,
                "native routing fixture timed out\n{source}"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
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

#[derive(Default)]
struct Checks {
    body: String,
    expressions: Vec<String>,
}
impl Checks {
    fn expect(&mut self, expression: impl AsRef<str>, expected: impl std::fmt::Display) {
        let expression = expression.as_ref();
        self.expressions.push(format!("{expression} == {expected}"));
        let code = self.expressions.len();
        assert!(code < 256, "exit codes must remain distinct");
        writeln!(
            self.body,
            "        if {expression} != {expected}:\n            return {code}."
        )
        .unwrap();
    }
    fn memory(&mut self) {
        self.body.push_str(concat!(
            "        let mapping = LinuxMapMemory(usize(4096)).\n",
            "        if mapping < 0:\n            return 255.\n",
            "        let buffer = usize(mapping).\n",
            "        let output = buffer + 1024.\n",
        ));
    }
    fn raw(&mut self, value: &[u8]) {
        for (offset, value) in value.iter().enumerate() {
            writeln!(self.body, "        store8(buffer + {offset}, u8({value})).").unwrap();
        }
    }
    fn finish_memory(&mut self) {
        self.expect("LinuxUnmapMemory(buffer, usize(4096))", 0);
    }
}
fn text(value: &str) -> String {
    let mut quoted = String::from("\"");
    for ch in value.chars() {
        match ch {
            '"' => quoted.push_str("\\\""),
            '\\' => quoted.push_str("\\\\"),
            '\n' => quoted.push_str("\\n"),
            '\r' => quoted.push_str("\\r"),
            '\t' => quoted.push_str("\\t"),
            ch if ch.is_control() => write!(quoted, "\\u{{{:x}}}", u32::from(ch)).unwrap(),
            ch => quoted.push(ch),
        }
    }
    quoted.push('"');
    quoted
}
fn bytes(value: &str) -> String {
    format!("bytes({})", text(value))
}

#[test]
fn literals_match_raw_with_exact_segment_counts() {
    let mut checks = Checks::default();
    for (pattern, path, expected) in [
        ("/", "/", true),
        ("/say", "/say", true),
        ("/say", "/say/", false),
        ("/say/", "/say", false),
        ("/say/", "/say/", true),
        ("/a/b", "/a/b", true),
        ("/a/b", "/a/c", false),
        ("/a/b", "/a/b/c", false),
        ("/a/b", "/a", false),
        ("/a//b", "/a//b", true),
        ("/a//b", "/a/b", false),
        ("/Say", "/say", false),
        ("/a%b", "/a%b", true),
        ("/a%b", "/aX", false),
        ("/say/:what", "/say/hi", true),
        ("/say/:what", "/say/", false),
        ("/say/:what", "/say/hi/", false),
        ("/say/:what", "/say/hi/there", false),
        ("/:x", "/hi", true),
        ("/:x", "/", false),
        ("/:x", "/a/b", false),
        ("/say/:", "/say/", false),
        ("", "/", false),
        ("/", "", false),
        ("say/hi", "/say/hi", false),
        ("/say/hi", "say/hi", false),
        ("/a/:x", "/a/", false),
    ] {
        checks.expect(
            format!("RouteMatch({}, {})", bytes(pattern), bytes(path)),
            expected,
        );
    }
    Fixture::new().execute(&checks);
}

#[test]
fn captures_are_raw_with_last_repeated_name_winning() {
    let mut checks = Checks::default();
    for (pattern, path, name, expected) in [
        ("/say/:what", "/say/hi", "what", "hi"),
        ("/say/:what", "/say/other", "what", "other"),
        ("/say/:what", "/say/hi", "missing", ""),
        ("/say/:what", "/say/hi", "", ""),
        ("/say/:what", "/nope/hi", "what", ""),
        ("/say/hi", "/say/hi", "what", ""),
        ("/:x/:x", "/a/b", "x", "b"),
        ("/:x", "/a%20b", "x", "a%20b"),
        ("/:x", "/a+b", "x", "a+b"),
        ("/:x", "/", "x", ""),
        ("/a/:x", "/a/b/c", "x", ""),
        ("/say/:what", "/say/é", "what", "é"),
    ] {
        checks.expect(
            format!(
                "RouteCapture({}, {}, {})",
                bytes(pattern),
                bytes(path),
                bytes(name)
            ),
            bytes(expected),
        );
    }
    Fixture::new().execute(&checks);
}

#[test]
fn decode_is_strict_with_exact_small_capacities() {
    let mut checks = Checks::default();
    checks.memory();
    checks.expect(
        format!("RouteDecode({}, output, usize(16))", bytes("a+b")),
        3,
    );
    checks.expect("bytes_at(output, usize(3))", bytes("a+b"));
    // Exact one-byte capacity must succeed for a single escape.
    checks.expect(
        format!("RouteDecode({}, output, usize(1))", bytes("%41")),
        1,
    );
    checks.expect("bytes_at(output, usize(1))", bytes("A"));
    checks.expect(
        format!("RouteDecode({}, output, usize(0))", bytes("%41")),
        -28,
    );
    // Escapes may yield slash and NUL; plus is never decoded.
    checks.expect(
        format!("RouteDecode({}, output, usize(1))", bytes("%2F")),
        1,
    );
    checks.expect("bytes_at(output, usize(1))", bytes("/"));
    checks.expect(
        format!("RouteDecode({}, output, usize(1))", bytes("%00")),
        1,
    );
    checks.expect("load8(output)", "u8(0)");
    checks.expect(
        format!("RouteDecode({}, output, usize(1))", bytes("%7e")),
        1,
    );
    checks.expect("bytes_at(output, usize(1))", bytes("~"));
    checks.expect(format!("RouteDecode({}, output, usize(0))", bytes("")), 0);
    checks.expect(
        format!("RouteDecode({}, output, usize(3))", bytes("abc")),
        3,
    );
    checks.expect(
        format!("RouteDecode({}, output, usize(2))", bytes("abc")),
        -28,
    );
    // Two decoded bytes with capacity one fail after storing the valid prefix.
    checks.expect(
        format!("RouteDecode({}, output, usize(1))", bytes("%41%42")),
        -28,
    );
    checks.expect("load8(output)", "u8(65)");
    // Raw and percent-encoded UTF-8 pass through the same strict scalar check.
    checks.expect(format!("RouteDecode({}, output, usize(8))", bytes("é")), 2);
    checks.expect("bytes_at(output, usize(2))", bytes("é"));
    checks.expect(
        format!("RouteDecode({}, output, usize(8))", bytes("%C3%A9")),
        2,
    );
    checks.expect("bytes_at(output, usize(2))", bytes("é"));
    for bad in [
        "%",
        "%4",
        "a%2",
        "%2G",
        "%GG",
        "%C3",
        "%E2%82",
        "%C0%80",
        "%ED%A0%80",
        "%F4%90%80%80",
        "%80",
    ] {
        checks.expect(
            format!("RouteDecode({}, output, usize(128))", bytes(bad)),
            -22,
        );
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn malformed_raw_utf8_is_rejected_at_decode_boundaries() {
    let mut checks = Checks::default();
    checks.memory();
    for invalid in [
        &[0x80][..],
        &[0xbf],
        &[0xc0, 0x80],
        &[0xc1, 0xbf],
        &[0xc2],
        &[0xc2, 0x20],
        &[0xe0, 0x80, 0x80],
        &[0xed, 0xa0, 0x80],
        &[0xed, 0xbf, 0xbf],
        &[0xe2, 0x82],
        &[0xf0, 0x80, 0x80, 0x80],
        &[0xf4, 0x90, 0x80, 0x80],
        &[0xf5, 0x80, 0x80, 0x80],
        &[0xf0, 0x9f, 0x98],
        &[0xfe],
        &[0xff],
    ] {
        checks.raw(invalid);
        let input = format!("bytes_at(buffer, usize({}))", invalid.len());
        checks.expect(format!("RouteDecode({input}, output, usize(128))"), -22);
    }
    // The exact legal boundaries adjacent to overlongs/surrogates/out-of-range.
    for valid in [
        "\u{7f}",
        "\u{80}",
        "\u{7ff}",
        "\u{800}",
        "\u{d7ff}",
        "\u{e000}",
        "\u{ffff}",
        "\u{10000}",
        "\u{10ffff}",
    ] {
        checks.expect(
            format!("RouteDecode({}, output, usize(8))", bytes(valid)),
            valid.len(),
        );
        checks.expect(
            format!("bytes_at(output, usize({}))", valid.len()),
            bytes(valid),
        );
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}
