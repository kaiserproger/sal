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
        std::fs::create_dir_all(&path).expect("fixture directory");
        let library = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in ["bytes.sal", "routing.sal"] {
            std::fs::copy(library.join(name), path.join(name)).expect("copy real SAL library");
        }
        Self(path)
    }

    fn execute(&self, checks: &Checks) {
        let source = format!(
            "use \"routing.sal\".\n\
             operation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n\
             \x20       let mut failure = 0.\n{}        return failure.\n",
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
    raws: usize,
}
impl Checks {
    fn expect(&mut self, expression: impl AsRef<str>, expected: impl std::fmt::Display) {
        let expression = expression.as_ref();
        self.expressions.push(format!("{expression} == {expected}"));
        let code = self.expressions.len();
        assert!(code < 256, "exit codes must remain distinct");
        writeln!(
            self.body,
            "        if failure == 0 && {expression} != {expected}:\n            set failure = {code}."
        )
        .unwrap();
    }
    fn memory(&mut self) {
        self.body.push_str(concat!(
            "        let store = buffer(usize(4096)).\n",
            "        let buffer = borrow_mut(store, usize(0), usize(1024)).\n",
            "        let output = borrow_mut(store, usize(1024), usize(3072)).\n",
        ));
    }
    fn raw(&mut self, value: &[u8]) {
        for (offset, value) in value.iter().enumerate() {
            writeln!(
                self.body,
                "        put(buffer, usize({offset}), u8({value}))."
            )
            .unwrap();
        }
        let tag = self.raws;
        self.raws += 1;
        writeln!(
            self.body,
            "        let rawInput{tag} = view(buffer).\n        let rawView{tag} = slice(rawInput{tag}, usize(0), usize({})).",
            value.len()
        )
        .unwrap();
    }
    fn finish_memory(&mut self) {
        self.body.push_str(concat!(
            "        borrow_end(buffer).\n",
            "        borrow_end(output).\n",
            "        buffer_drop(store).\n",
        ));
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
    checks.body.push_str(&format!(
        "        let plus = slice_mut(output, usize(0), usize(16)).\n        let plusCount = RouteDecode({}, plus).\n        borrow_end(plus).\n",
        bytes("a+b"),
    ));
    checks.expect("plusCount", 3);
    checks.body.push_str(
        "        let plusView = view(output).\n        let plusBytes = slice(plusView, usize(0), usize(plusCount)).\n",
    );
    checks.expect("plusBytes", bytes("a+b"));
    checks.body.push_str(concat!(
        "        borrow_end(plusView).\n",
        "        borrow_end(plusBytes).\n",
    ));
    // Exact one-byte loan must succeed for a single escape.
    checks.body.push_str(&format!(
        "        let one = slice_mut(output, usize(0), usize(1)).\n        let oneCount = RouteDecode({}, one).\n        borrow_end(one).\n",
        bytes("%41"),
    ));
    checks.expect("oneCount", 1);
    checks.body.push_str(
        "        let oneView = view(output).\n        let oneByte = slice(oneView, usize(0), usize(oneCount)).\n",
    );
    checks.expect("oneByte", bytes("A"));
    checks.body.push_str(concat!(
        "        borrow_end(oneView).\n",
        "        borrow_end(oneByte).\n",
    ));
    checks.body.push_str(&format!(
        "        let empty = slice_mut(output, usize(0), usize(0)).\n        let emptyCount = RouteDecode({}, empty).\n        borrow_end(empty).\n",
        bytes("%41"),
    ));
    checks.expect("emptyCount", -28);
    // Escapes may yield slash and NUL; plus is never decoded.
    checks.body.push_str(&format!(
        "        let slash = slice_mut(output, usize(0), usize(1)).\n        let slashCount = RouteDecode({}, slash).\n        borrow_end(slash).\n",
        bytes("%2F"),
    ));
    checks.expect("slashCount", 1);
    checks.body.push_str(
        "        let slashView = view(output).\n        let slashByte = slice(slashView, usize(0), usize(slashCount)).\n",
    );
    checks.expect("slashByte", bytes("/"));
    checks.body.push_str(concat!(
        "        borrow_end(slashView).\n",
        "        borrow_end(slashByte).\n",
    ));
    checks.body.push_str(&format!(
        "        let nul = slice_mut(output, usize(0), usize(1)).\n        let nulCount = RouteDecode({}, nul).\n        borrow_end(nul).\n",
        bytes("%00"),
    ));
    checks.expect("nulCount", 1);
    checks.body.push_str(
        "        let nulView = view(output).\n        let nulByte = byte(nulView, usize(0)).\n",
    );
    checks.expect("nulByte", "u8(0)");
    checks.body.push_str("        borrow_end(nulView).\n");
    checks.body.push_str(&format!(
        "        let tilde = slice_mut(output, usize(0), usize(1)).\n        let tildeCount = RouteDecode({}, tilde).\n        borrow_end(tilde).\n",
        bytes("%7e"),
    ));
    checks.expect("tildeCount", 1);
    checks.body.push_str(
        "        let tildeView = view(output).\n        let tildeByte = slice(tildeView, usize(0), usize(tildeCount)).\n",
    );
    checks.expect("tildeByte", bytes("~"));
    checks.body.push_str(concat!(
        "        borrow_end(tildeView).\n",
        "        borrow_end(tildeByte).\n",
    ));
    // Empty input decodes to zero with no capacity needed.
    checks.body.push_str(&format!(
        "        let blank = slice_mut(output, usize(0), usize(0)).\n        let blankCount = RouteDecode({}, blank).\n        borrow_end(blank).\n",
        bytes(""),
    ));
    checks.expect("blankCount", 0);
    checks.body.push_str(&format!(
        "        let word = slice_mut(output, usize(0), usize(3)).\n        let wordCount = RouteDecode({}, word).\n        borrow_end(word).\n",
        bytes("abc"),
    ));
    checks.expect("wordCount", 3);
    checks.body.push_str(&format!(
        "        let tight = slice_mut(output, usize(0), usize(2)).\n        let tightCount = RouteDecode({}, tight).\n        borrow_end(tight).\n",
        bytes("abc"),
    ));
    checks.expect("tightCount", -28);
    // Two decoded bytes with capacity one fail after storing the valid prefix.
    checks.body.push_str(&format!(
        "        let pair = slice_mut(output, usize(0), usize(1)).\n        let pairCount = RouteDecode({}, pair).\n        borrow_end(pair).\n",
        bytes("%41%42"),
    ));
    checks.expect("pairCount", -28);
    checks.body.push_str(
        "        let pairView = view(output).\n        let pairFirst = byte(pairView, usize(0)).\n",
    );
    checks.expect("pairFirst", "u8(65)");
    checks.body.push_str("        borrow_end(pairView).\n");
    // Raw and percent-encoded UTF-8 pass through the same strict scalar check.
    checks.body.push_str(&format!(
        "        let utf = slice_mut(output, usize(0), usize(8)).\n        let utfCount = RouteDecode({}, utf).\n        borrow_end(utf).\n",
        bytes("é"),
    ));
    checks.expect("utfCount", 2);
    checks.body.push_str(
        "        let utfView = view(output).\n        let utfBytes = slice(utfView, usize(0), usize(utfCount)).\n",
    );
    checks.expect("utfBytes", bytes("é"));
    checks.body.push_str(concat!(
        "        borrow_end(utfView).\n",
        "        borrow_end(utfBytes).\n",
    ));
    checks.body.push_str(&format!(
        "        let pct = slice_mut(output, usize(0), usize(8)).\n        let pctCount = RouteDecode({}, pct).\n        borrow_end(pct).\n",
        bytes("%C3%A9"),
    ));
    checks.expect("pctCount", 2);
    checks.body.push_str(
        "        let pctView = view(output).\n        let pctBytes = slice(pctView, usize(0), usize(pctCount)).\n",
    );
    checks.expect("pctBytes", bytes("é"));
    checks.body.push_str(concat!(
        "        borrow_end(pctView).\n",
        "        borrow_end(pctBytes).\n",
    ));
    for (index, bad) in [
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
    ]
    .iter()
    .enumerate()
    {
        checks.body.push_str(&format!(
            "        let bad{index} = slice_mut(output, usize(0), usize(128)).\n        let badCount{index} = RouteDecode({}, bad{index}).\n        borrow_end(bad{index}).\n",
            bytes(bad),
        ));
        checks.expect(format!("badCount{index}"), -22);
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn malformed_raw_utf8_is_rejected_at_decode_boundaries() {
    let mut checks = Checks::default();
    checks.memory();
    for (index, invalid) in [
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
    ]
    .iter()
    .enumerate()
    {
        checks.raw(invalid);
        let suffix = checks.raws - 1;
        checks.body.push_str(&format!(
            "        let bad{index} = slice_mut(output, usize(0), usize(128)).\n        let badCount{index} = RouteDecode(rawView{suffix}, bad{index}).\n        borrow_end(bad{index}).\n",
        ));
        checks.expect(format!("badCount{index}"), -22);
        checks.body.push_str(&format!(
            "        borrow_end(rawInput{suffix}).\n        borrow_end(rawView{suffix}).\n",
        ));
    }
    // The exact legal boundaries adjacent to overlongs/surrogates/out-of-range.
    for (index, valid) in [
        "\u{7f}",
        "\u{80}",
        "\u{7ff}",
        "\u{800}",
        "\u{d7ff}",
        "\u{e000}",
        "\u{ffff}",
        "\u{10000}",
        "\u{10ffff}",
    ]
    .iter()
    .enumerate()
    {
        checks.body.push_str(&format!(
            "        let edge{index} = slice_mut(output, usize(0), usize(8)).\n        let edgeCount{index} = RouteDecode({}, edge{index}).\n        borrow_end(edge{index}).\n",
            bytes(valid),
        ));
        checks.expect(format!("edgeCount{index}"), valid.len());
        checks.body.push_str(&format!(
            "        let edgeView{index} = view(output).\n        let edgeBytes{index} = slice(edgeView{index}, usize(0), usize(edgeCount{index})).\n",
        ));
        checks.expect(format!("edgeBytes{index}"), bytes(valid));
        checks.body.push_str(&format!(
            "        borrow_end(edgeView{index}).\n        borrow_end(edgeBytes{index}).\n",
        ));
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn decode_validates_each_transition_before_capacity_and_keeps_prefix() {
    let mut checks = Checks::default();
    checks.memory();
    for (index, (encoded, capacity, expected, first)) in [
        ("%80", 0, -22, None),
        ("%C0%80", 0, -22, None),
        ("%C3%41", 1, -22, Some(195)),
        ("%C3%A9", 1, -28, Some(195)),
        ("%ED%A0%80", 2, -22, Some(237)),
        ("%F4%90%80%80", 3, -22, Some(244)),
        ("%E2%82", 2, -22, Some(226)),
    ]
    .into_iter()
    .enumerate()
    {
        checks.body.push_str(&format!(
            "        BytesFill(output, u8(120)).\n        let slot{index} = slice_mut(output, usize(0), usize({capacity})).\n        let count{index} = RouteDecode({}, slot{index}).\n        borrow_end(slot{index}).\n",
            bytes(encoded),
        ));
        checks.expect(format!("count{index}"), expected);
        checks.body.push_str(&format!(
            "        let prefix{index} = view(output).\n        let sentinel{index} = byte(prefix{index}, usize({capacity})).\n",
        ));
        checks.expect(format!("sentinel{index}"), "u8(120)");
        if let Some(first) = first {
            checks.body.push_str(&format!(
                "        let first{index} = byte(prefix{index}, usize(0)).\n",
            ));
            checks.expect(format!("first{index}"), format!("u8({first})"));
        }
        checks
            .body
            .push_str(&format!("        borrow_end(prefix{index}).\n"));
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}
