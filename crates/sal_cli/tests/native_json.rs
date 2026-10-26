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
            "sal-native-json-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("fixture directory");
        let library = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in ["bytes.sal", "text.sal", "json.sal"] {
            std::fs::copy(library.join(name), path.join(name)).expect("copy real SAL library");
        }
        Self(path)
    }

    fn execute(&self, checks: &Checks) {
        let source = format!(
            "use \"json.sal\".\n\
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
            .expect("compile JSON fixture");
        success(&build);
        let mut child = Running(
            Command::new(self.0.join("out/case"))
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .expect("run native JSON fixture"),
        );
        let deadline = Instant::now() + Duration::from_secs(15);
        loop {
            if let Some(status) = child.0.try_wait().expect("native status") {
                assert!(
                    status.success(),
                    "native JSON result {status}; checks (exit code, expression): {:?}\n{source}",
                    checks.expressions
                );
                break;
            }
            assert!(
                Instant::now() < deadline,
                "native JSON fixture timed out\n{source}"
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
fn validates_nested_values_separators_numbers_and_complete_input() {
    let mut checks = Checks::default();
    for input in [
        "null",
        "true",
        "false",
        "0",
        "-0",
        "1234567890",
        "-123",
        "0.0",
        "-0.5",
        "1e0",
        "1E+23",
        "1e-999",
        "-12.34e+56",
        "[]",
        "{}",
        "[1,2,3]",
        "{\"a\":[true,false,null,{\"雪\":\"😀\"}],\"b\":-3.5e+8}",
        " \t\r\n [ 1 , { \"x\" : [] } ] \r\n",
        "\"\"",
        "\"hello\"",
        "{\"a\":1,\"a\":2}",
    ] {
        checks.expect(format!("JsonValidate({})", bytes(input)), "true");
    }
    for input in [
        "",
        " ",
        "tru",
        "True",
        "undefined",
        "+1",
        "01",
        "-01",
        "--1",
        "-",
        ".1",
        "1.",
        "1e",
        "1e+",
        "1e-",
        "1e+-1",
        "1.e2",
        "00.0",
        "0x10",
        "1 2",
        "truefalse",
        "nullx",
        "{}x",
        "[] []",
        "[1 2]",
        "[1,]",
        "[,1]",
        "[1,,2]",
        "[",
        "]",
        "{",
        "{a:1}",
        "{\"a\" 1}",
        "{\"a\":}",
        "{\"a\":1,}",
        "{,}",
        "{\"a\":1 \"b\":2}",
        "[{}",
        "{\"a\":[1,2}}",
        "\u{b}null",
        "null\u{c}",
        "\"unterminated",
    ] {
        checks.expect(format!("JsonValidate({})", bytes(input)), "false");
    }
    checks.expect(
        format!(
            "JsonValueEnd({}, usize(0), usize(4))",
            bytes(" \t[1]garbage")
        ),
        5,
    );
    checks.expect(
        format!("JsonValueEnd({}, usize(0), usize(1))", bytes("true!")),
        4,
    );
    checks.expect(
        format!("JsonValueEnd({}, usize(0), usize(1))", bytes("12.5e-2!")),
        7,
    );
    checks.expect(
        format!("JsonValueEnd({}, usize(2), usize(1))", bytes("xxnull")),
        6,
    );
    checks.expect("JsonValueEnd(bytes(\"0\"), usize(2), usize(64))", -22);
    checks.expect("JsonWhitespaceEnd(bytes(\" \"), usize(2))", -22);
    checks.expect("JsonWhitespaceEnd(bytes(\"\"), usize(0))", 0);
    checks.expect("JsonWhitespaceEnd(bytes(\" \"), usize(1))", 1);
    checks.expect(
        format!("JsonWhitespaceEnd({}, usize(0))", bytes(" \t\r\nx")),
        4,
    );
    checks.expect(
        format!("JsonWhitespaceEnd({}, usize(0))", bytes("\u{b}")),
        0,
    );
    Fixture::new().execute(&checks);
}

#[test]
fn explicit_depth_budget_and_default_64_are_enforced() {
    let mut checks = Checks::default();
    for (input, depth, expected) in [
        ("0", 0, -22),
        ("0", 1, 1),
        ("[]", 0, -22),
        ("[]", 1, 2),
        ("[0]", 1, -22),
        ("[0]", 2, 3),
        ("[[]]", 2, 4),
        ("{\"a\":0}", 1, -22),
        ("{\"a\":0}", 2, 7),
        ("[[0]]", 2, -22),
        ("[[0]]", 3, 5),
    ] {
        checks.expect(
            format!("JsonValueEnd({}, usize(0), usize({depth}))", bytes(input)),
            expected,
        );
    }
    for (nesting, expected) in [(63, "true"), (64, "false"), (100, "false")] {
        let input = format!("{}0{}", "[".repeat(nesting), "]".repeat(nesting));
        checks.expect(format!("JsonValidate({})", bytes(&input)), expected);
    }
    Fixture::new().execute(&checks);
}

#[test]
fn shared_utf8_scanner_preserves_json_scalar_and_escape_boundaries() {
    let mut checks = Checks::default();
    for (input, start, expected) in [
        ("", 0, -22),
        ("a", 1, -22),
        ("a", 2, -22),
        ("a", 0, 97),
        ("é", 0, 233),
        ("雪", 0, 38634),
        ("😀", 0, 128512),
        ("é", 1, -22),
    ] {
        checks.expect(
            format!("JsonUtf8Scalar({}, usize({start}))", bytes(input)),
            expected,
        );
    }
    for (input, expected) in [
        ("\\\"", 34),
        ("\\\\", 92),
        ("\\/", 47),
        ("\\b", 8),
        ("\\f", 12),
        ("\\n", 10),
        ("\\r", 13),
        ("\\t", 9),
        ("\\x", -22),
        ("\\uD7FF", 55295),
        ("\\uE000", 57344),
        ("\\uD800\\uDC00", 65536),
        ("\\uDBFF\\uDFFF", 1114111),
        ("\\uD800\\uDBFF", -22),
        ("\\uD800\\uE000", -22),
        ("\\uDC00", -22),
    ] {
        checks.expect(
            format!("JsonEscapeScalar({}, usize(0))", bytes(input)),
            expected,
        );
    }
    Fixture::new().execute(&checks);
}

#[test]
fn string_scanning_checks_escapes_utf8_and_surrogate_pairs() {
    let mut checks = Checks::default();
    for input in [
        "\"\"",
        "\"ascii\"",
        "\"é雪😀\"",
        "\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"",
        "\"\\u0000\\u001f\\u007F\\u0080\\u07ff\\u0800\\uD7ff\\ue000\\uffff\"",
        "\"\\uD800\\uDC00\\uDBFF\\uDFFF\"",
        "\"\\ud83d\\ude00\"",
    ] {
        checks.expect(
            format!("JsonStringEnd({}, usize(0))", bytes(input)),
            input.len(),
        );
        checks.expect(format!("JsonValidate({})", bytes(input)), "true");
    }
    for input in [
        "",
        "x",
        "\"",
        "\"\\",
        "\"\\x\"",
        "\"\\u\"",
        "\"\\u000\"",
        "\"\\u00xz\"",
        "\"\\uD800\"",
        "\"\\uDC00\"",
        "\"\\uDBFF\\uDBFF\"",
        "\"\\uD800x\"",
        "\"\\uD800\\n\"",
        "\"\\uD800\\u0000\"",
        "\"\\uD800\\uDC0\"",
        "\"a\nb\"",
        "\"\u{0}\"",
        "\"\u{1f}\"",
    ] {
        checks.expect(format!("JsonStringEnd({}, usize(0))", bytes(input)), -22);
        checks.expect(format!("JsonValidate({})", bytes(input)), "false");
    }
    checks.expect(
        format!("JsonStringEnd({}, usize(2))", bytes("xx\"a\"junk")),
        5,
    );
    checks.expect("JsonStringEnd(bytes(\"\"), usize(1))", -22);
    Fixture::new().execute(&checks);
}

#[test]
fn unsigned_integers_have_exact_grammar_and_overflow_errors() {
    let mut checks = Checks::default();
    for (input, expected) in [
        ("0", 0),
        ("1", 1),
        ("42", 42),
        ("9223372036854775806", 9223372036854775806_i64),
        ("9223372036854775807", i64::MAX),
        ("9223372036854775808", -75),
        ("18446744073709551615", -75),
        ("999999999999999999999999999999999", -75),
        ("", -22),
        ("00", -22),
        ("01", -22),
        ("-0", -22),
        ("-1", -22),
        ("+1", -22),
        (" 1", -22),
        ("1 ", -22),
        ("1.0", -22),
        ("1e0", -22),
        ("1\n", -22),
        ("999999999999999999999999x", -22),
    ] {
        checks.expect(format!("JsonUnsigned({})", bytes(input)), expected);
    }
    Fixture::new().execute(&checks);
}

#[test]
fn decode_and_encode_exact_bytes_capacity_edges_and_no_terminator() {
    let mut checks = Checks::default();
    checks.memory();
    // Fixed-position helpers: sentinel windows check no-terminator writes.
    checks.body.push_str(concat!(
        "        let sentinel = slice_mut(output, usize(128), usize(8)).\n",
        "        put(sentinel, usize(0), u8(255)).\n",
        "        borrow_end(sentinel).\n",
    ));
    let encoded = "\"A\\u0000\\b\\f\\n\\r\\t\\\"\\\\\\/é\\u96ea\\ud83d\\ude00\"";
    let decoded = "A\0\u{8}\u{c}\n\r\t\"\\/é雪😀";
    checks.body.push_str(concat!(
        "        let full = slice_mut(output, usize(0), usize(128)).\n",
        "        let fullCount = JsonDecodeString(bytes(\"\\\"A\\\\u0000\\\\b\\\\f\\\\n\\\\r\\\\t\\\\\\\"\\\\\\\\\\\\/é\\\\u96ea\\\\ud83d\\\\ude00\\\"\"), usize(0), full).\n",
        "        borrow_end(full).\n",
    ));
    checks.expect("fullCount", decoded.len());
    checks.body.push_str(concat!(
        "        let gotView = view(output).\n",
        "        let got = slice(gotView, usize(0), usize(fullCount)).\n",
    ));
    checks.expect("got", bytes(decoded));
    checks.body.push_str(concat!(
        "        borrow_end(gotView).\n",
        "        borrow_end(got).\n",
        "        let exactCap = slice_mut(output, usize(0), usize(17)).\n",
        "        put(exactCap, usize(10), u8(255)).\n",
        "        borrow_end(exactCap).\n",
    ));
    checks.body.push_str(&format!(
        "        let exact = slice_mut(output, usize(0), usize({})).\n        let exactCount = JsonDecodeString({}, usize(0), exact).\n        borrow_end(exact).\n",
        decoded.len(),
        bytes(encoded),
    ));
    checks.expect("exactCount", decoded.len());
    checks.body.push_str(
        "        let edgeView = view(output).\n        let edgeByte = slice(edgeView, usize(10), usize(1)).\n",
    );
    // The poisoned byte at offset 10 must be overwritten by the UTF-8 lead byte of é.
    checks.expect("edgeByte", "slice(bytes(\"é\"), usize(0), usize(1))");
    checks.body.push_str(concat!(
        "        borrow_end(edgeView).\n",
        "        borrow_end(edgeByte).\n",
    ));
    checks.body.push_str(&format!(
        "        let short = slice_mut(output, usize(0), usize({})).\n        let shortCount = JsonDecodeString({}, usize(0), short).\n        borrow_end(short).\n",
        decoded.len() - 1,
        bytes(encoded),
    ));
    checks.expect("shortCount", -28);
    checks.body.push_str(concat!(
        "        let empty = slice_mut(output, usize(0), usize(0)).\n",
        "        let emptyCount = JsonDecodeString(bytes(\"\\\"\\\"\"), usize(0), empty).\n",
        "        borrow_end(empty).\n",
    ));
    checks.expect("emptyCount", 0);
    checks.body.push_str(concat!(
        "        let missing = slice_mut(output, usize(0), usize(0)).\n",
        "        let missingCount = JsonDecodeString(bytes(\"\\\"x\\\"\"), usize(0), missing).\n",
        "        borrow_end(missing).\n",
    ));
    checks.expect("missingCount", -28);
    checks.body.push_str(concat!(
        "        let shifted = slice_mut(output, usize(0), usize(1)).\n",
        "        let shiftedCount = JsonDecodeString(bytes(\"xx\\\"A\\\"junk\"), usize(2), shifted).\n",
        "        borrow_end(shifted).\n",
    ));
    checks.expect("shiftedCount", 1);
    for (index, input) in [
        "\"a\\x\"",
        "\"a",
        "\"\\uD800\"",
        "\"\\uDC00\"",
        "\"\n\"",
        "x",
        "",
    ]
    .iter()
    .enumerate()
    {
        checks.body.push_str(&format!(
            "        let bad{index} = slice_mut(output, usize(0), usize(128)).\n        let badCount{index} = JsonDecodeString({}, usize(0), bad{index}).\n        borrow_end(bad{index}).\n",
            bytes(input),
        ));
        checks.expect(format!("badCount{index}"), -22);
    }
    checks.body.push_str(concat!(
        "        let past = slice_mut(output, usize(0), usize(128)).\n",
        "        let pastCount = JsonDecodeString(bytes(\"\"), usize(1), past).\n",
        "        borrow_end(past).\n",
    ));
    checks.expect("pastCount", -22);
    let controls: String = (0..32).map(char::from).collect();
    let value = format!("{controls}\"\\/é雪😀");
    let mut expected = String::from("\"");
    for code in 0..32 {
        write!(expected, "\\u{code:04x}").unwrap();
    }
    expected.push_str("\\\"\\\\/é雪😀\"");
    checks.body.push_str(&format!(
        "        let wide = slice_mut(output, usize(0), usize({})).\n        let wideCount = JsonWriteString({}, wide).\n        borrow_end(wide).\n",
        expected.len(),
        bytes(&value),
    ));
    checks.expect("wideCount", expected.len());
    checks.body.push_str(
        "        let wideView = view(output).\n        let wideBytes = slice(wideView, usize(0), usize(wideCount)).\n",
    );
    checks.expect("wideBytes", bytes(&expected));
    checks.body.push_str(concat!(
        "        borrow_end(wideView).\n",
        "        borrow_end(wideBytes).\n",
    ));
    checks.body.push_str(&format!(
        "        let narrow = slice_mut(output, usize(0), usize({})).\n        let narrowCount = JsonWriteString({}, narrow).\n        borrow_end(narrow).\n",
        expected.len() - 1,
        bytes(&value),
    ));
    checks.expect("narrowCount", -28);
    for (index, capacity) in [0usize, 1usize].iter().enumerate() {
        checks.body.push_str(&format!(
            "        let cap{index} = slice_mut(output, usize(0), usize({capacity})).\n        let capCount{index} = JsonWriteString(bytes(\"\"), cap{index}).\n        borrow_end(cap{index}).\n",
        ));
        checks.expect(format!("capCount{index}"), -28);
    }
    checks.body.push_str(concat!(
        "        let pair = slice_mut(output, usize(0), usize(2)).\n",
        "        let pairCount = JsonWriteString(bytes(\"\"), pair).\n",
        "        borrow_end(pair).\n",
    ));
    checks.expect("pairCount", 2);
    checks.body.push_str(concat!(
        "        let pairView = view(output).\n",
        "        let pairBytes = slice(pairView, usize(0), usize(pairCount)).\n",
    ));
    checks.expect("pairBytes", bytes("\"\""));
    checks.body.push_str(concat!(
        "        borrow_end(pairView).\n",
        "        borrow_end(pairBytes).\n",
    ));
    for (index, (value, capacity)) in [("x", 2), ("\0", 6), ("\"", 3), ("😀", 5)]
        .iter()
        .enumerate()
    {
        checks.body.push_str(&format!(
            "        let edgeWin{index} = slice_mut(output, usize(0), usize({capacity})).\n        let edgeCount{index} = JsonWriteString({}, edgeWin{index}).\n        borrow_end(edgeWin{index}).\n",
            bytes(value),
        ));
        checks.expect(format!("edgeCount{index}"), -28);
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn malformed_raw_utf8_is_rejected_by_all_string_paths() {
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
        let mut quoted = vec![b'"'];
        quoted.extend_from_slice(invalid);
        quoted.push(b'"');
        checks.raw(&quoted);
        let suffix = checks.raws - 1;
        let input = format!("rawView{suffix}");
        let base = format!("rawInput{suffix}");
        checks.expect(format!("JsonStringEnd({input}, usize(0))"), -22);
        checks.expect(format!("JsonValidate({input})"), "false");
        checks.body.push_str(&format!(
            "        let badWin{suffix} = slice_mut(output, usize(0), usize(128)).\n        let badCount{suffix} = JsonDecodeString({input}, usize(0), badWin{suffix}).\n        borrow_end(badWin{suffix}).\n",
        ));
        checks.expect(format!("badCount{suffix}"), -22);
        // Invalid scalar write path: each raw byte fails through JsonWriteString.
        checks.body.push_str(&format!(
            "        let rawWin{suffix} = slice_mut(output, usize(0), usize(128)).\n        let rawSingle{suffix} = slice({base}, usize(1), usize(1)).\n        let rawCount{suffix} = JsonWriteString(rawSingle{suffix}, rawWin{suffix}).\n        borrow_end(rawWin{suffix}).\n        borrow_end(rawSingle{suffix}).\n",
        ));
        checks.expect(format!("rawCount{suffix}"), -22);
        checks.body.push_str(&format!(
            "        borrow_end({base}).\n        borrow_end({input}).\n",
        ));
    }
    // The exact legal boundaries adjacent to overlongs/surrogates/out-of-range values.
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
        let quoted = format!("\"{valid}\"");
        checks.body.push_str(&format!(
            "        let edge{index} = slice_mut(output, usize(0), usize(4)).\n        let edgeCount{index} = JsonDecodeString({}, usize(0), edge{index}).\n        borrow_end(edge{index}).\n",
            bytes(&quoted),
        ));
        checks.expect(format!("edgeCount{index}"), valid.len());
        checks.body.push_str(&format!(
            "        let edgeView{index} = view(output).\n        let edgeBytes{index} = slice(edgeView{index}, usize(0), usize(edgeCount{index})).\n",
        ));
        checks.expect(format!("edgeBytes{index}"), bytes(valid));
        checks.body.push_str(&format!(
            "        borrow_end(edgeView{index}).\n        borrow_end(edgeBytes{index}).\n",
        ));
        checks.body.push_str(&format!(
            "        let word{index} = slice_mut(output, usize(0), usize(8)).\n        let wordCount{index} = JsonWriteString({}, word{index}).\n        borrow_end(word{index}).\n",
            bytes(valid),
        ));
        checks.expect(format!("wordCount{index}"), quoted.len());
        checks.body.push_str(&format!(
            "        let wordView{index} = view(output).\n        let wordBytes{index} = slice(wordView{index}, usize(0), usize(wordCount{index})).\n",
        ));
        checks.expect(format!("wordBytes{index}"), bytes(&quoted));
        checks.body.push_str(&format!(
            "        borrow_end(wordView{index}).\n        borrow_end(wordBytes{index}).\n",
        ));
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}
