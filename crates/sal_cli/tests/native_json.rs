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
        std::fs::create_dir_all(path.join("linux")).expect("fixture directory");
        let library = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib");
        for name in ["bytes.sal", "json.sal", "linux/memory.sal"] {
            std::fs::copy(library.join(name), path.join(name)).expect("copy real SAL library");
        }
        Self(path)
    }

    fn execute(&self, checks: &Checks) {
        let source = format!(
            "use \"json.sal\".\nuse \"linux/memory.sal\".\n\
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
    let encoded = "\"A\\u0000\\b\\f\\n\\r\\t\\\"\\\\\\/é\\u96ea\\ud83d\\ude00\"";
    let decoded = "A\0\u{8}\u{c}\n\r\t\"\\/é雪😀";
    checks
        .body
        .push_str("        store8(output + 128, u8(255)).\n");
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(0), output, usize(128))",
            bytes(encoded)
        ),
        decoded.len(),
    );
    checks.expect(
        format!("bytes_at(output, usize({}))", decoded.len()),
        bytes(decoded),
    );
    checks.body.push_str(&format!(
        "        store8(output + {}, u8(255)).\n",
        decoded.len()
    ));
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(0), output, usize({}))",
            bytes(encoded),
            decoded.len()
        ),
        decoded.len(),
    );
    checks.expect(format!("load8(output + {})", decoded.len()), "u8(255)");
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(0), output, usize({}))",
            bytes(encoded),
            decoded.len() - 1
        ),
        -28,
    );
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(0), output, usize(0))",
            bytes("\"\"")
        ),
        0,
    );
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(0), output, usize(0))",
            bytes("\"x\"")
        ),
        -28,
    );
    checks.expect(
        format!(
            "JsonDecodeString({}, usize(2), output, usize(1))",
            bytes("xx\"A\"junk")
        ),
        1,
    );
    for input in [
        "\"a\\x\"",
        "\"a",
        "\"\\uD800\"",
        "\"\\uDC00\"",
        "\"\n\"",
        "x",
        "",
    ] {
        checks.expect(
            format!(
                "JsonDecodeString({}, usize(0), output, usize(128))",
                bytes(input)
            ),
            -22,
        );
    }
    checks.expect(
        "JsonDecodeString(bytes(\"\"), usize(1), output, usize(128))",
        -22,
    );
    let controls: String = (0..32).map(char::from).collect();
    let value = format!("{controls}\"\\/é雪😀");
    let mut expected = String::from("\"");
    for code in 0..32 {
        write!(expected, "\\u{code:04x}").unwrap();
    }
    expected.push_str("\\\"\\\\/é雪😀\"");
    checks.body.push_str(&format!(
        "        store8(output + {}, u8(255)).\n",
        expected.len()
    ));
    checks.expect(
        format!(
            "JsonWriteString({}, output, usize({}))",
            bytes(&value),
            expected.len()
        ),
        expected.len(),
    );
    checks.expect(
        format!("bytes_at(output, usize({}))", expected.len()),
        bytes(&expected),
    );
    checks.expect(format!("load8(output + {})", expected.len()), "u8(255)");
    checks.expect(
        format!(
            "JsonWriteString({}, output, usize({}))",
            bytes(&value),
            expected.len() - 1
        ),
        -28,
    );
    for capacity in [0, 1] {
        checks.expect(
            format!("JsonWriteString(bytes(\"\"), output, usize({capacity}))"),
            -28,
        );
    }
    checks.expect("JsonWriteString(bytes(\"\"), output, usize(2))", 2);
    checks.expect("bytes_at(output, usize(2))", bytes("\"\""));
    for (value, capacity) in [("x", 2), ("\0", 6), ("\"", 3), ("😀", 5)] {
        checks
            .body
            .push_str(&format!("        store8(output + {capacity}, u8(255)).\n"));
        checks.expect(
            format!(
                "JsonWriteString({}, output, usize({capacity}))",
                bytes(value)
            ),
            -28,
        );
        checks.expect(format!("load8(output + {capacity})"), "u8(255)");
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
        let input = format!("bytes_at(buffer, usize({}))", quoted.len());
        checks.expect(format!("JsonStringEnd({input}, usize(0))"), -22);
        checks.expect(format!("JsonValidate({input})"), "false");
        checks.expect(
            format!("JsonDecodeString({input}, usize(0), output, usize(128))"),
            -22,
        );
        let raw = format!("bytes_at(buffer + 1, usize({}))", invalid.len());
        checks.expect(format!("JsonWriteString({raw}, output, usize(128))"), -22);
    }
    // The exact legal boundaries adjacent to overlongs/surrogates/out-of-range values.
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
        let quoted = format!("\"{valid}\"");
        checks.expect(
            format!(
                "JsonDecodeString({}, usize(0), output, usize(4))",
                bytes(&quoted)
            ),
            valid.len(),
        );
        checks.expect(
            format!("bytes_at(output, usize({}))", valid.len()),
            bytes(valid),
        );
        checks.expect(
            format!("JsonWriteString({}, output, usize(8))", bytes(valid)),
            quoted.len(),
        );
        checks.expect(
            format!("bytes_at(output, usize({}))", quoted.len()),
            bytes(&quoted),
        );
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}
