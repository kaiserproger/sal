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
            "sal-native-warehouse-codec-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&path).expect("fixture directory");
        let library =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../apps/warehouse/codec.sal");
        std::fs::copy(&library, path.join("codec.sal")).expect("copy real warehouse codec");
        Self(path)
    }

    fn execute(&self, checks: &Checks) {
        let source = format!(
            "use \"codec.sal\".\nuse \"std/bytes.sal\".\nuse \"std/linux/memory.sal\".\n\
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
            .expect("compile warehouse codec fixture");
        success(&build);
        let mut child = Running(
            Command::new(self.0.join("out/case"))
                .stdout(Stdio::null())
                .stderr(Stdio::null())
                .spawn()
                .expect("run native warehouse codec fixture"),
        );
        let deadline = Instant::now() + Duration::from_secs(15);
        loop {
            if let Some(status) = child.0.try_wait().expect("native status") {
                assert!(
                    status.success(),
                    "native warehouse codec result {status}; checks (exit code, expression): {:?}\n{source}",
                    checks.expressions
                );
                break;
            }
            assert!(
                Instant::now() < deadline,
                "native warehouse codec fixture timed out\n{source}"
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
        ));
    }
    fn finish_memory(&mut self) {
        self.expect("LinuxUnmapMemory(buffer, usize(4096))", 0);
    }
    fn request(&mut self, var: &str, body: &str, needs_codes: bool, capacity: usize) {
        let needs = if needs_codes { "true" } else { "false" };
        writeln!(
            self.body,
            "        let {var} = WarehouseDecodeRequest(bytes({}), {needs}, buffer, usize({capacity})).",
            text(body),
        )
        .unwrap();
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

#[test]
fn reserve_decodes_ids_codes_orders_and_defaults() {
    let mut checks = Checks::default();
    checks.memory();
    // IDs, defaults and counts are consumer-visible decode results.
    checks.request(
        "r0",
        "{\"warehouse_id\":1,\"codes\":[\"RED-M\"]}",
        true,
        4096,
    );
    checks.expect("r0.status", 0);
    checks.expect("r0.warehouse_id", 1);
    checks.expect("r0.code_count", 1);
    // Codes may precede the ID without moving the payload.
    checks.request("r1", "{\"codes\":[\"A\"],\"warehouse_id\":7}", true, 4096);
    checks.expect("r1.status", 0);
    checks.expect("r1.warehouse_id", 7);
    checks.expect("r1.code_count", 1);
    // warehouse_id is optional for reserve/release and defaults to 1.
    checks.request("r2", "{\"codes\":[\"X\"]}", true, 4096);
    checks.expect("r2.status", 0);
    checks.expect("r2.warehouse_id", 1);
    checks.expect("r2.code_count", 1);
    // Misspelled IDs are unknown fields; the default still applies.
    checks.request("r3", "{\"warehouse_ids\":5,\"codes\":[\"A\"]}", true, 4096);
    checks.expect("r3.status", 0);
    checks.expect("r3.warehouse_id", 1);
    // Escaped field names match after decoding, in any order.
    checks.request(
        "r4",
        "{\"c\\u006fdes\":[\"Z\"],\"wareh\\u006fuse_id\":4}",
        true,
        4096,
    );
    checks.expect("r4.status", 0);
    checks.expect("r4.warehouse_id", 4);
    checks.expect("r4.code_count", 1);
    // Unicode, quotes, backslashes and slashes decode into the payload.
    checks.request(
        "r5",
        "{\"warehouse_id\":2,\"codes\":[\"é雪😀\",\"a\\\"b\\\\c/d\"]}",
        true,
        4096,
    );
    checks.expect("r5.status", 0);
    checks.expect("r5.code_count", 2);
    // Unknown fields are validated, then ignored, even when deeply nested.
    checks.request(
        "r6",
        "{\"warehouse_id\":1,\"extra\":{\"deep\":[1,2,null]},\"codes\":[\"A\"],\"n\":null,\"s\":\"x\"}",
        true,
        4096,
    );
    checks.expect("r6.status", 0);
    checks.expect("r6.code_count", 1);
    // Python-style `{"warehouse_id": 2, "codes": [...]}` spaces after commas.
    checks.request(
        "w0",
        "{\"warehouse_id\": 2, \"codes\": [\"RED-M\"]}",
        true,
        4096,
    );
    checks.expect("w0.status", 0);
    checks.expect("w0.warehouse_id", 2);
    checks.expect("w0.code_count", 1);
    // Whitespace everywhere: newlines and tabs around every separator.
    checks.request(
        "w1",
        "{\n\t\"codes\"\t:\t[ \"A\" , \"B\" ] ,\n\t\"warehouse_id\"\t:\t1\n}",
        true,
        4096,
    );
    checks.expect("w1.status", 0);
    checks.expect("w1.warehouse_id", 1);
    checks.expect("w1.code_count", 2);
    // Prefix-sharing codes remain distinct after decoding.
    checks.request("distinct", "{\"codes\":[\"AB\",\"A\"]}", true, 4096);
    checks.expect("distinct.status", 0);
    checks.expect("distinct.code_count", 2);
    // The documented 64-code upper bound succeeds.
    let mut array = String::from("{\"warehouse_id\":3,\"codes\":[");
    for index in 0..64 {
        if index > 0 {
            array.push(',');
        }
        write!(array, "\"K{index}\"").unwrap();
    }
    array.push_str("]}");
    checks.request("r8", &array, true, 4096);
    checks.expect("r8.status", 0);
    checks.expect("r8.code_count", 64);
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn stock_requires_id_and_ignores_codes() {
    let mut checks = Checks::default();
    checks.memory();
    // Stock carries only the warehouse parameter.
    checks.request("s0", "{\"warehouse_id\":9}", false, 4096);
    checks.expect("s0.status", 0);
    checks.expect("s0.warehouse_id", 9);
    checks.expect("s0.code_count", 0);
    // In stock mode codes are an ordinary unknown field: validated, ignored.
    checks.request("s1", "{\"warehouse_id\":9,\"codes\":[\"X\"]}", false, 4096);
    checks.expect("s1.status", 0);
    checks.expect("s1.code_count", 0);
    // The largest supported ID must survive decoding exactly.
    checks.request("s2", "{\"warehouse_id\":9223372036854775807}", false, 4096);
    checks.expect("s2.status", 0);
    checks.expect("s2.warehouse_id", 9223372036854775807_i64);
    // Stock without an ID, or with a malformed ID/codes value, is rejected.
    for (index, body) in [
        "{}",
        "{\"codes\":[\"X\"]}",
        "{\"warehouse_id\":null}",
        "{\"warehouse_id\":1,\"codes\":[}}",
    ]
    .iter()
    .enumerate()
    {
        let var = format!("bad{index}");
        checks.request(&var, body, false, 4096);
        checks.expect(format!("{var}.status"), 400);
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn malformed_bodies_are_400() {
    let mut checks = Checks::default();
    checks.memory();
    let mut bodies: Vec<String> = vec![
        "",
        " ",
        "{",
        "}",
        "[]",
        "[1]",
        "\"x\"",
        "1",
        "true",
        "null",
        "nul",
        "{,}",
        "{\"a\":1,}",
        "{\"warehouse_id\"}",
        "{\"warehouse_id\":1,}",
        "{\"warehouse_id\":1 \"codes\":[\"A\"]}",
        "{\"warehouse_id\";1,\"codes\":[\"A\"]}",
        "{}",
        "{\"warehouse_id\":1}",
        "{\"codes\":[]}",
        "{\"warehouse_id\":1,\"codes\":[]}",
        "{\"codes\":[\"\"]}",
        "{\"codes\":[\"A\",\"\"]}",
        "{\"warehouse_id\":1,\"warehouse_id\":2,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":1,\"wareh\\u006fuse_id\":2,\"codes\":[\"A\"]}",
        "{\"codes\":[\"A\"],\"codes\":[\"B\"],\"warehouse_id\":1}",
        "{\"c\\u006fdes\":[\"A\"],\"codes\":[\"B\"],\"warehouse_id\":1}",
        "{\"codes\":[\"A\",\"A\"],\"warehouse_id\":1}",
        "{\"codes\":[\"A\",\"\\u0041\"],\"warehouse_id\":1}",
        "{\"codes\":[\"\\u00e9\",\"é\"],\"warehouse_id\":1}",
        "{\"codes\":[\"AB\",\"A\",\"AB\"],\"warehouse_id\":1}",
        "{\"warehouse_id\":null,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":true,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":\"1\",\"codes\":[\"A\"]}",
        "{\"warehouse_id\":-5,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":0,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":1.5,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":1e2,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":01,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":+1,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":9223372036854775808,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":99999999999999999999999999,\"codes\":[\"A\"]}",
        "{\"warehouse_id\":[1],\"codes\":[\"A\"]}",
        "{\"warehouse_id\":{\"v\":1},\"codes\":[\"A\"]}",
        "{\"warehouse_id\":1,\"codes\":\"A\"}",
        "{\"warehouse_id\":1,\"codes\":null}",
        "{\"warehouse_id\":1,\"codes\":[1]}",
        "{\"warehouse_id\":1,\"codes\":[null]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\",1]}",
        "{\"warehouse_id\":1,\"codes\":[[\"A\"]]}",
        "{\"warehouse_id\":1,\"codes\":[{\"k\":\"A\"}]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\",]}",
        "{\"warehouse_id\":1,\"codes\":[,\"A\"]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\\u0000B\"]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\nB\"]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\"],\"x\":{\"a\":}}",
        "{\"warehouse_id\":1,\"codes\":[\"A\"],\"x\":[1,]}",
        "{\"warehouse_id\":1,\"codes\":[\"A\"],\"x\":tru}",
        "{\"warehouse_id\":1,\"codes\":[\"A\"]}x",
        "{\"warehouse_id\":1,\"codes\":[\"A\"]}{}",
        "{\"warehouse_id\":1,\"codes\":[\"A\"]]",
        "{\"warehouse_id\":1,\"codes\":[\"A\"]",
    ]
    .into_iter()
    .map(String::from)
    .collect();
    bodies.push(format!(
        "{{\"warehouse_id\":1,\"codes\":[\"A\"],\"x\":{} depths {}}}",
        "[".repeat(100),
        "]".repeat(100)
    ));
    for (index, body) in bodies.iter().enumerate() {
        let var = format!("m{index}");
        checks.request(&var, body, true, 4096);
        checks.expect(format!("{var}.status"), 400);
    }
    checks.finish_memory();
    Fixture::new().execute(&checks);
}

#[test]
fn limits_are_413_with_explicit_edges() {
    let mut checks = Checks::default();
    checks.memory();
    // 65 codes exceed the 64-code bound; the array below is the same shape.
    let mut over = String::from("{\"warehouse_id\":1,\"codes\":[");
    for index in 0..65 {
        if index > 0 {
            over.push(',');
        }
        write!(over, "\"C{index}\"").unwrap();
    }
    over.push_str("]}");
    checks.request("l0", &over, true, 4096);
    checks.expect("l0.status", 413);
    // A 129-byte decoded code exceeds the 128-byte bound.
    let long129 = "Q".repeat(129);
    let body129 = format!("{{\"warehouse_id\":1,\"codes\":[\"{long129}\"]}}");
    checks.request("l1", &body129, true, 4096);
    checks.expect("l1.status", 413);
    // A 128-byte code is the exact upper edge and succeeds.
    let long128 = "Q".repeat(128);
    let body128 = format!("{{\"warehouse_id\":1,\"codes\":[\"{long128}\"]}}");
    checks.request("l2", &body128, true, 4096);
    checks.expect("l2.status", 0);
    checks.expect("l2.code_count", 1);
    // Even the serialized payload cannot fit these caller buffers.
    checks.request("small", &body128, true, 64);
    checks.expect("small.status", 413);
    checks.request("empty", "{\"codes\":[\"A\"]}", true, 0);
    checks.expect("empty.status", 413);
    // Bodies are built in SAL so the 65536-byte boundary needs no giant literal.
    checks.body.push_str(concat!(
        "        let area_map = LinuxMapMemory(usize(131072)).\n",
        "        if area_map < 0:\n            return 255.\n",
        "        let area = usize(area_map).\n",
        "        let copied = BytesCopy(area, usize(131072), bytes(\"{\\\"warehouse_id\\\":1,\\\"codes\\\":[\\\"A\\\"]}\")).\n",
        "        let mut total = copied.\n",
        "        while total < 65537:\n",
        "            store8(area + usize(total), u8(32)).\n",
        "            set total = total + 1.\n",
        "        let over_sized = WarehouseDecodeRequest(bytes_at(area, usize(65537)), true, buffer, usize(4096)).\n",
    ));
    checks.expect("over_sized.status", 413);
    checks.expect(
        "WarehouseDecodeRequest(bytes_at(area, usize(65536)), true, buffer, usize(4096)).status",
        0,
    );
    checks.expect(
        "WarehouseDecodeRequest(bytes_at(area, usize(65536)), true, buffer, usize(4096)).code_count",
        1,
    );
    checks.expect("LinuxUnmapMemory(area, usize(131072))", 0);
    checks.finish_memory();
    Fixture::new().execute(&checks);
}
