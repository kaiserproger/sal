//! Integration tests for `sal verify` vacuous-pass hardening.
//!
//! Drives the built `sal` binary via `CARGO_BIN_EXE_sal`; std only. Paths are
//! hermetic: fixtures resolve relative to `CARGO_MANIFEST_DIR`.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn sal_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_sal"))
}

fn root_path(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../")
        .join(rel)
}

fn run_verify(sal: &Path, rust: &Path, strict: bool) -> Output {
    let mut cmd = Command::new(sal_bin());
    cmd.arg("verify").arg(sal).arg("--rust").arg(rust);
    if strict {
        cmd.arg("--strict");
    }
    cmd.output().expect("failed to run sal binary")
}

fn combined(out: &Output) -> String {
    format!(
        "{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

#[test]
fn ok_fixture_passes_and_prints_ok() {
    let sal = root_path("tests/verify_fixtures/ok/ok.sal");
    let rust = root_path("tests/verify_fixtures/ok/src");
    let out = run_verify(&sal, &rust, false);
    let text = combined(&out);
    assert!(out.status.success(), "ok fixture must exit 0:\n{text}");
    assert!(
        text.contains("ok"),
        "ok fixture must print ok line:\n{text}"
    );
}

#[test]
fn bad_fixture_trips_arch001() {
    let sal = root_path("tests/verify_fixtures/bad/bad.sal");
    let rust = root_path("tests/verify_fixtures/bad/src");
    let out = run_verify(&sal, &rust, false);
    let text = combined(&out);
    assert!(!out.status.success(), "bad fixture must fail:\n{text}");
    assert!(
        text.contains("ARCH001"),
        "bad fixture must mention ARCH001:\n{text}"
    );
}

#[test]
fn unmarked_warns_without_strict() {
    let sal = root_path("tests/verify_fixtures/unmarked/unmarked.sal");
    let rust = root_path("tests/verify_fixtures/unmarked/src");
    let out = run_verify(&sal, &rust, false);
    let text = combined(&out);
    assert!(
        out.status.success(),
        "unmarked without --strict must exit 0:\n{text}"
    );
    assert!(
        text.contains("VERIFY003"),
        "unmarked run must report VERIFY003:\n{text}"
    );
}

#[test]
fn unmarked_fails_with_strict() {
    let sal = root_path("tests/verify_fixtures/unmarked/unmarked.sal");
    let rust = root_path("tests/verify_fixtures/unmarked/src");
    let out = run_verify(&sal, &rust, true);
    let text = combined(&out);
    assert!(
        !out.status.success(),
        "unmarked with --strict must fail:\n{text}"
    );
}

#[test]
fn empty_fixture_trips_verify001() {
    let sal = root_path("tests/verify_fixtures/empty/empty.sal");
    let rust = root_path("tests/verify_fixtures/empty/src");
    let out = run_verify(&sal, &rust, false);
    let text = combined(&out);
    assert!(!out.status.success(), "empty fixture must fail:\n{text}");
    assert!(
        text.contains("VERIFY001"),
        "empty fixture must mention VERIFY001:\n{text}"
    );
}

#[test]
fn sal_check_failure_still_fails_verify() {
    let sal = root_path("examples/payments_bad.sal");
    let rust = root_path("tests/verify_fixtures/ok/src");
    let out = run_verify(&sal, &rust, false);
    let text = combined(&out);
    assert!(
        !out.status.success(),
        "payments_bad.sal must fail verify:\n{text}"
    );
}
