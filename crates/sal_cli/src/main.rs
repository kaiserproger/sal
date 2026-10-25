//! SAL CLI: deterministic checking, Anglish translation, native artifacts.
//!
//! CONTRACT (implemented):
//! - `sal check <file.sal> [--strict]`: parse, registry, type/body/architecture/
//!   effect checks. Print each diagnostic via
//!   sal_syntax::format_diagnostic + source. Summary `N error(s), M warning(s)`.
//!   Exit 1 if any Error, or any Warning with --strict; else print `ok` line.
//! - `sal emit-rust <file.sal> --out <dir>`: on check errors exit 1 without
//!   writing; else write EmittedFiles under <dir>, print each path.
//! - `sal verify <file.sal> --rust <dir> [--strict]`: check + scan <dir>
//!   recursively for `.rs` files; per file extract `sal:module NAME` marker
//!   (first line comment containing `sal:module`, name = trailing token) and
//!   `use` paths (line-based: strip `pub`, take path before `;`, cut at `{`
//!   for `use a::{b}` prefixes, cut ` as x` suffixes; skip non-`use` lines).
//!   Markerless files are reported individually as VERIFY003 warnings (they
//!   fail the run with --strict via the shared exit policy). Zero `.rs` files
//!   under the scanned path is VERIFY001 (error); `.rs` files present but zero
//!   markers is VERIFY002 (error). Unknown marker modules delegate to sal_ir
//!   ARCH201; the CLI never swallows them. Print, same exit policy as check.
//! - `sal run-ang <file.ang> [--port-over N] [--strict]`: translate to SAL on
//!   stdout; diagnostics on stderr; fail on errors or strict warnings.
//! - `sal build-exe <file.sal|--ang file.ang> --out <dir> [--strict]` defaults
//!   to Linux x86-64 native assembly plus as/ld. Unsupported native behavior
//!   fails closed. `--backend rust-std` explicitly selects the legacy emitter.
//! - `sal build-lib <file.sal|--ang file.ang> --out <dir> [--strict]` produces
//!   native archive and C header from checked scalar C exports.

mod anglish;
mod native_build;
mod server_frontend;
mod sources;

use sal_backend_rust::emit_rust;
use sal_ir::{
    build, check_architecture, check_effects, check_types, verify_rust_imports, RustFile,
};
use sal_syntax::{format_diagnostic, Diagnostic, Severity, Span};
use std::path::{Path, PathBuf};

fn usage() -> &'static str {
    "usage:\n  sal check <file.sal> [--strict]\n  sal emit-rust <file.sal> --out <dir> [--strict]\n  sal verify <file.sal> --rust <dir> [--strict]\n  sal run-ang <file.ang> [--port-over N] [--model-command PROGRAM [--model-arg ARG]...] [--strict]\n  sal build-exe <file.sal|--ang file.ang> --out <dir> [--link <object-or-archive>]... [--model-command PROGRAM [--model-arg ARG]...] [--backend native|rust-std] [--strict]\n  sal build-lib <file.sal|--ang file.ang> --out <dir> [--model-command PROGRAM [--model-arg ARG]...] [--strict]"
}

fn bad_args(msg: String) -> ! {
    eprintln!("sal: {}", msg);
    eprintln!("{}", usage());
    std::process::exit(2);
}

fn missing(msg: String) -> ! {
    eprintln!("sal: {}", msg);
    std::process::exit(2);
}

fn read_source(path: &str) -> String {
    match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => missing(format!("cannot read '{}': {}", path, e)),
    }
}

/// Load diagnostics, registry, and semantic checks in deterministic order.
fn run_checks(source: &sources::Sources) -> (sal_ir::Ir, Vec<Diagnostic>) {
    let mut diags = source.diagnostics.clone();
    let (ir, build_diags) = build(&source.file);
    diags.extend(build_diags);
    diags.extend(check_types(&ir));
    diags.extend(check_architecture(&ir));
    diags.extend(check_effects(&ir));
    diags.extend(sal_ir::check_bodies(&ir));
    (ir, diags)
}

fn count_severities(diags: &[Diagnostic]) -> (usize, usize) {
    let mut errors = 0usize;
    let mut warnings = 0usize;
    for d in diags {
        match d.severity {
            Severity::Error => errors += 1,
            Severity::Warning => warnings += 1,
            Severity::Info => {}
        }
    }
    (errors, warnings)
}

fn has_failures(diags: &[Diagnostic], strict: bool) -> bool {
    let (errors, warnings) = count_severities(diags);
    errors > 0 || (strict && warnings > 0)
}

fn report(diags: &[Diagnostic], source: &sources::Sources) {
    for d in diags {
        println!("{}", source.format(d));
    }
    let (errors, warnings) = count_severities(diags);
    println!("{} error(s), {} warning(s)", errors, warnings);
}

fn parse_check_args(rest: &[String]) -> (String, bool) {
    let mut file: Option<String> = None;
    let mut strict = false;
    for arg in rest {
        let a: &str = arg.as_str();
        if a == "--strict" {
            strict = true;
        } else if a.starts_with('-') {
            bad_args(format!("unexpected flag '{}' for check", a));
        } else if file.is_none() {
            file = Some(a.to_string());
        } else {
            bad_args("too many positional arguments for check".to_string());
        }
    }
    match file {
        Some(f) => (f, strict),
        None => bad_args("missing <file.sal>".to_string()),
    }
}

fn parse_emit_args(rest: &[String]) -> (String, String, bool) {
    let mut file: Option<String> = None;
    let mut out: Option<String> = None;
    let mut strict = false;
    let mut i = 0usize;
    while i < rest.len() {
        let a: &str = match rest.get(i) {
            Some(v) => v.as_str(),
            None => break,
        };
        if a == "--strict" {
            strict = true;
        } else if a == "--out" {
            let v = match rest.get(i + 1) {
                Some(v) => v.as_str().to_string(),
                None => bad_args("flag --out needs a value".to_string()),
            };
            if v.is_empty() {
                bad_args("flag --out needs a non-empty value".to_string());
            }
            out = Some(v);
            i += 1;
        } else if let Some(v) = a.strip_prefix("--out=") {
            let v = v.to_string();
            if v.is_empty() {
                bad_args("flag --out needs a non-empty value".to_string());
            }
            out = Some(v);
        } else if a.starts_with('-') {
            bad_args(format!("unexpected flag '{}' for emit-rust", a));
        } else if file.is_none() {
            file = Some(a.to_string());
        } else {
            bad_args("too many positional arguments for emit-rust".to_string());
        }
        i += 1;
    }
    let file = match file {
        Some(f) => f,
        None => bad_args("missing <file.sal>".to_string()),
    };
    let out = match out {
        Some(o) => o,
        None => bad_args("missing --out <dir>".to_string()),
    };
    (file, out, strict)
}

fn parse_verify_args(rest: &[String]) -> (String, String, bool) {
    let mut file: Option<String> = None;
    let mut rust_dir: Option<String> = None;
    let mut strict = false;
    let mut i = 0usize;
    while i < rest.len() {
        let a: &str = match rest.get(i) {
            Some(v) => v.as_str(),
            None => break,
        };
        if a == "--strict" {
            strict = true;
        } else if a == "--rust" {
            let v = match rest.get(i + 1) {
                Some(v) => v.as_str().to_string(),
                None => bad_args("flag --rust needs a value".to_string()),
            };
            if v.is_empty() {
                bad_args("flag --rust needs a non-empty value".to_string());
            }
            rust_dir = Some(v);
            i += 1;
        } else if let Some(v) = a.strip_prefix("--rust=") {
            let v = v.to_string();
            if v.is_empty() {
                bad_args("flag --rust needs a non-empty value".to_string());
            }
            rust_dir = Some(v);
        } else if a.starts_with('-') {
            bad_args(format!("unexpected flag '{}' for verify", a));
        } else if file.is_none() {
            file = Some(a.to_string());
        } else {
            bad_args("too many positional arguments for verify".to_string());
        }
        i += 1;
    }
    let file = match file {
        Some(f) => f,
        None => bad_args("missing <file.sal>".to_string()),
    };
    let rust_dir = match rust_dir {
        Some(o) => o,
        None => bad_args("missing --rust <dir>".to_string()),
    };
    (file, rust_dir, strict)
}

fn cmd_check(rest: &[String]) {
    let (file, strict) = parse_check_args(rest);
    let source = sources::Sources::load(&file);
    let (_ir, diags) = run_checks(&source);
    report(&diags, &source);
    if has_failures(&diags, strict) {
        std::process::exit(1);
    }
    println!("ok: {} checks passed", file);
}

fn cmd_emit(rest: &[String]) {
    let (file, out_dir, strict) = parse_emit_args(rest);
    let source = sources::Sources::load(&file);
    let (ir, diags) = run_checks(&source);
    report(&diags, &source);
    if has_failures(&diags, strict) {
        std::process::exit(1);
    }
    let out_root = Path::new(&out_dir);
    for emitted in emit_rust(&ir) {
        let dest = out_root.join(&emitted.path);
        if let Some(parent) = dest.parent() {
            if !parent.as_os_str().is_empty() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!("sal: cannot create directory '{}': {}", parent.display(), e);
                    std::process::exit(1);
                }
            }
        }
        if let Err(e) = std::fs::write(&dest, &emitted.content) {
            eprintln!("sal: cannot write '{}': {}", dest.display(), e);
            std::process::exit(1);
        }
        println!("{}", dest.display());
    }
}
fn parse_run_en_args(rest: &[String]) -> (String, Option<String>, bool, anglish::Model) {
    let mut file: Option<String> = None;
    let mut port_over: Option<String> = None;
    let mut strict = false;
    let mut model = anglish::Model::default();
    let mut i = 0usize;
    while i < rest.len() {
        let a: &str = match rest.get(i) {
            Some(v) => v.as_str(),
            None => break,
        };
        if a == "--strict" {
            strict = true;
        } else if a == "--model-command" {
            let value = rest
                .get(i + 1)
                .unwrap_or_else(|| bad_args("--model-command needs an executable".into()));
            model.program(value.clone());
            i += 1;
        } else if a == "--model-arg" {
            let value = rest
                .get(i + 1)
                .unwrap_or_else(|| bad_args("--model-arg needs an argument".into()));
            model.argument(value.clone());
            i += 1;
        } else if a == "--port-over" {
            let v = match rest.get(i + 1) {
                Some(v) => v.as_str().to_string(),
                None => bad_args("flag --port-over needs a value".to_string()),
            };
            port_over = Some(parse_port(v));
            i += 1;
        } else if let Some(v) = a.strip_prefix("--port-over=") {
            if v.is_empty() {
                bad_args("flag --port-over needs a non-empty value".to_string());
            }
            port_over = Some(parse_port(v.to_string()));
        } else if a.starts_with('-') {
            bad_args(format!("unexpected flag '{}' for run-ang", a));
        } else if file.is_none() {
            file = Some(a.to_string());
        } else {
            bad_args("too many positional arguments for run-ang".to_string());
        }
        i += 1;
    }
    model.validate();
    match file {
        Some(f) => (f, port_over, strict, model),
        None => bad_args("missing <file.ang>".to_string()),
    }
}

fn parse_port(v: String) -> String {
    match v.parse::<u32>() {
        Ok(n) if (1..=65535).contains(&n) => n.to_string(),
        _ => bad_args(format!(
            "invalid port '{}' for --port-over (want 1..=65535)",
            v
        )),
    }
}

/// Replace the port digits on the single `listens on port` line.
fn apply_port_over(level_b: &str, port: &str) -> String {
    let mut lines: Vec<String> = Vec::new();
    for line in level_b.lines() {
        if line.contains("listens on port") {
            lines.push(replace_port_digits(line, port));
        } else {
            lines.push(line.to_string());
        }
    }
    let mut out = lines.join("\n");
    if level_b.ends_with('\n') {
        out.push('\n');
    }
    out
}

fn replace_port_digits(line: &str, port: &str) -> String {
    let marker = "listens on port";
    let search_from = match line.find(marker) {
        Some(idx) => idx + marker.len(),
        None => return line.to_string(),
    };
    let bytes = line.as_bytes();
    let mut i = search_from;
    while i < line.len() && !bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i >= line.len() {
        return line.to_string();
    }
    let mut end = i;
    while end < line.len() && bytes[end].is_ascii_digit() {
        end += 1;
    }
    format!("{}{}{}", &line[..i], port, &line[end..])
}

fn cmd_run_en(rest: &[String]) {
    let (file, port_over, strict, model) = parse_run_en_args(rest);
    let en_source = read_source(&file);
    let (mut level_b, sem_diags) = model.translate(&en_source).unwrap_or_else(|error| {
        eprintln!("sal: {error}");
        std::process::exit(1);
    });
    if let Some(port) = port_over {
        let count = level_b
            .lines()
            .filter(|l| l.contains("listens on port"))
            .count();
        if count != 1 {
            let d = Diagnostic {
                code: "E9004",
                severity: Severity::Error,
                message: format!(
                    "--port-over {} needs exactly one `listens on port` line, found {}",
                    port, count
                ),
                span: Span::single(1, 1),
                suggestion: None,
            };
            eprintln!("{}", format_diagnostic(&d, &level_b));
            std::process::exit(1);
        }
        level_b = apply_port_over(&level_b, &port);
    }
    // stdout is compilable SAL, so omp and shell pipelines can consume it.
    for diagnostic in &sem_diags {
        eprintln!("{}", format_diagnostic(diagnostic, &en_source));
    }
    if has_failures(&sem_diags, strict) {
        std::process::exit(1);
    }
    let source = sources::Sources::from_text(Path::new(&file), level_b);
    let (_, diagnostics) = run_checks(&source);
    for diagnostic in &diagnostics {
        eprintln!("{}", source.format(diagnostic));
    }
    if has_failures(&diagnostics, strict) {
        std::process::exit(1);
    }
    if model.enabled() {
        eprintln!(
            "sal: model proposal passed structural checks; preservation of intent is not proved"
        );
    }
    let level_b = source.root_text();
    print!("{}", level_b);
    if !level_b.ends_with('\n') {
        println!();
    }
}

fn binary_stem(path: &str) -> String {
    match Path::new(path).file_stem().and_then(|s| s.to_str()) {
        Some(s) if !s.is_empty() => s.to_string(),
        _ => bad_args(format!("cannot derive binary name from '{}'", path)),
    }
}

/// First-line comment containing `sal:module`; name = trailing token.
fn extract_module(content: &str) -> Option<String> {
    let line = content.lines().next()?;
    let idx = line.find("sal:module")?;
    let before = &line[..idx];
    let trimmed = line.trim_start();
    let is_comment = before.contains("//")
        || trimmed.starts_with("//")
        || trimmed.starts_with('#')
        || trimmed.starts_with("/*")
        || trimmed.starts_with('*');
    if !is_comment {
        return None;
    }
    let tail = line.trim_end();
    let token = tail.split_whitespace().next_back()?;
    let name = token.trim_matches(['.', ',', ';', ':', '*', '/', '"', '\'']);
    if name.is_empty() {
        return None;
    }
    Some(name.to_string())
}

/// Line-based `use` path extraction: strip `pub` (+ optional scope), take path
/// before `;`, cut at `{` for `use a::{b}` prefixes, cut ` as x` suffixes.
fn extract_imports(content: &str) -> Vec<String> {
    let mut imports = Vec::new();
    for raw in content.lines() {
        let mut line: &str = raw.trim();
        if line.starts_with("//") || line.starts_with('#') || line.starts_with('*') {
            continue;
        }
        if line.starts_with("pub") && line[3..].starts_with([' ', '\t', '(']) {
            line = line[3..].trim_start();
            if line.starts_with('(') {
                match line.find(')') {
                    Some(end) => line = line[end + 1..].trim_start(),
                    None => continue,
                }
            }
        }
        if !(line.starts_with("use ") || line.starts_with("use\t")) {
            continue;
        }
        let rest = line["use ".len()..].trim_start();
        let mut path = match rest.find(';') {
            Some(i) => &rest[..i],
            None => rest,
        };
        path = path.trim();
        if let Some(i) = path.find('{') {
            path = path[..i].trim();
        }
        if let Some(i) = path.find(" as ") {
            path = path[..i].trim();
        } else if let Some(i) = path.find(" as\t") {
            path = path[..i].trim();
        }
        path = path.trim_end_matches([':', ' ', '\t']);
        if path.is_empty() {
            continue;
        }
        imports.push(path.to_string());
    }
    imports
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let ftype = match entry.file_type() {
            Ok(t) => t,
            Err(_) => continue,
        };
        if ftype.is_symlink() {
            continue;
        }
        if ftype.is_dir() {
            collect_rs_files(&entry.path(), out);
        } else if ftype.is_file() {
            let p = entry.path();
            if p.extension().and_then(|s| s.to_str()) == Some("rs") {
                out.push(p);
            }
        }
    }
}

fn cmd_verify(rest: &[String]) {
    let (file, rust_dir, strict) = parse_verify_args(rest);
    let source = sources::Sources::load(&file);
    let (ir, mut diags) = run_checks(&source);
    let rust_path = Path::new(&rust_dir);
    let mut rs_paths: Vec<PathBuf> = Vec::new();
    if rust_path.is_file() {
        rs_paths.push(rust_path.to_path_buf());
    } else if rust_path.is_dir() {
        collect_rs_files(rust_path, &mut rs_paths);
        rs_paths.sort();
    } else {
        missing(format!(
            "cannot scan '{}': no such file or directory",
            rust_dir
        ));
    }
    let mut rfiles: Vec<RustFile> = Vec::new();
    let mut unmarked: Vec<PathBuf> = Vec::new();
    let mut rs_count = 0usize;
    for p in &rs_paths {
        if p.extension().and_then(|s| s.to_str()) != Some("rs") {
            continue;
        }
        rs_count += 1;
        let content = match std::fs::read_to_string(p) {
            Ok(c) => c,
            Err(_) => continue,
        };
        match extract_module(&content) {
            Some(module) => rfiles.push(RustFile {
                module,
                imports: extract_imports(&content),
            }),
            None => unmarked.push(p.clone()),
        }
    }
    if rs_count == 0 {
        diags.push(Diagnostic {
            code: "VERIFY001",
            severity: Severity::Error,
            message: format!("no .rs files found under '{}'", rust_dir),
            span: Span::single(1, 1),
            suggestion: None,
        });
    } else {
        if rfiles.is_empty() {
            diags.push(Diagnostic {
                code: "VERIFY002",
                severity: Severity::Error,
                message: format!(
                    "found {} .rs file(s) under '{}' but none carries a `sal:module` marker",
                    rs_count, rust_dir
                ),
                span: Span::single(1, 1),
                suggestion: None,
            });
        }
        for p in &unmarked {
            diags.push(Diagnostic {
                code: "VERIFY003",
                severity: Severity::Warning,
                message: format!(
                    "'{}' has no `sal:module` marker; skipping Rust import checks for this file",
                    p.display()
                ),
                span: Span::single(1, 1),
                suggestion: None,
            });
        }
        diags.extend(verify_rust_imports(&ir, &rfiles));
    }
    report(&diags, &source);
    if has_failures(&diags, strict) {
        std::process::exit(1);
    }
    println!("ok: {} checks passed", file);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cmd: &str = match args.first() {
        Some(c) => c.as_str(),
        None => bad_args("missing command".to_string()),
    };
    let rest: &[String] = match args.get(1..) {
        Some(r) => r,
        None => &[],
    };
    match cmd {
        "check" => cmd_check(rest),
        "emit-rust" => cmd_emit(rest),
        "verify" => cmd_verify(rest),
        "run-ang" => cmd_run_en(rest),
        "build-exe" => native_build::build(rest, false),
        "build-lib" => native_build::build(rest, true),
        "-h" | "--help" | "help" => println!("{}", usage()),
        _ => bad_args(format!("unknown command '{}'", cmd)),
    }
}
