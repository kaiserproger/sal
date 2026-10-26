//! Native build driver: tools run at build time; the result imports no runtime.

use std::path::{Path, PathBuf};
use std::process::Command;

use sal_backend_native::{emit_native, NativeTarget};

use crate::{bad_args, binary_stem, has_failures, report, run_checks, sources::Sources};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Native,
    RustStd,
}

struct Args {
    source: String,
    out: PathBuf,
    strict: bool,
    backend: Backend,
    links: Vec<PathBuf>,
}

fn parse(rest: &[String], library: bool) -> Args {
    let mut source = None;
    let mut out = None;
    let mut strict = false;
    let mut backend = Backend::Native;
    let mut links = Vec::new();
    let mut args = rest.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--strict" => strict = true,
            "--out" => {
                let value = args
                    .next()
                    .filter(|value| !value.is_empty())
                    .unwrap_or_else(|| bad_args("--out needs a directory".into()));
                if out.replace(PathBuf::from(value)).is_some() {
                    bad_args("--out must be specified once".into());
                }
            }
            "--link" => {
                let value = args
                    .next()
                    .filter(|value| !value.is_empty())
                    .unwrap_or_else(|| bad_args("--link needs an object or archive".into()));
                links.push(Path::new(value).canonicalize().unwrap_or_else(|error| {
                    bad_args(format!("cannot resolve --link input '{value}': {error}"))
                }));
            }
            "--backend" => {
                backend = match args.next().map(String::as_str) {
                    Some("native") => Backend::Native,
                    Some("rust-std") if !library => Backend::RustStd,
                    _ => bad_args(
                        "backend must be native (or rust-std for explicit legacy executables)"
                            .into(),
                    ),
                };
            }
            value if value.starts_with('-') => bad_args(format!("unknown build flag '{value}'")),
            value => {
                if source.replace(value.to_owned()).is_some() {
                    bad_args("provide exactly one SAL input".into());
                }
            }
        }
    }
    if !links.is_empty() && (library || backend != Backend::Native) {
        bad_args("--link is only supported for native executables; archive consumers link foreign inputs themselves".into());
    }
    Args {
        source: source.unwrap_or_else(|| bad_args("missing <file.sal>".into())),
        out: out.unwrap_or_else(|| bad_args("missing --out <dir>".into())),
        strict,
        backend,
        links,
    }
}

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("sal: {message}");
    std::process::exit(1)
}

fn write(path: &Path, data: impl AsRef<[u8]>) {
    std::fs::write(path, data)
        .unwrap_or_else(|error| fail(format!("cannot write '{}': {error}", path.display())));
}

fn execute(tool: &str, args: impl IntoIterator<Item = impl AsRef<std::ffi::OsStr>>) {
    let output = Command::new(tool)
        .args(args)
        .output()
        .unwrap_or_else(|error| fail(format!("cannot run {tool}: {error}")));
    if !output.status.success() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
        fail(format!("{tool} failed with {}", output.status));
    }
}

pub fn build(rest: &[String], library: bool) {
    let args = parse(rest, library);
    let mut source = Sources::load(&args.source);
    if args.backend == Backend::Native && !library && !has_failures(&source.diagnostics, false) {
        match crate::server_frontend::lower(&source.file) {
            Ok(Some(generated)) => {
                // Original names were checked before consuming DSL declarations.
                source.file.items.retain(|item| {
                    !matches!(
                        item,
                        sal_syntax::Item::Server(_) | sal_syntax::Item::Route(_)
                    )
                });
                source.append_generated(generated);
            }
            Ok(None) => {}
            Err(errors) => source.diagnostics.extend(errors),
        }
    }
    let (ir, mut diagnostics) = run_checks(&source);
    if args.backend == Backend::RustStd {
        diagnostics.extend(sal_ir::check_exec(&ir));
    }
    report(&diagnostics, &source);
    if has_failures(&diagnostics, args.strict) {
        std::process::exit(1);
    }
    let stem = binary_stem(&args.source);
    match args.backend {
        Backend::Native => {
            if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
                fail("native backend currently targets Linux x86-64 only");
            }
            let target = if library {
                NativeTarget::StaticLibrary
            } else {
                NativeTarget::Executable
            };
            let program = match emit_native(&ir, target) {
                Ok(program) => program,
                Err(errors) => {
                    report(&errors, &source);
                    std::process::exit(1);
                }
            };
            std::fs::create_dir_all(&args.out)
                .unwrap_or_else(|error| fail(format!("cannot create output directory: {error}")));
            let assembly = args.out.join("main.s");
            let object = args.out.join("main.o");
            write(&assembly, program.assembly);
            execute(
                "as",
                [
                    "--64".as_ref(),
                    assembly.as_os_str(),
                    "-o".as_ref(),
                    object.as_os_str(),
                ],
            );
            let artifact = if library {
                args.out.join(format!("lib{stem}.a"))
            } else {
                args.out.join(&stem)
            };
            if library {
                // Replacing rather than appending guarantees no stale archive members.
                if artifact.exists() {
                    std::fs::remove_file(&artifact)
                        .unwrap_or_else(|error| fail(format!("cannot replace archive: {error}")));
                }
                execute(
                    "ar",
                    ["rcsD".as_ref(), artifact.as_os_str(), object.as_os_str()],
                );
                if let Some(header) = program.header {
                    write(&args.out.join(format!("{stem}.h")), header);
                }
            } else {
                execute(
                    "ld",
                    [
                        "-m".as_ref(),
                        "elf_x86_64".as_ref(),
                        "--build-id=none".as_ref(),
                        "-z".as_ref(),
                        "noexecstack".as_ref(),
                        "-o".as_ref(),
                        artifact.as_os_str(),
                        object.as_os_str(),
                    ]
                    .into_iter()
                    .chain(args.links.iter().map(|path| path.as_os_str())),
                );
            }
            println!("{}", artifact.display());
        }
        Backend::RustStd => {
            eprintln!("sal: explicit legacy rust-std backend; this artifact uses Rust stdlib");
            let program = match sal_backend_exec::emit_exec(&ir) {
                Ok(program) => program,
                Err(errors) => {
                    report(&errors, &source);
                    std::process::exit(1);
                }
            };
            std::fs::create_dir_all(&args.out)
                .unwrap_or_else(|error| fail(format!("cannot create output directory: {error}")));
            let source = args.out.join("main.rs");
            let artifact = args.out.join(&stem);
            write(&source, program.main_rs);
            execute(
                "rustc",
                [
                    "--edition".as_ref(),
                    "2021".as_ref(),
                    "-O".as_ref(),
                    source.as_os_str(),
                    "-o".as_ref(),
                    artifact.as_os_str(),
                ],
            );
            println!("{}", artifact.display());
        }
    }
}
