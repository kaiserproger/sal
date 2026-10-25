//! SAL executable backend: HTTP server + console programs, direct compilation, no agents.
//!
//! CONTRACT (do not change public signatures; implement bodies only):
//! - `emit_exec(ir) -> Result<ExecProgram, Vec<Diagnostic>>`: validates the
//!   executable subset and returns ONE self-contained Rust program text
//!   (`main.rs` content, std-only, no dependencies). Fails (Err) on any error
//!   diagnostic; warnings do not block.
//! - Executable subset (checked in sal_ir::check_exec, codes X1xx): TWO program
//!   kinds. Server program (any `server` or `route` present): exactly one
//!   `server NAME:` block; server has `listens on port N.` (1..=65535, X100);
//!   `speaks HTTP/1.` required (X101 if missing/other version). One or more
//!   `route NAME:` blocks; each has `handles METHOD PATH.` (METHOD GET only,
//!   X102; PATH starts with `/`, `:p` segments non-empty, X103) and
//!   `responds with ...` exactly one of: `Text.` | `"literal".` |
//!   `param NAME.` (X104 otherwise). `operation NAME:` blocks optional; only
//!   `returns Text.` + `responds with "lit".` hello-world form is executable
//!   (other operations ignored with W1xx warning, never an error).
//!   Console program (no servers AND no routes): exactly one hello-world
//!   `operation` (`returns Text.` + `responds with "lit".`; X107 when none,
//!   X108 when more than one operation total; non-hello operations ignored
//!   with W100, never an error).
//! - Character/Word/Text: primitives (Character -> char, Word/Text -> String).
//!   Route `:p` params are Text (any non-`/` chars incl. spaces via %20; Word
//!   params rejected at semfront E9006). Returned Text is written verbatim.
//! - Emitted server program: `std::net::TcpListener` on `127.0.0.1:N`, single-threaded
//!   accept loop, parses `METHOD /path VERSION` request line only. Incoming
//!   VERSION must be exactly `HTTP/1.0` or `HTTP/1.1`; anything else (HTTP/2,
//!   garbage) is malformed -> `400` with `bad request`, never a 200. Route match:
//!   literal segments equal, `:p` captures one segment (percent-decoded UTF-8,
//!   `+` stays `+`). Response: `HTTP/1.0 200 OK\r\ncontent-type:
//!   text/plain; charset=utf-8\r\ncontent-length: <bytes>\r\nconnection:
//!   close\r\n\r\n<body>`. Unknown route/method -> `404` with `not found` body.
//!   Binds/version fixed at compile time; N and routes baked in as literals.
//! - Emitted console program: `fn main() { println!("{}", "LIT"); }` where LIT
//!   is the hello-world operation's responds literal with Rust string escaping:
//!   `\` -> `\\`, `"` -> `\"`, newline -> `\n`, other control chars ->
//!   `\u{...}` (lowercase hex). Format-arg form (never bare `println!("LIT")`)
//!   so braces/JSON pass through verbatim. No TcpListener, no routes.
//!   Deterministic: operations scanned in name order, first hello-world wins.
//! - Operation bodies (typed `Stmt`/`Expr` AST on `OperationDecl.body`):
//!   console lowering only. `let [mut] NAME = EXPR;` binds a Rust `let`
//!   (`let mut` preserved); `set NAME = EXPR;` assigns `NAME = EXPR;`;
//!   `return "lit".` prints the literal via `println!("{}", "lit")` and returns
//!   (a lone `return "lit"` body emits the legacy one-line program byte-shape);
//!   `return VAR` prints the variable, other `return EXPR` prints the
//!   rendered expression; `if` lowers to a real `if`/`else`; call/effect
//!   statements lower to `{expr};`. Expressions: `Lit` -> escaped `"..."`,
//!   Int/Float/Bool literals, `Var` -> name, `len(x)` -> `x.len()`,
//!   `push(v, x)` -> `v.push(x)`, other calls -> `name(args)`, `a.b`,
//!   `a[i]`, `(left OP right)` for `+`/`-`/`*`/`/`/`%`/`<`/`<=`/`>`/`>=`/`==`/`!=`.
//!   `for`/`while` loops stay explicitly rejected with one B200 error each
//!   (never a panic); reserved native intrinsics (`bytes`, `byte`, `slice`,
//!   numeric conversions, `syscall`, `address`, `bytes_at`, `load8`, `store8`)
//!   are intentionally rejected as explicit B201 errors rather than lowered.
//! - Emitted code must compile under rustc stable with no deps and never panic
//!   on any input bytes (all reads bounded, all indexing guarded, UTF-8 lossy).

use sal_ir::{Ir, RespondsKind, RouteDecl, ServerDecl, TypeRef};

use sal_syntax::{BinOp, Expr, Severity, Span, Stmt};

#[cfg(test)]
mod c_abi_tests;

#[derive(Debug, Clone)]
pub struct ExecProgram {
    pub main_rs: String,
}

pub fn emit_exec(ir: &Ir) -> Result<ExecProgram, Vec<sal_syntax::Diagnostic>> {
    let mut diagnostics: Vec<sal_syntax::Diagnostic> = sal_ir::check_exec(ir);
    collect_c_feature_errors(ir, &mut diagnostics);
    let has_error: bool = diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == sal_ir::Severity::Error);
    if has_error {
        return Err(diagnostics);
    }
    if ir.servers.is_empty() && ir.routes.is_empty() {
        match emit_console(ir) {
            Ok(Some(main_rs)) => return Ok(ExecProgram { main_rs }),
            Ok(None) => return Err(diagnostics),
            Err(mut loop_errors) => {
                let mut all: Vec<sal_syntax::Diagnostic> = diagnostics;
                all.append(&mut loop_errors);
                return Err(all);
            }
        }
    }
    let mut servers: Vec<(&String, &ServerDecl)> = ir.servers.iter().collect();
    servers.sort_by(|left, right| left.0.cmp(right.0));
    let server: &ServerDecl = match servers.first() {
        Some(entry) => entry.1,
        None => return Err(diagnostics),
    };
    let port: u16 = match server.port {
        Some(value) => value,
        None => return Err(diagnostics),
    };
    let mut routes: Vec<(&String, &RouteDecl)> = ir.routes.iter().collect();
    routes.sort_by(|left, right| left.0.cmp(right.0));
    let mut blocks = String::new();
    for (name, route) in routes.iter() {
        blocks.push_str(&emit_route(name, route));
    }
    Ok(ExecProgram {
        main_rs: emit_main(port, &blocks),
    })
}

fn collect_c_feature_errors(ir: &Ir, errors: &mut Vec<sal_syntax::Diagnostic>) {
    let mut entities: Vec<_> = ir.entities.values().collect();
    entities.sort_by(|left, right| left.name.cmp(&right.name));
    for entity in entities {
        if entity.c_layout {
            errors.push(unsupported_c_feature("C record layout", &entity.span));
        }
    }
    let mut operations: Vec<_> = ir.operations.values().collect();
    operations.sort_by(|left, right| left.name.cmp(&right.name));
    for operation in operations {
        if operation.c_import.is_some() {
            errors.push(unsupported_c_feature("C import", &operation.span));
        }
        let mut statements: Vec<_> = operation.body.iter().rev().collect();
        let mut expressions = Vec::new();
        while let Some(statement) = statements.pop() {
            match statement {
                Stmt::Let { expr, .. }
                | Stmt::Assign { expr, .. }
                | Stmt::Return(expr)
                | Stmt::ExprStmt(expr) => expressions.push(expr),
                Stmt::If { cond, then, else_ } => {
                    expressions.push(cond);
                    statements.extend(else_.iter().rev());
                    statements.extend(then.iter().rev());
                }
                Stmt::While { cond, body } => {
                    expressions.push(cond);
                    statements.extend(body.iter().rev());
                }
                Stmt::For { iter, body, .. } => {
                    expressions.push(iter);
                    statements.extend(body.iter().rev());
                }
                Stmt::Break | Stmt::Continue => {}
            }
            while let Some(expr) = expressions.pop() {
                match expr {
                    Expr::Call { name, args } => {
                        if matches!(name.as_str(), "size_of" | "align_of" | "offset_of") {
                            errors.push(unsupported_c_feature(
                                "C record reflection",
                                &operation.span,
                            ));
                        }
                        expressions.extend(args.iter().rev());
                    }
                    Expr::Field { base, .. } | Expr::Not(base) => expressions.push(base),
                    Expr::Index { base, index } => {
                        expressions.push(index);
                        expressions.push(base);
                    }
                    Expr::BinOp { left, right, .. } => {
                        expressions.push(right);
                        expressions.push(left);
                    }
                    Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {
                    }
                }
            }
        }
    }
}

fn unsupported_c_feature(feature: &str, span: &Span) -> sal_syntax::Diagnostic {
    sal_syntax::Diagnostic {
        code: "B201",
        severity: Severity::Error,
        message: format!(
            "{feature} is not supported by the legacy Rust backend; use the native backend"
        ),
        span: span.clone(),
        suggestion: None,
    }
}

/// Emit the console program for the single hello-world operation (`returns
/// Text` + responds literal). Operations are scanned in name order; the first
/// hello-world operation wins. Body lowering: when the winning operation has
/// an empty body, emits the legacy `fn main() { println!("LIT"); }`
/// byte-for-byte; otherwise lowers `let`/`set`/`return`/`if`/call statements
/// and their expressions into a `fn main() { ... }` block (see CONTRACT
/// header). `for`/`while` loops and reserved native intrinsics are rejected:
/// returns `Err` with one B200 error per loop plus one B201 error per
/// intrinsic call (never a panic). `Ok(None)` means no hello-world operation
/// exists (check_exec reports X107 then).
fn emit_console(ir: &Ir) -> Result<Option<String>, Vec<sal_syntax::Diagnostic>> {
    let mut names: Vec<&String> = ir.operations.keys().collect();
    names.sort();
    for name in names {
        let operation = match ir.operations.get(name) {
            Some(operation) => operation,
            None => continue,
        };
        let is_text = matches!(&operation.returns, Some(TypeRef::Named(ty)) if ty == "Text");
        let has_literal = operation.responds_literal.is_some();
        let has_return = operation.body.iter().any(|stmt| match stmt {
            Stmt::Return(_) => true,
            Stmt::If { then, else_, .. } => {
                then.iter().any(|s| matches!(s, Stmt::Return(_)))
                    || else_.iter().any(|s| matches!(s, Stmt::Return(_)))
            }
            _ => false,
        });
        if is_text && (has_literal || has_return) {
            return lower_console_body(operation);
        }
    }
    Ok(None)
}

/// Lower the winning hello-world operation into its console program. A body of
/// exactly one `Return(Lit)` emits the legacy one-line program byte-for-byte;
/// an empty body falls back to the responds literal one-liner; anything else
/// goes through the general sequence lowering.
fn lower_console_body(
    operation: &sal_ir::OperationDecl,
) -> Result<Option<String>, Vec<sal_syntax::Diagnostic>> {
    if operation.body.is_empty() {
        let literal: &str = match operation.responds_literal.as_ref() {
            Some(literal) => literal.as_str(),
            None => return Ok(None),
        };
        let escaped: String = esc_console_literal(literal);
        return Ok(Some(format!(
            "fn main() {{ println!(\"{{}}\", \"{escaped}\"); }}\n"
        )));
    }
    if let [Stmt::Return(Expr::Lit(literal))] = operation.body.as_slice() {
        let escaped: String = esc_console_literal(literal);
        return Ok(Some(format!(
            "fn main() {{ println!(\"{{}}\", \"{escaped}\"); }}\n"
        )));
    }
    let mut errors: Vec<sal_syntax::Diagnostic> = Vec::new();
    collect_legacy_errors(&operation.body, &operation.span, &mut errors);
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut out = String::from("fn main() {\n");
    emit_stmts(&operation.body, 1, &mut out);
    out.push_str("}\n");
    Ok(Some(out))
}

/// Walk statements collecting one B200 error per `for`/`while` loop plus one
/// B201 error per reserved native intrinsic call. Never panics; order follows
/// source.
fn collect_legacy_errors(body: &[Stmt], span: &Span, errors: &mut Vec<sal_syntax::Diagnostic>) {
    for stmt in body.iter() {
        match stmt {
            Stmt::If {
                cond, then, else_, ..
            } => {
                collect_expr_errors(cond, span, errors);
                collect_legacy_errors(then, span, errors);
                collect_legacy_errors(else_, span, errors);
            }
            Stmt::For { iter, body, .. } => {
                errors.push(loop_error("`for` loops are not yet lowered", span));
                collect_expr_errors(iter, span, errors);
                collect_legacy_errors(body, span, errors);
            }
            Stmt::While { cond, body } => {
                errors.push(loop_error("`while` loops are not yet lowered", span));
                collect_expr_errors(cond, span, errors);
                collect_legacy_errors(body, span, errors);
            }
            Stmt::Break | Stmt::Continue => {
                errors.push(loop_error("loop control is not yet lowered", span));
            }
            Stmt::Let { expr, .. } | Stmt::Assign { expr, .. } => {
                collect_expr_errors(expr, span, errors);
            }
            Stmt::Return(expr) | Stmt::ExprStmt(expr) => {
                collect_expr_errors(expr, span, errors);
            }
        }
    }
}
/// Build one B201 error diagnostic for a reserved native intrinsic call.
fn intrinsic_error(name: &str, span: &Span) -> sal_syntax::Diagnostic {
    sal_syntax::Diagnostic {
        code: "B201",
        severity: Severity::Error,
        message: format!("`{name}` is a native intrinsic and is not lowered by the legacy backend"),
        span: span.clone(),
        suggestion: None,
    }
}

/// Walk an expression collecting one B201 error per reserved native intrinsic
/// call that the legacy backend intentionally does not lower. Plain calls and
/// the historical `len`/`push` shapes pass through; never panics.
fn collect_expr_errors(expr: &Expr, span: &Span, errors: &mut Vec<sal_syntax::Diagnostic>) {
    match expr {
        Expr::Call { name, args } => {
            if matches!(
                name.as_str(),
                "bytes"
                    | "byte"
                    | "slice"
                    | "usize"
                    | "i64"
                    | "u8"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "isize"
                    | "u16"
                    | "u32"
                    | "u64"
                    | "size_of"
                    | "align_of"
                    | "offset_of"
                    | "syscall"
                    | "address"
                    | "bytes_at"
                    | "load8"
                    | "store8"
                    | "atomic_load"
                    | "atomic_store"
                    | "atomic_cas"
                    | "load64"
                    | "store64"
                    | "concurrency_state"
                    | "operation_address"
                    | "thread_launch"
            ) {
                errors.push(intrinsic_error(name, span));
            }
            for arg in args.iter() {
                collect_expr_errors(arg, span, errors);
            }
        }
        Expr::Field { base, .. } | Expr::Not(base) => collect_expr_errors(base, span, errors),
        Expr::Index { base, index } => {
            collect_expr_errors(base, span, errors);
            collect_expr_errors(index, span, errors);
        }
        Expr::BinOp { left, right, .. } => {
            collect_expr_errors(left, span, errors);
            collect_expr_errors(right, span, errors);
        }
        Expr::Lit(_) | Expr::Int(_) | Expr::Float(_) | Expr::Bool(_) | Expr::Var(_) => {}
    }
}

/// Build one B200 error diagnostic for an unlowerable loop statement.
fn loop_error(message: &str, span: &Span) -> sal_syntax::Diagnostic {
    sal_syntax::Diagnostic {
        code: "B200",
        severity: Severity::Error,
        message: message.to_owned(),
        span: span.clone(),
        suggestion: None,
    }
}

/// Emit a statement sequence at `indent` levels of 4 spaces. Callers guarantee
/// no loops or reserved intrinsics remain (B200/B201 raised earlier), so `For`
/// and `While` render as a `compile_error!` guard that is unreachable on
/// success paths.
fn emit_stmts(body: &[Stmt], indent: usize, out: &mut String) {
    for stmt in body.iter() {
        emit_stmt(stmt, indent, out);
    }
}

/// Emit one statement at `indent` levels of 4 spaces.
fn emit_stmt(stmt: &Stmt, indent: usize, out: &mut String) {
    let pad: String = "    ".repeat(indent);
    match stmt {
        Stmt::Let {
            name,
            mutable,
            expr,
        } => {
            let rendered: String = emit_expr(expr);
            if *mutable {
                out.push_str(&format!("{pad}let mut {name} = {rendered};\n"));
            } else {
                out.push_str(&format!("{pad}let {name} = {rendered};\n"));
            }
        }
        Stmt::Assign { name, expr } => {
            let rendered: String = emit_expr(expr);
            out.push_str(&format!("{pad}{name} = {rendered};\n"));
        }
        Stmt::Return(Expr::Lit(literal)) => {
            let escaped: String = esc_console_literal(literal);
            out.push_str(&format!("{pad}println!(\"{{}}\", \"{escaped}\");\n"));
            out.push_str(&format!("{pad}return;\n"));
        }
        Stmt::Return(Expr::Var(name)) => {
            out.push_str(&format!("{pad}println!(\"{{}}\", {name});\n"));
            out.push_str(&format!("{pad}return;\n"));
        }
        Stmt::Return(expr) => {
            let rendered: String = emit_expr(expr);
            out.push_str(&format!("{pad}println!(\"{{}}\", {rendered});\n"));
            out.push_str(&format!("{pad}return;\n"));
        }
        Stmt::If { cond, then, else_ } => {
            let rendered: String = emit_expr(cond);
            out.push_str(&format!("{pad}if {rendered} {{\n"));
            emit_stmts(then, indent + 1, out);
            if else_.is_empty() {
                out.push_str(&format!("{pad}}}\n"));
            } else {
                out.push_str(&format!("{pad}}} else {{\n"));
                emit_stmts(else_, indent + 1, out);
                out.push_str(&format!("{pad}}}\n"));
            }
        }
        Stmt::ExprStmt(expr) => {
            let rendered: String = emit_expr(expr);
            out.push_str(&format!("{pad}{rendered};\n"));
        }
        Stmt::For { .. } | Stmt::While { .. } | Stmt::Break | Stmt::Continue => {
            out.push_str(&format!(
                "{pad}compile_error!(\"loops are not yet lowered (B200)\");\n"
            ));
        }
    }
}

/// Render one expression as Rust source. `len(x)` -> `x.len()`,
/// `push(v, x)` -> `v.push(x)`, other calls -> `name(args)`, field access ->
/// `base.field`, indexing -> `base[index]`, binary operators parenthesized.
fn emit_expr(expr: &Expr) -> String {
    match expr {
        Expr::Lit(literal) => format!("\"{}\"", esc_str_literal(literal)),
        Expr::Int(value) => value.to_string(),
        Expr::Float(value) => {
            let mut text: String = value.to_string();
            if !text.contains('.') && !text.contains('e') && !text.contains('E') {
                text.push_str(".0");
            }
            text
        }
        Expr::Bool(value) => value.to_string(),
        Expr::Not(value) => format!("(!{})", emit_expr(value)),
        Expr::Var(name) => name.clone(),
        Expr::Call { name, args } => emit_call(name, args),
        Expr::Field { base, field } => format!("{}.{field}", emit_expr(base)),
        Expr::Index { base, index } => {
            format!("{}[{}]", emit_expr(base), emit_expr(index))
        }
        Expr::BinOp { op, left, right } => {
            let symbol: &str = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Rem => "%",
                BinOp::Lt => "<",
                BinOp::Le => "<=",
                BinOp::Gt => ">",
                BinOp::Ge => ">=",
                BinOp::Eq => "==",
                BinOp::Ne => "!=",
                BinOp::And => "&&",
                BinOp::Or => "||",
            };
            format!("({} {symbol} {})", emit_expr(left), emit_expr(right))
        }
    }
}

/// Render a call: `len(x)` -> `x.len()`, `push(v, x)` -> `v.push(x)`,
/// anything else -> `name(arg0, arg1, ...)`. Arity is validated by
/// `check_bodies`; malformed builtin shapes fall back to plain call syntax.
fn emit_call(name: &str, args: &[Expr]) -> String {
    if name == "len" {
        if let [single] = args {
            return format!("{}.len()", emit_expr(single));
        }
    }
    if name == "push" {
        if let [vec, value] = args {
            return format!("{}.push({})", emit_expr(vec), emit_expr(value));
        }
    }
    let mut rendered = String::new();
    rendered.push_str(name);
    rendered.push('(');
    let mut first: bool = true;
    for arg in args.iter() {
        if !first {
            rendered.push_str(", ");
        }
        first = false;
        rendered.push_str(&emit_expr(arg));
    }
    rendered.push(')');
    rendered
}

/// Escape text as the inside of the console `println!("...")` literal:
/// `\` -> `\\`, `"` -> `\"`, newline -> `\n`, any other control char
/// (U+0000..U+001F except `\n`, plus U+007F) -> `\u{...}` (lowercase hex).
/// Everything else (including non-ASCII text) passes through verbatim.
/// Never panics.
fn esc_console_literal(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            _ => {
                let code: u32 = ch as u32;
                if code < 0x20 || code == 0x7F {
                    out.push_str(&format!("\\u{{{:x}}}", code));
                } else {
                    out.push(ch);
                }
            }
        }
    }
    out
}

/// Escape raw bytes as a Rust `b"..."` literal body (no panics, ASCII-only output).
fn esc_byte_string(data: &[u8]) -> String {
    let mut out = String::new();
    for byte in data.iter() {
        match byte {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            _ => {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                let hi: usize = usize::from(*byte >> 4);
                let lo: usize = usize::from(*byte & 0x0F);
                let hi_ch: char = match HEX.get(hi) {
                    Some(v) => *v as char,
                    None => '0',
                };
                let lo_ch: char = match HEX.get(lo) {
                    Some(v) => *v as char,
                    None => '0',
                };
                out.push_str("\\x");
                out.push(hi_ch);
                out.push(lo_ch);
            }
        }
    }
    out
}

/// Escape text as the inside of a Rust `"..."` string literal.
fn esc_str_literal(text: &str) -> String {
    let mut out = String::new();
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => {
                let code: u32 = ch as u32;
                if code < 0x20 || code == 0x7F {
                    out.push_str(&format!("\\u{{{:x}}}", code));
                } else {
                    out.push(ch);
                }
            }
        }
    }
    out
}

/// Emit one route-match block: length gate, per-segment literal/param checks,
/// then `respond(200, body); return;` on full match. Never emits indexing,
/// unwrap/expect/panic paths; duplicate `:p` names reuse one binding.
fn emit_route(name: &str, route: &RouteDecl) -> String {
    let path: &str = match route.path.as_ref() {
        Some(value) => value.as_str(),
        None => "/",
    };
    let stripped: &str = match path.strip_prefix('/') {
        Some(value) => value,
        None => path,
    };
    let segments: Vec<&str> = stripped.split('/').collect();
    let used_param: Option<&str> = match route.responds.as_ref() {
        Some(RespondsKind::Param(value)) => Some(value.as_str()),
        _ => None,
    };
    let mut body = String::from("b\"\"");
    match route.responds.as_ref() {
        Some(RespondsKind::Text) | None => {}
        Some(RespondsKind::Literal(text)) => {
            body = format!("b\"{}\"", esc_byte_string(text.as_bytes()));
        }
        Some(RespondsKind::Param(param)) => {
            let wanted: String = format!(":{param}");
            let mut found: bool = false;
            for segment in segments.iter() {
                if *segment == wanted.as_str() {
                    found = true;
                    break;
                }
            }
            if found {
                body = format!("cap_{param}.as_bytes()");
            }
        }
    }
    let mut checks = String::new();
    let mut declared: Vec<String> = Vec::new();
    for (index, segment) in segments.iter().enumerate() {
        match segment.strip_prefix(':') {
            Some(param) => {
                let var: String = match used_param {
                    Some(used) if used == param => format!("cap_{param}"),
                    _ => format!("_cap_{param}"),
                };
                let already: bool = declared.iter().any(|seen| seen == &var);
                if !already {
                    declared.push(var.clone());
                    checks.push_str(&format!(
                        "            let mut {var}: String = String::new();\n"
                    ));
                }
                checks.push_str(&format!(
                    "            match segs.get({index}) {{\n                Some(v) if !v.is_empty() => {{ {var} = pct_decode(*v); }}\n                _ => {{ ok = false; }}\n            }}\n"
                ));
            }
            None => {
                let lit: String = esc_str_literal(segment);
                checks.push_str(&format!(
                    "            match segs.get({index}) {{\n                Some(v) if *v == \"{lit}\" => {{}}\n                _ => {{ ok = false; }}\n            }}\n"
                ));
            }
        }
    }
    let count: usize = segments.len();
    format!(
        "    // route `{name}`: handles GET {path}\n    {{\n        if segs.len() == {count} {{\n            let mut ok: bool = true;\n{checks}            if ok {{\n                respond(&mut stream, 200, \"OK\", {body});\n                return;\n            }}\n        }}\n    }}\n"
    )
}

/// Assemble the full single-file server program. Placeholders avoid `format!`
/// brace-escaping: `@SAL_PORT@` becomes the literal port, `@SAL_ROUTES@` the
/// baked route-match blocks.
fn emit_main(port: u16, routes: &str) -> String {
    const TEMPLATE: &str = r#"use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

fn hex_val(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn pct_decode(segment: &str) -> String {
    let bytes: &[u8] = segment.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i: usize = 0;
    while i < bytes.len() {
        let byte: u8 = match bytes.get(i) {
            Some(v) => *v,
            None => break,
        };
        if byte == b'%' {
            let hi: Option<u8> = match bytes.get(i + 1) {
                Some(v) => hex_val(*v),
                None => None,
            };
            let lo: Option<u8> = match bytes.get(i + 2) {
                Some(v) => hex_val(*v),
                None => None,
            };
            match (hi, lo) {
                (Some(h), Some(l)) => {
                    out.push((h << 4) | l);
                    i += 3;
                }
                _ => {
                    out.push(b'%');
                    i += 1;
                }
            }
        } else {
            out.push(byte);
            i += 1;
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn read_request_line(stream: &mut TcpStream) -> Option<(String, String)> {
    let mut buf: Vec<u8> = Vec::new();
    let mut chunk: [u8; 512] = [0; 512];
    let mut complete: bool = false;
    while buf.len() < 8192 && !complete {
        let n: usize = match stream.read(&mut chunk) {
            Ok(v) => v,
            Err(_) => return None,
        };
        if n == 0 {
            break;
        }
        let room: usize = 8192 - buf.len();
        let take: usize = if n < room { n } else { room };
        let mut k: usize = 0;
        while k < take {
            match chunk.get(k) {
                Some(v) => buf.push(*v),
                None => break,
            }
            k += 1;
        }
        let mut j: usize = 0;
        while j < buf.len() {
            match buf.get(j) {
                Some(v) if *v == b'\n' => {
                    complete = true;
                    break;
                }
                _ => {}
            }
            j += 1;
        }
    }
    if buf.is_empty() {
        return None;
    }
    let mut end: usize = buf.len();
    let mut saw_newline: bool = false;
    let mut j: usize = 0;
    while j < buf.len() {
        match buf.get(j) {
            Some(v) if *v == b'\n' => {
                end = j;
                saw_newline = true;
                break;
            }
            _ => {}
        }
        j += 1;
    }
    if !saw_newline && buf.len() >= 8192 {
        return None;
    }
    let mut line: Vec<u8> = Vec::with_capacity(end);
    let mut k: usize = 0;
    while k < end {
        match buf.get(k) {
            Some(v) => line.push(*v),
            None => break,
        }
        k += 1;
    }
    match line.last() {
        Some(v) if *v == b'\r' => {
            let _ = line.pop();
        }
        _ => {}
    }
    let text: String = String::from_utf8_lossy(&line).into_owned();
    let parts: Vec<&str> = text.split_whitespace().collect();
    if parts.len() != 3 {
        return None;
    }
    let method: String = match parts.get(0) {
        Some(v) => (*v).to_owned(),
        None => return None,
    };
    let target: String = match parts.get(1) {
        Some(v) => (*v).to_owned(),
        None => return None,
    };
    match parts.get(2) {
        Some(v) if *v == "HTTP/1.0" || *v == "HTTP/1.1" => {}
        _ => return None,
    }
    Some((method, target))
}

fn respond(stream: &mut TcpStream, code: u16, reason: &str, body: &[u8]) {
    let header: String = format!(
        "HTTP/1.0 {} {}\r\ncontent-type: text/plain; charset=utf-8\r\ncontent-length: {}\r\nconnection: close\r\n\r\n",
        code,
        reason,
        body.len()
    );
    let _ = stream.write_all(header.as_bytes());
    let _ = stream.write_all(body);
    let _ = stream.flush();
}

fn handle(mut stream: TcpStream) {
    let req: Option<(String, String)> = read_request_line(&mut stream);
    let (method, target) = match req {
        Some(v) => v,
        None => {
            respond(&mut stream, 400, "Bad Request", b"bad request");
            return;
        }
    };
    if method != "GET" {
        respond(&mut stream, 404, "Not Found", b"not found");
        return;
    }
    let noquery: &str = match target.split('?').next() {
        Some(v) => v,
        None => {
            respond(&mut stream, 400, "Bad Request", b"bad request");
            return;
        }
    };
    let path: &str = match noquery.strip_prefix('/') {
        Some(v) => v,
        None => {
            respond(&mut stream, 400, "Bad Request", b"bad request");
            return;
        }
    };
    let segs: Vec<&str> = path.split('/').collect();
@SAL_ROUTES@    respond(&mut stream, 404, "Not Found", b"not found");
}

fn main() {
    let listener: TcpListener = match TcpListener::bind("127.0.0.1:@SAL_PORT@") {
        Ok(v) => v,
        Err(_) => return,
    };
    loop {
        let next: std::io::Result<(TcpStream, std::net::SocketAddr)> = listener.accept();
        let stream: TcpStream = match next {
            Ok((s, _)) => s,
            Err(_) => continue,
        };
        handle(stream);
    }
}
"#;
    TEMPLATE
        .replace("@SAL_PORT@", &port.to_string())
        .replace("@SAL_ROUTES@", routes)
}
