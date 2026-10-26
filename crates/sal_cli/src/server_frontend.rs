//! Server/route sugar lowers to ordinary SAL library calls, never host networking.
//! The caller validates the original namespace before consuming Server/Route
//! declarations, so generated entry points cannot hide duplicate names.

use std::fmt::Write;

use sal_syntax::{Diagnostic, Item, RespondsKind, SalFile, Severity};

pub(crate) fn lower(file: &SalFile) -> Result<Option<String>, Vec<Diagnostic>> {
    if !file
        .items
        .iter()
        .any(|item| matches!(item, Item::Server(_) | Item::Route(_)))
    {
        return Ok(None);
    }

    let mut diagnostics = sal_ir::check_declarations(file);
    diagnostics.extend(sal_ir::check_server_declarations(file));
    for item in &file.items {
        if let Item::Operation(operation) = item {
            if matches!(operation.name.as_str(), "Main" | "ServerDispatch") {
                diagnostics.push(Diagnostic {
                    code: "X109",
                    severity: Severity::Error,
                    message: format!(
                        "operation `{}` conflicts with the native server entry point",
                        operation.name
                    ),
                    span: operation.span.clone(),
                    suggestion: Some(
                        "rename the user operation before lowering server declarations".into(),
                    ),
                });
            }
        }
    }
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(diagnostics);
    }

    let port = file
        .items
        .iter()
        .find_map(|item| match item {
            Item::Server(server) => server.port,
            _ => None,
        })
        .expect("checked server has a port");
    let mut routes: Vec<_> = file
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Route(route) => Some(route),
            _ => None,
        })
        .collect();
    routes.sort_unstable_by(|left, right| left.name.cmp(&right.name));

    let mut source = String::from(
        "use \"std/server.sal\".\nuse \"std/http.sal\".\nuse \"std/routing.sal\".\n\n",
    );
    writeln!(
        source,
        "operation Main:\n    returns i64.\n    effects: SystemCall.\n    body:\n        return ServerRun(u64(0), i64({port}), usize(262144), i64(32)).\n"
    )
    .expect("write generated SAL");
    source.push_str(
        r#"operation ServerDispatch:
    accepts client of type i64.
    accepts arena of type MutBytes.
    returns i64.
    effects: SystemCall.
    body:
        let capacity = len(arena).
        if capacity < 4096:
            return -28.
        let requestCapacity = (capacity - 512) / 2.
        let decodeCapacity = capacity - 512 - requestCapacity.
        let requestBuffer = slice_mut(arena, usize(0), requestCapacity).
        let decode = slice_mut(arena, requestCapacity, decodeCapacity).
        let header = slice_mut(arena, capacity - 512, usize(512)).
        let received = HttpReadRequest(client, requestBuffer).
        if received < 0:
            if received == -400 || received == -413 || received == -431:
                return HttpWriteTextResponse(client, 0 - received, bytes(""), header).
            if received == -11 || received == -110:
                return HttpWriteTextResponse(client, i64(408), bytes(""), header).
            return received.
        let request = slice(view(requestBuffer), usize(0), usize(received)).
        if HttpMethod(request) != bytes("GET"):
            return HttpWriteTextResponse(client, i64(404), bytes(""), header).
        let path = HttpPath(request).
"#,
    );
    // Request and decode halves are disjoint; the latter is at least as large.
    // A capture cannot expand when percent-decoded, so decoding cannot exhaust
    // that half. Header scratch never aliases either borrowed or decoded bodies.
    for (index, route) in routes.iter().enumerate() {
        let pattern = literal(route.path.as_deref().expect("checked route has a path"));
        match route
            .responds
            .as_ref()
            .expect("checked route has a response")
        {
            RespondsKind::Param(name) => {
                let name = literal(name);
                writeln!(
                    source,
                    "        let capture{index} = RouteCapture(bytes({pattern}), path, bytes({name})).\n        if len(capture{index}) != 0:\n            let decoded{index} = RouteDecode(capture{index}, decode).\n            if decoded{index} == -22:\n                return HttpWriteTextResponse(client, i64(400), bytes(\"\"), header).\n            if decoded{index} < 0:\n                return decoded{index}.\n            return HttpWriteTextResponse(client, i64(200), slice(view(decode), usize(0), usize(decoded{index})), header)."
                )
                .expect("write generated route");
            }
            response => {
                let body = match response {
                    RespondsKind::Literal(body) => body.as_str(),
                    RespondsKind::Text => "",
                    RespondsKind::Param(_) => unreachable!("parameter response handled above"),
                };
                let body = literal(body);
                writeln!(
                    source,
                    "        if RouteMatch(bytes({pattern}), path):\n            return HttpWriteTextResponse(client, i64(200), bytes({body}), header)."
                )
                .expect("write generated route");
            }
        }
    }
    source
        .push_str("        return HttpWriteTextResponse(client, i64(404), bytes(\"\"), header).\n");
    Ok(Some(source))
}

// SAL escapes, not Rust debug formatting: every Unicode scalar round-trips,
// including NUL and control characters that cannot appear in a source line.
fn literal(value: &str) -> String {
    let mut result = String::with_capacity(value.len() + 2);
    result.push('"');
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character.is_control() => {
                write!(result, "\\u{{{:x}}}", u32::from(character)).expect("write SAL escape");
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}
