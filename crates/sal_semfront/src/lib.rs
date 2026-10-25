//! SAL semantic frontend: PLAIN ENGLISH in, Level-B .sal out.
//!
//! Design axes (user order): language design from Rust (strict types, explicit
//! errors, no guessing), compile speed ethos from Go (single pass, no backtrack,
//! linear classifier), semantics from plain English (free sentences, not syntax).
//!
//! CONTRACT (do not change public signatures; implement bodies only):
//! - `compile_en(source) -> (String /* Level-B sal */, Vec<Diagnostic>)` is
//!   total and deterministic: same input -> same output, no I/O, no randomness,
//!   no LLM. Every input sentence either maps to a Level-B block or yields a
//!   diagnostic; NEVER silently drops a sentence.
//! - Sentence split: split on `.`, `!`, `?` followed by whitespace-or-end; keep
//!   `;` inside a sentence. Blank sentences skipped.
//! - Per-sentence classification (first match wins, case-insensitive):
//!   1. program name: contains `program` + (`named`|`called`) + NAME ->
//!      `application NAME.` (NAME = trailing `[A-Za-z_][A-Za-z0-9_]*` token,
//!      else E9001).
//!   2. listen: contains `listen` + port digits + optional `http/1` ->
//!      `server Main:` block with `listens on port N.` and
//!      `speaks HTTP/1.` (only when `http/1`/`http 1`/`http1` present; if another
//!      version mentioned -> E9003, unsupported). Server is ALWAYS `Main`
//!      (ONE WAY: program name lives only in `application`). Repeating listen
//!      with a different port -> E9004.
//!   3. request route: contains `request`/`requests` + `to` + path with
//!      `{param}` + `return` + response kind (`plain-text`/`plain text`/`text`)
//!      -> `route NAME:`; `{p}` become `:p`; no `{param}` -> E9002.
//!   4. hello world: contains `hello` + `world` -> `operation SayHello:`
//!      with `returns Text.` + `responds with "Hello, world!".`
//!   5. type alias: `X is a Y` / `X means Y` where X in {character, word, text}
//!      (any case) and Y likewise -> registers Character/Word/Text intent;
//!      output is a `#` comment line (no Level-B needed, all three are
//!      primitives). Unknown X -> E9005.
//!   6. anything else -> E9001 unrecognized sentence (message echoes trimmed
//!      sentence, max 80 chars).
//! - After all sentences: every route's `{param}` names must be Word or Text
//!   (Character route params -> E9006). Port present but no routes -> warning
//!   W9001 (server with no routes). Routes present but no listen -> error
//!   E9004 (routes with no port).
//! - Output Level-B uses ONLY constructs the compiler already accepts, in
//!   canonical order: `application`, then `server` blocks, then `route`
//!   blocks, then `operation` blocks, each terminated per Level-B grammar.
//! - Codes: E9001 unrecognized, E9002 bad route, E9003 bad HTTP version,
//!   E9004 port/route mismatch, E9005 bad type alias, E9006 bad param type,
//!   W9001 no routes. Spans: Span::single(sentence_index + 1, 1).

use sal_syntax::Diagnostic;

pub fn compile_en(source: &str) -> (String, Vec<Diagnostic>) {
    use sal_syntax::{Severity, Span};
    use std::collections::BTreeMap;
    use std::fmt::Write;

    fn identifier(value: &str) -> bool {
        let mut bytes = value.bytes();
        bytes
            .next()
            .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
            && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    }

    fn primitive(value: &str) -> Option<&'static str> {
        match value {
            "character" => Some("Character"),
            "word" => Some("Word"),
            "text" => Some("Text"),
            _ => None,
        }
    }

    fn diagnostic(
        diagnostics: &mut Vec<Diagnostic>,
        code: &'static str,
        line: usize,
        message: String,
    ) {
        diagnostics.push(Diagnostic {
            code,
            severity: if code.starts_with('W') {
                Severity::Warning
            } else {
                Severity::Error
            },
            message,
            span: Span::single(line, 1),
            suggestion: None,
        });
    }

    struct Route<'a> {
        path: String,
        params: Vec<&'a str>,
        response: Option<&'a str>,
        line: usize,
    }

    let mut diagnostics = Vec::new();
    let mut application = None;
    let mut listen: Option<(u16, bool, usize)> = None;
    let mut routes = Vec::new();
    let mut hello_count = 0_usize;
    let mut aliases = BTreeMap::new();
    let mut alias_comments = String::new();

    // Delimiters inside paths, HTTP versions, or quoted words are retained
    // unless followed by whitespace (or the end of the input).
    let mut start = 0;
    let mut chars = source.char_indices().peekable();
    let sentences = std::iter::from_fn(|| {
        while let Some((offset, ch)) = chars.next() {
            if matches!(ch, '.' | '!' | '?')
                && chars.peek().is_none_or(|(_, next)| next.is_whitespace())
            {
                let sentence = source[start..offset].trim();
                start = offset + ch.len_utf8();
                if !sentence.is_empty() {
                    return Some(sentence);
                }
            }
        }
        let trailing = source[start..].trim();
        start = source.len();
        (!trailing.is_empty()).then_some(trailing)
    });

    for (index, sentence) in sentences.enumerate() {
        let line = index + 1;
        let lower = sentence.to_ascii_lowercase();
        let words: Vec<_> = lower
            .split(|ch: char| !ch.is_ascii_alphanumeric() && ch != '_')
            .filter(|word| !word.is_empty())
            .collect();
        let has = |word| words.contains(&word);

        if has("program") && (has("named") || has("called")) {
            let name = sentence.split_whitespace().next_back().unwrap_or("");
            if identifier(name) {
                application = Some(name.to_owned());
            } else {
                diagnostic(
                    &mut diagnostics,
                    "E9001",
                    line,
                    format!("invalid program name in `{sentence}`"),
                );
            }
            continue;
        }

        if words
            .iter()
            .any(|word| matches!(*word, "listen" | "listens" | "listening"))
        {
            let port_word = words
                .windows(2)
                .find(|pair| pair[0] == "port")
                .map(|pair| pair[1])
                .or_else(|| {
                    words.iter().enumerate().find_map(|(offset, word)| {
                        (word.bytes().all(|byte| byte.is_ascii_digit())
                            && (offset == 0 || words[offset - 1] != "http"))
                            .then_some(*word)
                    })
                });
            let Some(port) = port_word
                .and_then(|word| word.parse::<u16>().ok())
                .filter(|port| *port != 0)
            else {
                diagnostic(
                    &mut diagnostics,
                    "E9004",
                    line,
                    "listen sentence requires a port from 1 to 65535".into(),
                );
                continue;
            };

            let mut http1 = false;
            let mut unsupported = false;
            for (offset, _) in lower.match_indices("http") {
                let suffix = lower[offset + 4..].trim_start();
                let version = suffix.strip_prefix('/').unwrap_or(suffix).trim_start();
                if !version.starts_with(|ch: char| ch.is_ascii_digit()) {
                    continue;
                }
                let end = version
                    .find(|ch: char| !ch.is_ascii_digit() && ch != '.')
                    .unwrap_or(version.len());
                if &version[..end] == "1" {
                    http1 = true;
                } else {
                    unsupported = true;
                }
            }
            if unsupported {
                diagnostic(
                    &mut diagnostics,
                    "E9003",
                    line,
                    "only HTTP/1 is supported".into(),
                );
                continue;
            }
            if let Some((previous, previous_http1, _)) = &mut listen {
                if *previous != port {
                    diagnostic(
                        &mut diagnostics,
                        "E9004",
                        line,
                        format!("conflicting listen ports {previous} and {port}"),
                    );
                } else {
                    *previous_http1 |= http1;
                }
            } else {
                listen = Some((port, http1, line));
            }
            continue;
        }

        if (has("request") || has("requests"))
            && has("to")
            && words
                .iter()
                .any(|word| matches!(*word, "return" | "returns" | "returning"))
            && (has("text") || lower.contains("plain-text"))
        {
            let path = sentence
                .split_whitespace()
                .find(|word| word.starts_with('/'))
                .unwrap_or("")
                .trim_end_matches([',', ';', ':']);
            let mut pattern = String::with_capacity(path.len());
            let mut params = Vec::new();
            let mut invalid = path.is_empty();
            for (index, segment) in path.split('/').enumerate() {
                if index != 0 {
                    pattern.push('/');
                }
                if segment.starts_with('{') && segment.ends_with('}') {
                    let param = &segment[1..segment.len() - 1];
                    if !identifier(param) {
                        invalid = true;
                    }
                    pattern.push(':');
                    pattern.push_str(param);
                    params.push(param);
                } else {
                    if segment.contains(['{', '}', ':', '#', '?', '"', '\\']) {
                        invalid = true;
                    }
                    pattern.push_str(segment);
                }
            }
            if invalid || params.is_empty() {
                diagnostic(
                    &mut diagnostics,
                    "E9002",
                    line,
                    "request route requires a path containing valid {param} segments".into(),
                );
                continue;
            }
            let response = sentence
                .split('"')
                .nth(1)
                .filter(|text| params.contains(text));
            routes.push(Route {
                path: pattern,
                params,
                response,
                line,
            });
            continue;
        }

        if has("hello") && has("world") {
            hello_count += 1;
            continue;
        }

        let mut alias_words = lower.split_whitespace();
        let alias = match (
            alias_words.next(),
            alias_words.next(),
            alias_words.next(),
            alias_words.next(),
            alias_words.next(),
        ) {
            (Some(name), Some("is"), Some("a"), Some(target), None)
            | (Some(name), Some("means"), Some(target), None, None) => Some((name, target)),
            _ => None,
        };
        if let Some((name, target)) = alias {
            if let (Some(name_type), Some(target_type)) = (primitive(name), primitive(target)) {
                aliases.insert(name.to_owned(), target_type);
                let _ = writeln!(alias_comments, "# {name_type} means {target_type}.");
            } else {
                diagnostic(
                    &mut diagnostics,
                    "E9005",
                    line,
                    format!("type alias `{sentence}` must use Character, Word, or Text"),
                );
            }
            continue;
        }

        diagnostic(
            &mut diagnostics,
            "E9001",
            line,
            format!(
                "unrecognized sentence: {}",
                sentence.chars().take(80).collect::<String>()
            ),
        );
    }

    for route in &routes {
        for param in &route.params {
            let name = param.to_ascii_lowercase();
            let ty = aliases
                .get(&name)
                .copied()
                .or_else(|| primitive(&name))
                .unwrap_or("Text");
            if ty == "Character" {
                diagnostic(
                    &mut diagnostics,
                    "E9006",
                    route.line,
                    format!("route parameter `{param}` must be Word or Text, not Character"),
                );
            }
        }
    }
    if let Some((_, _, line)) = listen {
        if routes.is_empty() {
            diagnostic(
                &mut diagnostics,
                "W9001",
                line,
                "server has no routes".into(),
            );
        }
    } else if let Some(route) = routes.first() {
        diagnostic(
            &mut diagnostics,
            "E9004",
            route.line,
            "routes require a listen port".into(),
        );
    }

    let mut output = String::new();
    if let Some(name) = &application {
        let _ = writeln!(output, "application {name}.");
    }
    output.push_str(&alias_comments);
    if let Some((port, http1, _)) = listen {
        let _ = writeln!(output, "server Main:\n    listens on port {port}.");
        if http1 {
            output.push_str("    speaks HTTP/1.\n");
        }
    }
    for (index, route) in routes.iter().enumerate() {
        let _ = writeln!(
            output,
            "route Route{}:\n    handles GET {}.",
            index + 1,
            route.path
        );
        if let Some(param) = &route.response {
            let _ = writeln!(output, "    responds with param {param}.");
        } else {
            output.push_str("    responds with Text.\n");
        }
    }
    for index in 0..hello_count {
        let name = if index == 0 {
            "SayHello".to_owned()
        } else {
            format!("SayHello{}", index + 1)
        };
        let _ = writeln!(
            output,
            "operation {name}:\n    returns Text.\n    responds with \"Hello, world!\"."
        );
    }
    (output, diagnostics)
}
