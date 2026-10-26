//! File loading stays outside the pure SAL parser and semantic registry.
//! Spans use disjoint virtual line ranges, mapped back to original files here.

use std::borrow::Cow;
use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};

use sal_syntax::{format_diagnostic, parse, Diagnostic, Item, LayerRule, SalFile, Severity, Span};

struct Source {
    path: PathBuf,
    text: Cow<'static, str>,
    start: usize,
    end: usize,
}

pub(crate) struct Sources {
    pub(crate) file: SalFile,
    pub(crate) diagnostics: Vec<Diagnostic>,
    originals: Vec<Source>,
    next_line: usize,
    loaded: BTreeSet<PathBuf>,
}

impl Sources {
    pub(crate) fn load(path: &str) -> Self {
        Self::from_text(Path::new(path), crate::read_source(path))
    }

    /// Resolve imports relative to the containing SAL source file.
    pub(crate) fn from_text(path: &Path, text: String) -> Self {
        let root = path.canonicalize().unwrap_or_else(|_| path.to_owned());
        let mut sources = Self {
            file: SalFile::default(),
            diagnostics: Vec::new(),
            originals: Vec::new(),
            next_line: 1,
            loaded: BTreeSet::new(),
        };
        let imports = sources.add(&root, Cow::Owned(text));
        sources.expand(root, imports);
        sources.ensure_runtimes();
        sources
    }

    pub(crate) fn append_generated(&mut self, text: String) {
        let path = PathBuf::from(format!("<generated:{}>", self.originals.len()));
        let imports = self.add(&path, Cow::Owned(text));
        self.expand(path, imports);
        self.ensure_runtimes();
    }

    fn ensure_runtimes(&mut self) {
        let runtimes = [
            (
                "std/json_model.sal",
                sal_ir::declarations::requires_json_runtime as fn(&SalFile) -> bool,
            ),
            (
                "std/text.sal",
                sal_ir::memory::requires_text_runtime as fn(&SalFile) -> bool,
            ),
            (
                "std/buffer.sal",
                sal_ir::memory::requires_buffer_runtime as fn(&SalFile) -> bool,
            ),
            (
                "std/collections.sal",
                sal_ir::collections::requires_collections_runtime as fn(&SalFile) -> bool,
            ),
        ];
        for (module, required) in runtimes {
            let path = Path::new(module);
            if self.loaded.contains(path) || !required(&self.file) {
                continue;
            }
            let text = standard_text(path).expect("embedded language runtime");
            let imports = self.add(path, Cow::Borrowed(text));
            self.expand(path.to_owned(), imports);
        }
    }

    fn expand(&mut self, root: PathBuf, imports: Vec<(PathBuf, Span)>) {
        enum Work {
            Enter { path: PathBuf, requested_at: Span },
            Leave(PathBuf),
        }
        let mut pending = Vec::new();
        let mut active = BTreeSet::new();
        active.insert(root.clone());
        pending.push(Work::Leave(root));
        for (path, requested_at) in imports.into_iter().rev() {
            pending.push(Work::Enter { path, requested_at });
        }
        while let Some(work) = pending.pop() {
            let (path, requested_at) = match work {
                Work::Leave(path) => {
                    active.remove(&path);
                    self.loaded.insert(path);
                    continue;
                }
                Work::Enter { path, requested_at } => (path, requested_at),
            };
            let canonical = if path.starts_with("std") {
                path
            } else {
                match path.canonicalize() {
                    Ok(path) => path,
                    Err(error) => {
                        self.problem(
                            format!("cannot load source '{}': {error}", path.display()),
                            requested_at,
                        );
                        continue;
                    }
                }
            };
            if active.contains(&canonical) {
                self.problem(
                    format!("source use cycle reaches '{}'", canonical.display()),
                    requested_at,
                );
                continue;
            }
            if self.loaded.contains(&canonical) {
                continue;
            }
            let text = if let Some(text) = standard_text(&canonical) {
                Cow::Borrowed(text)
            } else if canonical.starts_with("std") {
                self.problem(
                    format!("unknown standard module '{}'", canonical.display()),
                    requested_at,
                );
                continue;
            } else {
                match std::fs::read_to_string(&canonical) {
                    Ok(text) => Cow::Owned(text),
                    Err(error) => {
                        self.problem(
                            format!("cannot read source '{}': {error}", canonical.display()),
                            requested_at,
                        );
                        continue;
                    }
                }
            };
            let imports = self.add(&canonical, text);
            active.insert(canonical.clone());
            pending.push(Work::Leave(canonical));
            for (path, requested_at) in imports.into_iter().rev() {
                pending.push(Work::Enter { path, requested_at });
            }
        }
    }

    fn problem(&mut self, message: String, span: Span) {
        self.diagnostics.push(Diagnostic {
            code: "SRC100",
            severity: Severity::Error,
            message,
            span,
            suggestion: None,
        });
    }

    fn add(&mut self, path: &Path, text: Cow<'static, str>) -> Vec<(PathBuf, Span)> {
        let offset = self.next_line - 1;
        let (file, diagnostics) = parse(&text);
        self.next_line += text.lines().count().max(1) + 1;
        self.originals.push(Source {
            path: path.to_owned(),
            text,
            start: offset + 1,
            end: self.next_line,
        });
        self.diagnostics
            .extend(diagnostics.into_iter().map(|mut diagnostic| {
                shift(&mut diagnostic.span, offset);
                diagnostic
            }));
        let mut imports = Vec::new();
        for mut item in file.items {
            shift_item(&mut item, offset);
            if let Item::Use {
                path: relative,
                span,
            } = item
            {
                match import_path(path, Path::new(&relative)) {
                    Ok(path) => imports.push((path, span)),
                    Err(message) => self.problem(message.into(), span),
                }
            } else {
                self.file.items.push(item);
            }
        }
        imports
    }

    pub(crate) fn format(&self, diagnostic: &Diagnostic) -> String {
        let original = self.originals.iter().find(|source| {
            source.start <= diagnostic.span.line && diagnostic.span.line < source.end
        });
        if let Some(source) = original {
            let mut local = diagnostic.clone();
            local.span.line -= source.start - 1;
            local.span.end_line -= source.start - 1;
            format!(
                "{}:\n{}",
                source.path.display(),
                format_diagnostic(&local, &source.text)
            )
        } else {
            format_diagnostic(diagnostic, "")
        }
    }
}

fn import_path(owner: &Path, relative: &Path) -> Result<PathBuf, &'static str> {
    if relative.is_absolute() {
        return Err("source use requires a relative path");
    }
    let joined = if relative.starts_with("std") {
        relative.to_owned()
    } else {
        owner.parent().unwrap_or(Path::new(".")).join(relative)
    };
    if !joined.starts_with("std") {
        return Ok(joined);
    }
    let mut normalized = PathBuf::new();
    let mut depth = 0;
    for component in joined.components() {
        match component {
            Component::Normal(part) => {
                normalized.push(part);
                depth += 1;
            }
            Component::CurDir => {}
            Component::ParentDir if depth > 1 => {
                normalized.pop();
                depth -= 1;
            }
            _ => return Err("source use cannot escape the standard package"),
        }
    }
    Ok(normalized)
}

fn standard_text(path: &Path) -> Option<&'static str> {
    Some(match path.to_str()? {
        "std/bytes.sal" => include_str!("../../../stdlib/bytes.sal"),
        "std/http.sal" => include_str!("../../../stdlib/http.sal"),
        "std/json.sal" => include_str!("../../../stdlib/json.sal"),
        "std/json_model.sal" => include_str!("../../../stdlib/json_model.sal"),
        "std/text_list.sal" => include_str!("../../../stdlib/text_list.sal"),
        "std/routing.sal" => include_str!("../../../stdlib/routing.sal"),
        "std/server.sal" => include_str!("../../../stdlib/server.sal"),
        "std/postgres.sal" => include_str!("../../../stdlib/postgres.sal"),
        "std/concurrency.sal" => include_str!("../../../stdlib/concurrency.sal"),
        "std/buffer.sal" => include_str!("../../../stdlib/buffer.sal"),
        "std/text.sal" => include_str!("../../../stdlib/text.sal"),
        "std/math.sal" => include_str!("../../../stdlib/math.sal"),
        "std/time.sal" => include_str!("../../../stdlib/time.sal"),
        "std/binary.sal" => include_str!("../../../stdlib/binary.sal"),
        "std/hash.sal" => include_str!("../../../stdlib/hash.sal"),
        "std/fs.sal" => include_str!("../../../stdlib/fs.sal"),
        "std/net.sal" => include_str!("../../../stdlib/net.sal"),
        "std/http_client.sal" => include_str!("../../../stdlib/http_client.sal"),
        "std/collections.sal" => include_str!("../../../stdlib/collections.sal"),
        "std/linux/io.sal" => include_str!("../../../stdlib/linux/io.sal"),
        "std/linux/net.sal" => include_str!("../../../stdlib/linux/net.sal"),
        "std/linux/memory.sal" => include_str!("../../../stdlib/linux/memory.sal"),
        "std/linux/process.sal" => include_str!("../../../stdlib/linux/process.sal"),
        _ => return None,
    })
}

fn shift(span: &mut Span, offset: usize) {
    span.line += offset;
    span.end_line += offset;
}

fn shift_item(item: &mut Item, offset: usize) {
    let span = match item {
        Item::Application { span, .. } | Item::Use { span, .. } => span,
        Item::Entity(entity) => {
            for field in &mut entity.fields {
                shift(&mut field.span, offset);
            }
            &mut entity.span
        }
        Item::Enum(declaration) => &mut declaration.span,
        Item::Layer(layer) => {
            for rule in &mut layer.rules {
                let (LayerRule::Owns { span, .. }
                | LayerRule::MayDependOn { span, .. }
                | LayerRule::MustNotDependOn { span, .. }) = rule;
                shift(span, offset);
            }
            &mut layer.span
        }
        Item::Service(service) => &mut service.span,
        Item::Operation(operation) => &mut operation.span,
        Item::Module(module) => &mut module.span,
        Item::Server(server) => &mut server.span,
        Item::Route(route) => &mut route.span,
    };
    shift(span, offset);
}
