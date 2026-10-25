//! SAL Level-B syntax: controlled-English frontend.
//!
//! CONTRACT:
//! - Line-based grammar, `#` comments, blank lines skipped. Indent = spaces (tab = 4).
//! - Top-level (indent 0) headers:
//!   `application NAME.` | `use "PATH".` | `entity NAME:` | `enum NAME:` | `layer NAME:`
//!   | `service NAME:` | `operation NAME:` | `module NAME:`
//! - `entity` body: `has FIELD of type TYPE.` | `invariant TEXT.`
//! - `enum` body: `VARIANT.`
//! - `layer` body: `owns NAME.` | `may depend on NAME.`
//!   | `must not depend on NAME.` | `must not depend on NAME directly.`
//! - `service` body: `belongs to NAME.` | `implements NAME.`
//!   | `requires:` | `ensures:` | `ensures on success:`
//!   | `execution must be atomic.` | `allowed effects:` | `forbidden effects:`
//!   Sub-blocks under `requires:`/`ensures:`/`allowed effects:`/`forbidden effects:`
//!   hold one `ITEM.` per line at deeper indent (trailing `.` stripped on store).
//! - `operation` body: `accepts NAME of type TYPE.` | `returns TYPE.`
//!   | `effects: A, B.` | `exports "C" as "symbol".`
//!   | `requires:` / `ensures:` sub-blocks as above.
//!   | `body:` containing lets (`let NAME = EXPR.` / `let mut NAME = EXPR.`),
//!   assignments (`set NAME = EXPR.`), returns, expressions, if/else, for, and while.
//!   Expressions include literals, names, calls, fields, indexes, parenthesized
//!   groups, `+`, `-`, `*`, `/`, `%`, `<`, `<=`, `>`, `>=`, `==`, `!=`.
//!   Reserved intrinsic names stay ordinary calls here; reservation is semantic.
//!   `responds with "literal".` also stores the canonical `Return(Lit)` body node.
//! - `module` body: `belongs to NAME.` | `owns NAME.` | `may read NAME.`
//!   | `may modify NAME.` | `cannot modify NAME.` | `forbids CAP.` | `implements NAME.`
//! - `TYPE` = `Ident` with optional `<T, ...>` args (spaces allowed). `NAME` =
//!   `[A-Za-z_][A-Za-z0-9_]*`. Every statement ends with `.` (headers with `:`).
//! - `parse` is total: never panics, recovers per line/block, collects diagnostics.
//!   Error codes: E0001 unknown statement, E0002 bad terminator, E0003 bad indent,
//!   E0004 malformed type or expression, E0005 empty block.
//! - `format_diagnostic` renders rustc-style: `error[E0001]: msg\n --> line:col\n |
//!   <src>\n | ^^^ suggestion?`.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub col: usize,
    pub end_line: usize,
    pub end_col: usize,
}

impl Span {
    pub fn single(line: usize, col: usize) -> Self {
        Self {
            line,
            col,
            end_line: line,
            end_col: col + 1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Severity::Error => write!(f, "error"),
            Severity::Warning => write!(f, "warning"),
            Severity::Info => write!(f, "info"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub code: &'static str,
    pub severity: Severity,
    pub message: String,
    pub span: Span,
    pub suggestion: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeRef {
    Named(String),
    Generic { name: String, args: Vec<TypeRef> },
}

#[derive(Debug, Clone)]
pub struct FieldDecl {
    pub name: String,
    pub ty: TypeRef,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct EntityDecl {
    pub name: String,
    pub span: Span,
    pub fields: Vec<FieldDecl>,
    pub invariants: Vec<String>,
    pub c_layout: bool,
}

#[derive(Debug, Clone)]
pub struct EnumDecl {
    pub name: String,
    pub span: Span,
    pub variants: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum LayerRule {
    Owns {
        name: String,
        span: Span,
    },
    MayDependOn {
        target: String,
        span: Span,
    },
    MustNotDependOn {
        target: String,
        direct_only: bool,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub struct LayerDecl {
    pub name: String,
    pub span: Span,
    pub rules: Vec<LayerRule>,
}

#[derive(Debug, Clone)]
pub struct ServiceDecl {
    pub name: String,
    pub span: Span,
    pub belongs_to: Option<String>,
    pub implements: Vec<String>,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub atomic: bool,
    pub allowed_effects: Vec<String>,
    pub forbidden_effects: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ParamDecl {
    pub name: String,
    pub ty: TypeRef,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        name: String,
        mutable: bool,
        expr: Expr,
    },
    Assign {
        name: String,
        expr: Expr,
    },
    Return(Expr),
    If {
        cond: Expr,
        then: Vec<Stmt>,
        else_: Vec<Stmt>,
    },
    For {
        var: String,
        iter: Expr,
        body: Vec<Stmt>,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
    },
    Break,
    Continue,
    ExprStmt(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Lit(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Not(Box<Expr>),
    Var(String),
    Call {
        name: String,
        args: Vec<Expr>,
    },
    Field {
        base: Box<Expr>,
        field: String,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub struct OperationDecl {
    pub name: String,
    pub span: Span,
    pub accepts: Vec<ParamDecl>,
    pub returns: Option<TypeRef>,
    pub effects: Vec<String>,
    pub requires: Vec<String>,
    pub ensures: Vec<String>,
    pub responds_literal: Option<String>,
    pub c_export: Option<String>,
    pub c_import: Option<String>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub struct ModuleDecl {
    pub name: String,
    pub span: Span,
    pub belongs_to: Option<String>,
    pub owns: Vec<String>,
    pub may_read: Vec<String>,
    pub may_modify: Vec<String>,
    pub cannot_modify: Vec<String>,
    pub forbids: Vec<String>,
    pub implements: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ServerDecl {
    pub name: String,
    pub span: Span,
    pub port: Option<u16>,
    pub http_version: Option<String>,
}

#[derive(Debug, Clone)]
pub enum RouteMethod {
    Get,
}

#[derive(Debug, Clone)]
pub struct RouteDecl {
    pub name: String,
    pub span: Span,
    pub method: Option<RouteMethod>,
    pub path: Option<String>,
    pub responds: Option<RespondsKind>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RespondsKind {
    Text,
    Literal(String),
    Param(String),
}

#[derive(Debug, Clone)]
pub enum Item {
    Application { name: String, span: Span },
    Use { path: String, span: Span },
    Entity(EntityDecl),
    Enum(EnumDecl),
    Layer(LayerDecl),
    Service(ServiceDecl),
    Operation(OperationDecl),
    Module(ModuleDecl),
    Server(ServerDecl),
    Route(RouteDecl),
}

#[derive(Debug, Clone, Default)]
pub struct SalFile {
    pub items: Vec<Item>,
}

pub fn parse(_source: &str) -> (SalFile, Vec<Diagnostic>) {
    struct Line<'a> {
        number: usize,
        indent: usize,
        text: &'a str,
    }

    impl Line<'_> {
        fn span(&self) -> Span {
            Span {
                line: self.number,
                col: self.indent + 1,
                end_line: self.number,
                end_col: self.indent + self.text.chars().count() + 1,
            }
        }

        fn diagnostic(&self, code: &'static str, message: &str) -> Diagnostic {
            Diagnostic {
                code,
                severity: Severity::Error,
                message: message.into(),
                span: self.span(),
                suggestion: None,
            }
        }
    }

    fn is_name(text: &str) -> bool {
        let mut bytes = text.bytes();
        matches!(bytes.next(), Some(b'a'..=b'z' | b'A'..=b'Z' | b'_'))
            && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    }

    fn discard_type(ty: TypeRef) {
        let mut pending = match ty {
            TypeRef::Named(_) => return,
            TypeRef::Generic { args, .. } => args,
        };
        while let Some(ty) = pending.pop() {
            if let TypeRef::Generic { mut args, .. } = ty {
                pending.append(&mut args);
            }
        }
    }

    // Keep generic parsing iterative so deeply nested user input does not
    // consume the call stack.
    fn parse_type(text: &str) -> Option<TypeRef> {
        fn skip_space(bytes: &[u8], offset: &mut usize) {
            while bytes.get(*offset).is_some_and(u8::is_ascii_whitespace) {
                *offset += 1;
            }
        }

        struct Parents(Vec<(String, Vec<TypeRef>)>);

        impl Drop for Parents {
            fn drop(&mut self) {
                for (_, args) in &mut self.0 {
                    while let Some(ty) = args.pop() {
                        discard_type(ty);
                    }
                }
            }
        }

        let bytes = text.as_bytes();
        let mut offset = 0;
        let mut parents = Parents(Vec::new());
        'types: loop {
            skip_space(bytes, &mut offset);
            let start = offset;
            if !matches!(bytes.get(offset), Some(b'a'..=b'z' | b'A'..=b'Z' | b'_')) {
                return None;
            }
            offset += 1;
            while bytes
                .get(offset)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            {
                offset += 1;
            }
            let name = text.get(start..offset)?.to_owned();
            skip_space(bytes, &mut offset);
            if bytes.get(offset) == Some(&b'<') {
                parents.0.push((name, Vec::new()));
                offset += 1;
                continue;
            }
            let mut ty = TypeRef::Named(name);
            loop {
                skip_space(bytes, &mut offset);
                if parents.0.is_empty() {
                    if offset == bytes.len() {
                        return Some(ty);
                    }
                    discard_type(ty);
                    return None;
                }
                match bytes.get(offset) {
                    Some(b',') => {
                        if let Some((_, args)) = parents.0.last_mut() {
                            args.push(ty);
                        }
                        offset += 1;
                        continue 'types;
                    }
                    Some(b'>') => {
                        let Some((name, mut args)) = parents.0.pop() else {
                            discard_type(ty);
                            return None;
                        };
                        args.push(ty);
                        ty = TypeRef::Generic { name, args };
                        offset += 1;
                    }
                    _ => {
                        discard_type(ty);
                        return None;
                    }
                }
            }
        }
    }

    fn discard_expr(expr: Expr) {
        let mut pending = vec![expr];
        while let Some(expr) = pending.pop() {
            match expr {
                Expr::Call { mut args, .. } => pending.append(&mut args),
                Expr::Field { base, .. } | Expr::Not(base) => pending.push(*base),
                Expr::Index { base, index } => {
                    pending.push(*base);
                    pending.push(*index);
                }
                Expr::BinOp { left, right, .. } => {
                    pending.push(*left);
                    pending.push(*right);
                }
                _ => {}
            }
        }
    }

    fn expr_name<'a>(text: &'a str, offset: &mut usize) -> Option<&'a str> {
        let bytes = text.as_bytes();
        let start = *offset;
        if !matches!(bytes.get(*offset), Some(b'a'..=b'z' | b'A'..=b'Z' | b'_')) {
            return None;
        }
        *offset += 1;
        while bytes
            .get(*offset)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        {
            *offset += 1;
        }
        text.get(start..*offset)
    }

    fn expr_space(text: &str, offset: &mut usize) {
        while text
            .as_bytes()
            .get(*offset)
            .is_some_and(u8::is_ascii_whitespace)
        {
            *offset += 1;
        }
    }

    /// Unescape SAL string contents: `\\`, `\"`, `\n`, `\r`, `\t`,
    /// `\u{HEX}` (1-6 hex digits). Unknown escapes fail (None) so the
    /// expression is rejected instead of silently mangled. Never panics.
    fn unescape(raw: &str) -> Option<String> {
        let bytes = raw.as_bytes();
        let mut out = String::with_capacity(raw.len());
        let mut i = 0;
        while i < bytes.len() {
            let b = match bytes.get(i) {
                Some(v) => *v,
                None => break,
            };
            if b != b'\\' {
                let ch = raw.get(i..)?.chars().next()?;
                out.push(ch);
                i += ch.len_utf8();
                continue;
            }
            let e = *bytes.get(i + 1)?;
            match e {
                b'\\' => {
                    out.push('\\');
                    i += 2;
                }
                b'"' => {
                    out.push('"');
                    i += 2;
                }
                b'n' => {
                    out.push('\n');
                    i += 2;
                }
                b'r' => {
                    out.push('\r');
                    i += 2;
                }
                b't' => {
                    out.push('\t');
                    i += 2;
                }
                b'u' => {
                    if *bytes.get(i + 2)? != b'{' {
                        return None;
                    }
                    let mut j = i + 3;
                    let mut code: u32 = 0;
                    let mut digits = 0;
                    loop {
                        let d = *bytes.get(j)?;
                        if d == b'}' {
                            break;
                        }
                        let v = match d {
                            b'0'..=b'9' => u32::from(d - b'0'),
                            b'a'..=b'f' => u32::from(d - b'a') + 10,
                            b'A'..=b'F' => u32::from(d - b'A') + 10,
                            _ => return None,
                        };
                        if digits >= 6 {
                            return None;
                        }
                        code = code * 16 + v;
                        digits += 1;
                        j += 1;
                    }
                    if digits == 0 {
                        return None;
                    }
                    out.push(char::from_u32(code)?);
                    i = j + 1;
                }
                _ => return None,
            }
        }
        Some(out)
    }

    // Explicit frames keep both parsing and malformed-expression cleanup off
    // the call stack, including deeply nested calls, indexes and binary trees.
    fn parse_expr(text: &str) -> Option<Expr> {
        enum Kind {
            Root,
            Call { name: String, args: Vec<Expr> },
            Index(Option<Expr>),
            Group,
        }
        #[derive(Clone, Copy)]
        enum PendingOp {
            Binary(BinOp),
            Not,
        }
        struct Frame {
            kind: Kind,
            values: Vec<Expr>,
            ops: Vec<PendingOp>,
            expect_value: bool,
        }
        impl Frame {
            fn new(kind: Kind) -> Self {
                Self {
                    kind,
                    values: Vec::new(),
                    ops: Vec::new(),
                    expect_value: true,
                }
            }

            fn reduce(&mut self) -> Option<()> {
                match self.ops.pop()? {
                    PendingOp::Not => {
                        let value = self.values.pop()?;
                        self.values.push(Expr::Not(Box::new(value)));
                    }
                    PendingOp::Binary(op) => {
                        let right = self.values.pop()?;
                        let left = self.values.pop()?;
                        self.values.push(Expr::BinOp {
                            op,
                            left: Box::new(left),
                            right: Box::new(right),
                        });
                    }
                }
                Some(())
            }

            fn finish(&mut self) -> Option<Expr> {
                if self.expect_value {
                    return None;
                }
                while !self.ops.is_empty() {
                    self.reduce()?;
                }
                if self.values.len() != 1 {
                    return None;
                }
                self.expect_value = true;
                self.values.pop()
            }
        }
        impl Drop for Frame {
            fn drop(&mut self) {
                for value in self.values.drain(..) {
                    discard_expr(value);
                }
                match &mut self.kind {
                    Kind::Call { args, .. } => {
                        for arg in args.drain(..) {
                            discard_expr(arg);
                        }
                    }
                    Kind::Index(base) => {
                        if let Some(base) = base.take() {
                            discard_expr(base);
                        }
                    }
                    Kind::Root | Kind::Group => {}
                }
            }
        }
        fn precedence(op: PendingOp) -> u8 {
            match op {
                PendingOp::Not => 6,
                PendingOp::Binary(op) => match op {
                    BinOp::Mul | BinOp::Div | BinOp::Rem => 5,
                    BinOp::Add | BinOp::Sub => 4,
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 3,
                    BinOp::Eq | BinOp::Ne => 2,
                    BinOp::And => 1,
                    BinOp::Or => 0,
                },
            }
        }

        let bytes = text.as_bytes();
        let mut offset = 0;
        let mut frames = vec![Frame::new(Kind::Root)];
        loop {
            expr_space(text, &mut offset);
            let token = bytes.get(offset).copied();
            if token.is_none() {
                return if frames.len() == 1 {
                    frames.last_mut()?.finish()
                } else {
                    None
                };
            }
            let frame = frames.last_mut()?;
            if frame.expect_value && token == Some(b'!') && bytes.get(offset + 1) != Some(&b'=') {
                frame.ops.push(PendingOp::Not);
                offset += 1;
                continue;
            }
            if frame.expect_value && token == Some(b'(') {
                offset += 1;
                frames.push(Frame::new(Kind::Group));
                continue;
            }
            if frame.expect_value && token != Some(b')') {
                let value = match token? {
                    b'"' => {
                        offset += 1;
                        let start = offset;
                        let mut escaped = false;
                        loop {
                            let byte = *bytes.get(offset)?;
                            if byte == b'"' && !escaped {
                                break;
                            }
                            escaped = byte == b'\\' && !escaped;
                            offset += 1;
                        }
                        let literal = unescape(text.get(start..offset)?)?;
                        offset += 1;
                        Expr::Lit(literal)
                    }
                    b'-' | b'0'..=b'9' => {
                        let start = offset;
                        if token == Some(b'-') {
                            offset += 1;
                        }
                        let digits = offset;
                        while bytes.get(offset).is_some_and(u8::is_ascii_digit) {
                            offset += 1;
                        }
                        if offset == digits {
                            return None;
                        }
                        let float = bytes.get(offset) == Some(&b'.')
                            && bytes.get(offset + 1).is_some_and(u8::is_ascii_digit);
                        if float {
                            offset += 1;
                            while bytes.get(offset).is_some_and(u8::is_ascii_digit) {
                                offset += 1;
                            }
                        }
                        let number = text.get(start..offset)?;
                        if float {
                            let value: f64 = number.parse().ok()?;
                            if !value.is_finite() {
                                return None;
                            }
                            Expr::Float(value)
                        } else {
                            Expr::Int(number.parse().ok()?)
                        }
                    }
                    _ => {
                        let name = expr_name(text, &mut offset)?;
                        expr_space(text, &mut offset);
                        if bytes.get(offset) == Some(&b'(') && !matches!(name, "true" | "false") {
                            offset += 1;
                            frames.push(Frame::new(Kind::Call {
                                name: name.to_owned(),
                                args: Vec::new(),
                            }));
                            continue;
                        }
                        match name {
                            "true" => Expr::Bool(true),
                            "false" => Expr::Bool(false),
                            _ => Expr::Var(name.to_owned()),
                        }
                    }
                };
                let frame = frames.last_mut()?;
                frame.values.push(value);
                frame.expect_value = false;
                continue;
            }
            match token? {
                b'.' if !frame.expect_value => {
                    offset += 1;
                    expr_space(text, &mut offset);
                    let field = expr_name(text, &mut offset)?.to_owned();
                    let base = frame.values.pop()?;
                    frame.values.push(Expr::Field {
                        base: Box::new(base),
                        field,
                    });
                }
                b'[' if !frame.expect_value => {
                    let base = frame.values.pop()?;
                    offset += 1;
                    frames.push(Frame::new(Kind::Index(Some(base))));
                }
                b',' if !frame.expect_value && matches!(frame.kind, Kind::Call { .. }) => {
                    let arg = frame.finish()?;
                    if let Kind::Call { args, .. } = &mut frame.kind {
                        args.push(arg);
                    }
                    offset += 1;
                }
                b')' | b']' => {
                    let mut frame = frames.pop()?;
                    let closing_call = token == Some(b')');
                    if !matches!(
                        (&frame.kind, closing_call),
                        (Kind::Call { .. }, true) | (Kind::Index(_), false) | (Kind::Group, true)
                    ) {
                        return None;
                    }
                    let empty_call = matches!(&frame.kind, Kind::Call { args, .. } if args.is_empty())
                        && frame.expect_value
                        && frame.values.is_empty()
                        && frame.ops.is_empty();
                    if !empty_call {
                        let value = frame.finish()?;
                        match &mut frame.kind {
                            Kind::Call { args, .. } => args.push(value),
                            Kind::Index(_) | Kind::Group => frame.values.push(value),
                            Kind::Root => return None,
                        }
                    }
                    let value = match std::mem::replace(&mut frame.kind, Kind::Root) {
                        Kind::Call { name, args } => Expr::Call { name, args },
                        Kind::Index(Some(base)) => Expr::Index {
                            base: Box::new(base),
                            index: Box::new(frame.values.pop()?),
                        },
                        Kind::Group => frame.values.pop()?,
                        _ => return None,
                    };
                    let parent = frames.last_mut()?;
                    parent.values.push(value);
                    parent.expect_value = false;
                    offset += 1;
                }
                _ if !frame.expect_value => {
                    let (op, width) = match (token?, bytes.get(offset + 1)) {
                        (b'+', _) => (BinOp::Add, 1),
                        (b'-', _) => (BinOp::Sub, 1),
                        (b'*', _) => (BinOp::Mul, 1),
                        (b'/', _) => (BinOp::Div, 1),
                        (b'%', _) => (BinOp::Rem, 1),
                        (b'<', Some(b'=')) => (BinOp::Le, 2),
                        (b'>', Some(b'=')) => (BinOp::Ge, 2),
                        (b'<', _) => (BinOp::Lt, 1),
                        (b'>', _) => (BinOp::Gt, 1),
                        (b'=', Some(b'=')) => (BinOp::Eq, 2),
                        (b'!', Some(b'=')) => (BinOp::Ne, 2),
                        (b'&', Some(b'&')) => (BinOp::And, 2),
                        (b'|', Some(b'|')) => (BinOp::Or, 2),
                        _ => return None,
                    };
                    while frame.ops.last().is_some_and(|previous| {
                        precedence(*previous) >= precedence(PendingOp::Binary(op))
                    }) {
                        frame.reduce()?;
                    }
                    frame.ops.push(PendingOp::Binary(op));
                    frame.expect_value = true;
                    offset += width;
                }
                _ => return None,
            }
        }
    }

    type ParseError = (&'static str, &'static str);

    fn header(line: &Line<'_>) -> Result<(Item, bool), ParseError> {
        let keyword = line
            .text
            .split(|ch: char| ch.is_whitespace() || ch == ':' || ch == '.')
            .next()
            .unwrap_or("");
        let is_block = match keyword {
            "application" | "use" => false,
            "entity" | "enum" | "layer" | "service" | "operation" | "module" | "server"
            | "route" => true,
            _ => return Err(("E0001", "unknown top-level statement")),
        };
        if keyword == "use" {
            let Some(stem) = line.text.strip_suffix('.') else {
                return Err(("E0002", "use statement must end with `.`"));
            };
            let rest = stem.get(keyword.len()..).unwrap_or("");
            if !rest.starts_with(char::is_whitespace) {
                return Err(("E0001", "expected `use \"PATH\".`"));
            }
            let path = rest.trim();
            let expression = parse_expr(path).ok_or(("E0004", "expected `use \"PATH\".`"))?;
            let literal = match expression {
                Expr::Lit(literal) => literal,
                expression => {
                    discard_expr(expression);
                    return Err(("E0004", "expected `use \"PATH\".`"));
                }
            };
            if literal.is_empty() || literal.contains('\0') {
                return Err(("E0004", "use path must be nonempty and contain no NUL"));
            }
            return Ok((
                Item::Use {
                    path: literal,
                    span: line.span(),
                },
                false,
            ));
        }
        let terminator = if is_block { ':' } else { '.' };
        let Some(stem) = line.text.strip_suffix(terminator) else {
            return Err((
                "E0002",
                if is_block {
                    "declaration header must end with `:`"
                } else {
                    "application statement must end with `.`"
                },
            ));
        };
        let name = stem.get(keyword.len()..).unwrap_or("").trim();
        if !is_name(name)
            || !stem
                .get(keyword.len()..)
                .is_some_and(|rest| rest.starts_with(char::is_whitespace))
        {
            return Err(("E0001", "expected an identifier after declaration keyword"));
        }
        let name = name.to_owned();
        let span = line.span();
        let item = match keyword {
            "application" => Item::Application { name, span },
            "entity" => Item::Entity(EntityDecl {
                name,
                span,
                fields: Vec::new(),
                invariants: Vec::new(),
                c_layout: false,
            }),
            "enum" => Item::Enum(EnumDecl {
                name,
                span,
                variants: Vec::new(),
            }),
            "layer" => Item::Layer(LayerDecl {
                name,
                span,
                rules: Vec::new(),
            }),
            "service" => Item::Service(ServiceDecl {
                name,
                span,
                belongs_to: None,
                implements: Vec::new(),
                requires: Vec::new(),
                ensures: Vec::new(),
                atomic: false,
                allowed_effects: Vec::new(),
                forbidden_effects: Vec::new(),
            }),
            "operation" => Item::Operation(OperationDecl {
                name,
                span,
                accepts: Vec::new(),
                returns: None,
                effects: Vec::new(),
                requires: Vec::new(),
                ensures: Vec::new(),
                responds_literal: None,
                c_export: None,
                c_import: None,
                body: Vec::new(),
            }),
            "module" => Item::Module(ModuleDecl {
                name,
                span,
                belongs_to: None,
                owns: Vec::new(),
                may_read: Vec::new(),
                may_modify: Vec::new(),
                cannot_modify: Vec::new(),
                forbids: Vec::new(),
                implements: Vec::new(),
            }),
            "server" => Item::Server(ServerDecl {
                name,
                span,
                port: None,
                http_version: None,
            }),
            "route" => Item::Route(RouteDecl {
                name,
                span,
                method: None,
                path: None,
                responds: None,
            }),
            _ => return Err(("E0001", "unknown top-level statement")),
        };
        Ok((item, is_block))
    }

    fn named(text: &str) -> Result<String, ParseError> {
        if is_name(text) {
            Ok(text.to_owned())
        } else {
            Err(("E0001", "expected an identifier"))
        }
    }

    fn typed(text: &str) -> Result<(String, TypeRef), ParseError> {
        let Some((name, ty)) = text.split_once(" of type") else {
            return Err(("E0001", "expected `NAME of type TYPE`"));
        };
        let name = named(name.trim())?;
        if !ty.is_empty() && !ty.starts_with(char::is_whitespace) {
            return Err(("E0001", "expected `of type TYPE`"));
        }
        let ty = parse_type(ty).ok_or(("E0004", "malformed type"))?;
        Ok((name, ty))
    }

    enum Subblock<'a> {
        Text(&'a mut Vec<String>),
        Body(&'a mut Vec<Stmt>),
    }

    fn subblock<'a>(item: &'a mut Item, label: &str) -> Option<Subblock<'a>> {
        match item {
            Item::Service(service) => match label {
                "requires" => Some(Subblock::Text(&mut service.requires)),
                "ensures" | "ensures on success" => Some(Subblock::Text(&mut service.ensures)),
                "allowed effects" => Some(Subblock::Text(&mut service.allowed_effects)),
                "forbidden effects" => Some(Subblock::Text(&mut service.forbidden_effects)),
                _ => None,
            },
            Item::Operation(operation) => match label {
                "requires" => Some(Subblock::Text(&mut operation.requires)),
                "ensures" => Some(Subblock::Text(&mut operation.ensures)),
                "body" => Some(Subblock::Body(&mut operation.body)),
                _ => None,
            },
            _ => None,
        }
    }

    fn body_statement(line: &Line<'_>) -> Result<(Stmt, bool), ParseError> {
        let keyword = line
            .text
            .split(|ch: char| ch.is_whitespace() || ch == ':' || ch == '.')
            .next()
            .unwrap_or("");
        if matches!(keyword, "if" | "for" | "while") {
            let stem = line
                .text
                .strip_suffix(':')
                .ok_or(("E0002", "control-flow header must end with `:`"))?;
            let rest = stem.get(keyword.len()..).unwrap_or("").trim();
            let stmt = match keyword {
                "if" => Stmt::If {
                    cond: parse_expr(rest).ok_or(("E0004", "malformed expression"))?,
                    then: Vec::new(),
                    else_: Vec::new(),
                },
                "while" => Stmt::While {
                    cond: parse_expr(rest).ok_or(("E0004", "malformed expression"))?,
                    body: Vec::new(),
                },
                "for" => {
                    let mut offset = 0;
                    let var = expr_name(rest, &mut offset)
                        .ok_or(("E0004", "expected `for NAME in EXPR:`"))?;
                    let tail = rest.get(offset..).unwrap_or("");
                    if !tail.starts_with(char::is_whitespace) {
                        return Err(("E0004", "expected `for NAME in EXPR:`"));
                    }
                    let iter = tail
                        .trim_start()
                        .strip_prefix("in")
                        .filter(|tail| tail.starts_with(char::is_whitespace))
                        .ok_or(("E0004", "expected `for NAME in EXPR:`"))?;
                    Stmt::For {
                        var: var.to_owned(),
                        iter: parse_expr(iter.trim()).ok_or(("E0004", "malformed expression"))?,
                        body: Vec::new(),
                    }
                }
                _ => return Err(("E0001", "unknown body statement")),
            };
            return Ok((stmt, true));
        }
        let stem = line
            .text
            .strip_suffix('.')
            .ok_or(("E0002", "body statement must end with `.`"))?
            .trim_end();
        let stmt = match keyword {
            "let" => {
                let mut rest = stem.get(keyword.len()..).unwrap_or("").trim();
                let mut mutable = false;
                if let Some(tail) = rest
                    .strip_prefix("mut")
                    .filter(|tail| tail.starts_with(char::is_whitespace))
                {
                    mutable = true;
                    rest = tail.trim_start();
                }
                let (name, expr) = rest
                    .split_once('=')
                    .ok_or(("E0004", "expected `let [mut] NAME = EXPR`"))?;
                if !is_name(name.trim()) {
                    return Err(("E0004", "expected a binding name"));
                }
                if expr.trim_start().starts_with('=') {
                    return Err(("E0004", "malformed expression"));
                }
                Stmt::Let {
                    name: name.trim().to_owned(),
                    mutable,
                    expr: parse_expr(expr.trim()).ok_or(("E0004", "malformed expression"))?,
                }
            }
            "set" => {
                let rest = stem.get(keyword.len()..).unwrap_or("").trim();
                let (name, expr) = rest
                    .split_once('=')
                    .ok_or(("E0004", "expected `set NAME = EXPR`"))?;
                if !is_name(name.trim()) {
                    return Err(("E0004", "expected a binding name"));
                }
                if expr.trim_start().starts_with('=') {
                    return Err(("E0004", "malformed expression"));
                }
                Stmt::Assign {
                    name: name.trim().to_owned(),
                    expr: parse_expr(expr.trim()).ok_or(("E0004", "malformed expression"))?,
                }
            }
            "return" => Stmt::Return(
                parse_expr(stem.get(keyword.len()..).unwrap_or("").trim())
                    .ok_or(("E0004", "malformed expression"))?,
            ),
            "break" | "continue" => {
                if stem != keyword {
                    return Err(("E0004", "loop control takes no operand"));
                }
                if keyword == "break" {
                    Stmt::Break
                } else {
                    Stmt::Continue
                }
            }
            _ => {
                let expr = parse_expr(stem).ok_or_else(|| {
                    let mut offset = 0;
                    let name = expr_name(stem, &mut offset);
                    let tail = stem.get(offset..).unwrap_or("").trim_start();
                    if name.is_some()
                        && !tail.starts_with([
                            '(', '.', '[', '+', '-', '*', '/', '%', '<', '>', '=', '!', '&', '|',
                        ])
                    {
                        ("E0001", "unknown body statement")
                    } else {
                        ("E0004", "malformed expression")
                    }
                })?;
                Stmt::ExprStmt(expr)
            }
        };
        Ok((stmt, false))
    }

    fn parse_body(lines: &[Line<'_>], diagnostics: &mut Vec<Diagnostic>) -> Vec<Stmt> {
        struct Frame {
            indent: usize,
            stmts: Vec<Stmt>,
            owner: Option<Stmt>,
            is_else: bool,
            else_allowed: bool,
        }
        impl Frame {
            fn append(&mut self, stmt: Stmt, allow_else: bool) {
                self.else_allowed = allow_else && matches!(stmt, Stmt::If { .. });
                self.stmts.push(stmt);
            }
        }
        fn close(frames: &mut Vec<Frame>) {
            let Some(mut frame) = frames.pop() else {
                return;
            };
            let Some(mut owner) = frame.owner.take() else {
                return;
            };
            match &mut owner {
                Stmt::If { then, else_, .. } => {
                    if frame.is_else {
                        *else_ = frame.stmts;
                    } else {
                        *then = frame.stmts;
                    }
                }
                Stmt::For { body, .. } | Stmt::While { body, .. } => *body = frame.stmts,
                _ => {}
            }
            if let Some(parent) = frames.last_mut() {
                parent.append(owner, !frame.is_else);
            }
        }
        let Some(first) = lines.first() else {
            return Vec::new();
        };
        let mut frames = vec![Frame {
            indent: first.indent,
            stmts: Vec::new(),
            owner: None,
            is_else: false,
            else_allowed: false,
        }];
        for (index, line) in lines.iter().enumerate() {
            while frames.len() > 1
                && frames
                    .last()
                    .is_some_and(|frame| line.indent < frame.indent)
            {
                close(&mut frames);
            }
            let Some(frame) = frames.last_mut() else {
                break;
            };
            if line.indent != frame.indent {
                diagnostics.push(
                    line.diagnostic("E0003", "body statements must have matching indentation"),
                );
                continue;
            }
            let is_else = line.text == "else" || line.text == "else." || line.text == "else:";
            let parsed = if is_else {
                if line.text != "else:" {
                    Err(("E0002", "else header must end with `:`"))
                } else if !frame.else_allowed {
                    Err((
                        "E0001",
                        "else must follow an if block at the same indentation",
                    ))
                } else {
                    frame.else_allowed = false;
                    match frame.stmts.pop() {
                        Some(stmt) => Ok((stmt, true)),
                        None => Err(("E0001", "else must follow an if block")),
                    }
                }
            } else {
                body_statement(line)
            };
            match parsed {
                Ok((stmt, block)) => {
                    if block {
                        if let Some(child) = lines
                            .get(index + 1)
                            .filter(|next| next.indent > line.indent)
                        {
                            frames.push(Frame {
                                indent: child.indent,
                                stmts: Vec::new(),
                                owner: Some(stmt),
                                is_else,
                                else_allowed: false,
                            });
                        } else {
                            diagnostics
                                .push(line.diagnostic("E0005", "body block must not be empty"));
                            frame.append(stmt, !is_else);
                        }
                    } else {
                        frame.append(stmt, true);
                    }
                }
                Err((code, message)) => {
                    frame.else_allowed = false;
                    diagnostics.push(line.diagnostic(code, message));
                }
            }
        }
        while frames.len() > 1 {
            close(&mut frames);
        }
        frames.pop().map_or_else(Vec::new, |frame| frame.stmts)
    }

    fn statement(item: &mut Item, line: &Line<'_>) -> Result<Option<&'static str>, ParseError> {
        let stem = line
            .text
            .strip_suffix('.')
            .or_else(|| line.text.strip_suffix(':'))
            .unwrap_or(line.text)
            .trim_end();
        let label = match stem {
            "requires" => Some("requires"),
            "ensures" => Some("ensures"),
            "ensures on success" => Some("ensures on success"),
            "allowed effects" => Some("allowed effects"),
            "forbidden effects" => Some("forbidden effects"),
            "body" => Some("body"),
            _ => None,
        };
        if let Some(label) = label {
            if subblock(item, label).is_some() {
                return if line.text.ends_with(':') {
                    Ok(Some(label))
                } else {
                    Err(("E0002", "sub-block header must end with `:`"))
                };
            }
        }
        let prefixes: &[&str] = match item {
            Item::Entity(_) => &["has ", "invariant ", "layout"],
            Item::Enum(_) => &[""],
            Item::Layer(_) => &["owns ", "may depend on ", "must not depend on "],
            Item::Service(_) => &["belongs to ", "implements ", "execution must be atomic"],
            Item::Operation(_) => &[
                "accepts ",
                "returns",
                "effects:",
                "responds with ",
                "exports",
                "imports",
            ],
            Item::Module(_) => &[
                "belongs to ",
                "owns ",
                "may read ",
                "may modify ",
                "cannot modify ",
                "forbids ",
                "implements ",
            ],
            Item::Server(_) => &["listens on port ", "speaks "],
            Item::Route(_) => &["handles ", "responds with "],
            Item::Application { .. } | Item::Use { .. } => &[],
        };
        if !prefixes.iter().any(|prefix| stem.starts_with(prefix)) {
            return Err(("E0001", "unknown statement in declaration body"));
        }
        let Some(text) = line.text.strip_suffix('.') else {
            return Err(("E0002", "statement must end with `.`"));
        };
        let text = text.trim_end();
        match item {
            Item::Entity(entity) => {
                if let Some(rest) = text.strip_prefix("has ") {
                    let (name, ty) = typed(rest)?;
                    entity.fields.push(FieldDecl {
                        name,
                        ty,
                        span: line.span(),
                    });
                } else if let Some(rest) = text.strip_prefix("invariant ") {
                    if rest.trim().is_empty() {
                        return Err(("E0001", "invariant text must not be empty"));
                    }
                    entity.invariants.push(rest.trim().to_owned());
                } else if text.starts_with("layout") {
                    if text != "layout \"C\"" {
                        return Err(("E0004", "expected `layout \"C\"`"));
                    }
                    if entity.c_layout {
                        return Err(("E0004", "duplicate layout clause"));
                    }
                    entity.c_layout = true;
                } else {
                    return Err(("E0001", "unknown entity statement"));
                }
            }
            Item::Enum(declaration) => declaration.variants.push(named(text)?),
            Item::Layer(layer) => {
                let rule = if let Some(rest) = text.strip_prefix("owns ") {
                    LayerRule::Owns {
                        name: named(rest.trim())?,
                        span: line.span(),
                    }
                } else if let Some(rest) = text.strip_prefix("may depend on ") {
                    LayerRule::MayDependOn {
                        target: named(rest.trim())?,
                        span: line.span(),
                    }
                } else if let Some(rest) = text.strip_prefix("must not depend on ") {
                    let (target, direct_only) = match rest.strip_suffix(" directly") {
                        Some(target) => (target, true),
                        None => (rest, false),
                    };
                    LayerRule::MustNotDependOn {
                        target: named(target.trim())?,
                        direct_only,
                        span: line.span(),
                    }
                } else {
                    return Err(("E0001", "unknown layer statement"));
                };
                layer.rules.push(rule);
            }
            Item::Service(service) => {
                if let Some(rest) = text.strip_prefix("belongs to ") {
                    service.belongs_to = Some(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("implements ") {
                    service.implements.push(named(rest.trim())?);
                } else if text == "execution must be atomic" {
                    service.atomic = true;
                } else {
                    return Err(("E0001", "unknown service statement"));
                }
            }
            Item::Operation(operation) => {
                if let Some(rest) = text.strip_prefix("accepts ") {
                    let (name, ty) = typed(rest)?;
                    operation.accepts.push(ParamDecl { name, ty });
                } else if text == "returns" {
                    return Err(("E0004", "malformed type"));
                } else if let Some(rest) = text.strip_prefix("returns ") {
                    let ty = parse_type(rest).ok_or(("E0004", "malformed type"))?;
                    if let Some(previous) = operation.returns.replace(ty) {
                        discard_type(previous);
                    }
                } else if let Some(rest) = text.strip_prefix("effects:") {
                    let effects = rest
                        .split(',')
                        .map(|effect| named(effect.trim()))
                        .collect::<Result<Vec<_>, _>>()?;
                    operation.effects.extend(effects);
                } else if let Some(rest) = text.strip_prefix("responds with ") {
                    let body = rest.trim();
                    if body.starts_with('"') && body.ends_with('"') && body.len() >= 2 {
                        let literal = unescape(&body[1..body.len() - 1])
                            .ok_or(("E0004", "malformed string escape"))?;
                        operation.responds_literal = Some(literal.clone());
                        operation.body.push(Stmt::Return(Expr::Lit(literal)));
                    } else {
                        return Err(("E0001", "expected `responds with \"literal\"`"));
                    }
                } else if let Some(rest) = text
                    .strip_prefix("exports")
                    .or_else(|| text.strip_prefix("imports"))
                {
                    let imported = text.starts_with("imports");
                    let expected = if imported {
                        "expected `imports \"C\" as \"symbol\"`"
                    } else {
                        "expected `exports \"C\" as \"symbol\"`"
                    };
                    if !rest.starts_with([' ', '\t']) {
                        return Err(("E0004", expected));
                    }
                    let rest = rest.trim_start();
                    let abi = rest.strip_prefix('"').ok_or(("E0004", expected))?;
                    let end = abi.find('"').ok_or(("E0004", expected))?;
                    if &abi[..end] != "C" {
                        return Err(("E0004", "unknown C linkage ABI (only \"C\" is supported)"));
                    }
                    let after = &abi[end + 1..];
                    if !after.starts_with([' ', '\t']) {
                        return Err(("E0004", expected));
                    }
                    let after = after.trim_start();
                    let symbol = after.strip_prefix("as").ok_or(("E0004", expected))?;
                    if !symbol.starts_with([' ', '\t']) {
                        return Err(("E0004", expected));
                    }
                    let symbol = symbol.trim_start();
                    let symbol = symbol.strip_prefix('"').ok_or(("E0004", expected))?;
                    let end = symbol.find('"').ok_or(("E0004", expected))?;
                    if !symbol[end + 1..].is_empty() {
                        return Err(("E0004", expected));
                    }
                    let symbol = &symbol[..end];
                    if !is_name(symbol) {
                        return Err(("E0004", "invalid C linkage symbol"));
                    }
                    if operation.c_export.is_some() || operation.c_import.is_some() {
                        return Err(("E0004", "duplicate or conflicting C linkage clause"));
                    }
                    if imported {
                        operation.c_import = Some(symbol.to_owned());
                    } else {
                        operation.c_export = Some(symbol.to_owned());
                    }
                } else {
                    return Err(("E0001", "unknown operation statement"));
                }
            }
            Item::Server(server) => {
                if let Some(rest) = text.strip_prefix("listens on port ") {
                    let digits = rest.trim();
                    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
                        return Err(("E0004", "port must be digits"));
                    }
                    match digits.parse::<u16>() {
                        Ok(port) => server.port = Some(port),
                        Err(_) => return Err(("E0004", "port must be 0-65535")),
                    }
                } else if let Some(rest) = text.strip_prefix("speaks ") {
                    if rest.trim().is_empty() {
                        return Err(("E0001", "version must not be empty"));
                    }
                    server.http_version = Some(rest.trim().to_owned());
                } else {
                    return Err(("E0001", "unknown server statement"));
                }
            }
            Item::Route(route) => {
                if let Some(rest) = text.strip_prefix("handles ") {
                    let mut parts = rest.split_whitespace();
                    let method = parts.next().unwrap_or("");
                    let path = parts.next().unwrap_or("");
                    if parts.next().is_some() || method.is_empty() || path.is_empty() {
                        return Err(("E0001", "expected `handles METHOD PATH`"));
                    }
                    if method != "GET" {
                        return Err(("E0001", "only GET is supported"));
                    }
                    route.method = Some(RouteMethod::Get);
                    route.path = Some(path.to_owned());
                } else if let Some(rest) = text.strip_prefix("responds with ") {
                    let body = rest.trim();
                    if body == "Text." || body == "Text" {
                        route.responds = Some(RespondsKind::Text);
                    } else if body.starts_with('"') && body.ends_with('"') && body.len() >= 2 {
                        let literal = unescape(&body[1..body.len() - 1])
                            .ok_or(("E0004", "malformed string escape"))?;
                        route.responds = Some(RespondsKind::Literal(literal));
                    } else if let Some(param) = body
                        .strip_prefix("param ")
                        .or_else(|| body.strip_prefix("with "))
                    {
                        route.responds = Some(RespondsKind::Param(named(param.trim())?));
                    } else {
                        return Err((
                            "E0001",
                            "expected `responds with Text`, a literal, or param NAME",
                        ));
                    }
                } else {
                    return Err(("E0001", "unknown route statement"));
                }
            }
            Item::Module(module) => {
                if let Some(rest) = text.strip_prefix("belongs to ") {
                    module.belongs_to = Some(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("owns ") {
                    module.owns.push(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("may read ") {
                    module.may_read.push(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("may modify ") {
                    module.may_modify.push(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("cannot modify ") {
                    module.cannot_modify.push(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("forbids ") {
                    module.forbids.push(named(rest.trim())?);
                } else if let Some(rest) = text.strip_prefix("implements ") {
                    module.implements.push(named(rest.trim())?);
                } else {
                    return Err(("E0001", "unknown module statement"));
                }
            }
            Item::Application { .. } => {
                return Err(("E0001", "application does not have a body"));
            }
            Item::Use { .. } => {
                return Err(("E0001", "use does not have a body"));
            }
        }
        Ok(None)
    }

    let lines: Vec<_> = _source
        .lines()
        .enumerate()
        .filter_map(|(index, raw)| {
            let mut quoted = false;
            let mut escaped = false;
            let comment = raw
                .char_indices()
                .find_map(|(offset, ch)| {
                    if ch == '#' && !quoted {
                        return Some(offset);
                    }
                    if ch == '"' && !escaped {
                        quoted = !quoted;
                    }
                    escaped = quoted && ch == '\\' && !escaped;
                    None
                })
                .unwrap_or(raw.len());
            let content = raw.get(..comment).unwrap_or("").trim_end();
            let mut indent = 0;
            let text = content.trim_start_matches(|ch| match ch {
                ' ' => {
                    indent += 1;
                    true
                }
                '\t' => {
                    indent += 4;
                    true
                }
                _ => false,
            });
            (!text.is_empty()).then_some(Line {
                number: index + 1,
                indent,
                text,
            })
        })
        .collect();
    let mut file = SalFile::default();
    let mut diagnostics = Vec::new();
    let mut index = 0;
    while let Some(line) = lines.get(index) {
        if line.indent != 0 {
            diagnostics
                .push(line.diagnostic("E0003", "top-level headers must have no indentation"));
            index += 1;
            continue;
        }
        let mut end = index + 1;
        while lines.get(end).is_some_and(|next| next.indent > 0) {
            end += 1;
        }
        let (mut item, is_block) = match header(line) {
            Ok(header) => header,
            Err((code, message)) => {
                diagnostics.push(line.diagnostic(code, message));
                index = end;
                continue;
            }
        };
        index += 1;
        if !is_block {
            let complaint = match &item {
                Item::Use { .. } => "use statement cannot have a body",
                _ => "application statement cannot have a body",
            };
            while index < end {
                diagnostics.push(lines[index].diagnostic("E0003", complaint));
                index += 1;
            }
        } else if index == end {
            diagnostics.push(line.diagnostic("E0005", "declaration body must not be empty"));
        } else {
            let body_indent = lines[index].indent;
            while index < end {
                let body_line = &lines[index];
                if body_line.indent != body_indent {
                    diagnostics.push(body_line.diagnostic(
                        "E0003",
                        "statement indentation must match its declaration body",
                    ));
                    index += 1;
                    continue;
                }
                match statement(&mut item, body_line) {
                    Ok(Some(label)) => {
                        index += 1;
                        let start = index;
                        if let Some(Subblock::Body(target)) = subblock(&mut item, label) {
                            while index < end && lines[index].indent > body_indent {
                                index += 1;
                            }
                            target.extend(parse_body(&lines[start..index], &mut diagnostics));
                            if start == index {
                                diagnostics.push(
                                    body_line.diagnostic("E0005", "sub-block must not be empty"),
                                );
                            }
                            continue;
                        }
                        let child_indent = lines
                            .get(index)
                            .filter(|_| index < end)
                            .map_or(body_indent, |child| child.indent);
                        while index < end && lines[index].indent > body_indent {
                            let child = &lines[index];
                            if child.indent != child_indent {
                                diagnostics.push(child.diagnostic(
                                    "E0003",
                                    "sub-block items must have matching indentation",
                                ));
                            } else if let Some(value) = child.text.strip_suffix('.') {
                                let value = value.trim();
                                if value.is_empty() {
                                    diagnostics.push(
                                        child.diagnostic(
                                            "E0001",
                                            "sub-block item must not be empty",
                                        ),
                                    );
                                } else if let Some(Subblock::Text(target)) =
                                    subblock(&mut item, label)
                                {
                                    target.push(value.to_owned());
                                }
                            } else {
                                diagnostics.push(
                                    child.diagnostic("E0002", "sub-block item must end with `.`"),
                                );
                            }
                            index += 1;
                        }
                        if start == index {
                            diagnostics
                                .push(body_line.diagnostic("E0005", "sub-block must not be empty"));
                        }
                    }
                    Ok(None) => index += 1,
                    Err((code, message)) => {
                        diagnostics.push(body_line.diagnostic(code, message));
                        let label = body_line
                            .text
                            .strip_suffix('.')
                            .or_else(|| body_line.text.strip_suffix(':'))
                            .unwrap_or(body_line.text)
                            .trim_end();
                        let is_subblock = subblock(&mut item, label).is_some();
                        index += 1;
                        // A malformed sub-block must not turn its children into
                        // unrelated body statements.
                        if is_subblock {
                            while index < end && lines[index].indent > body_indent {
                                index += 1;
                            }
                        }
                    }
                }
            }
        }
        file.items.push(item);
    }
    (file, diagnostics)
}

pub fn format_diagnostic(_d: &Diagnostic, _source: &str) -> String {
    let source_line = _source
        .lines()
        .nth(_d.span.line.saturating_sub(1))
        .unwrap_or("");
    let source_line = if source_line.contains('\t') {
        std::borrow::Cow::Owned(source_line.replace('\t', "    "))
    } else {
        std::borrow::Cow::Borrowed(source_line)
    };
    let source_width = source_line.chars().count();
    let padding = _d.span.col.saturating_sub(1).min(source_width);
    let available = source_width.saturating_sub(padding).max(1);
    let width = if _d.span.end_line == _d.span.line {
        _d.span
            .end_col
            .saturating_sub(_d.span.col)
            .max(1)
            .min(available)
    } else {
        available
    };
    let mut rendered = format!(
        "{}[{}]: {}\n --> {}:{}\n |\n   {}\n | ",
        _d.severity, _d.code, _d.message, _d.span.line, _d.span.col, source_line,
    );
    rendered.extend(std::iter::repeat_n(' ', padding));
    rendered.extend(std::iter::repeat_n('^', width));
    if let Some(suggestion) = &_d.suggestion {
        rendered.push(' ');
        rendered.push_str(suggestion);
    }
    rendered
}

#[cfg(test)]
mod c_abi_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_typed_operation_bodies() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        let n = -4.\n        let pi = 3.14.\n        let ready = true.\n        emit(\"hi,#.\", n + 2 - 1, item.name, rows[0]).\n        if ready:\n            return \"yes\".\n        else:\n            if false:\n                return \"no\".\n        for row in rows:\n            emit(row).\n        while ready:\n            emit().\n        return n == 2 != false.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.body.len(), 8);
        assert_eq!(
            operation.body[0],
            Stmt::Let {
                name: "n".into(),
                mutable: false,
                expr: Expr::Int(-4)
            }
        );
        assert!(
            matches!(&operation.body[1], Stmt::Let { name, expr: Expr::Float(value), .. }
            if name == "pi" && value.to_string() == "3.14")
        );
    }

    #[test]
    fn parses_mutable_assign_new_operators_and_grouping() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        let mut n = 1.\n        set n = (n + 2) * 3 - 4 / 2 % 3.\n        return a + b * c.\n        return a < b == c >= d != e.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.body.len(), 4);
        assert_eq!(
            operation.body[0],
            Stmt::Let {
                name: "n".into(),
                mutable: true,
                expr: Expr::Int(1),
            }
        );
        let Stmt::Assign { name, expr } = &operation.body[1] else {
            panic!("expected assignment");
        };
        assert_eq!(name, "n");
        let Expr::BinOp {
            op: BinOp::Sub,
            left,
            right,
        } = expr
        else {
            panic!("expected top-level subtraction, got {expr:?}");
        };
        assert!(matches!(left.as_ref(), Expr::BinOp { op: BinOp::Mul, .. }));
        assert!(matches!(right.as_ref(), Expr::BinOp { op: BinOp::Rem, .. }));
        let Expr::BinOp {
            op: BinOp::Mul,
            left,
            ..
        } = left.as_ref()
        else {
            panic!("expected product");
        };
        assert!(matches!(left.as_ref(), Expr::BinOp { op: BinOp::Add, .. }));
        let Stmt::Return(add) = &operation.body[2] else {
            panic!("expected return");
        };
        let Expr::BinOp {
            op: BinOp::Add,
            right,
            ..
        } = add
        else {
            panic!("expected top-level addition, got {add:?}");
        };
        assert!(matches!(right.as_ref(), Expr::BinOp { op: BinOp::Mul, .. }));
        let Stmt::Return(chain) = &operation.body[3] else {
            panic!("expected return");
        };
        // `<`/`<=`/`>`/`>=` bind tighter than `==`/`!=`; `==`/`!=` are
        // left-associative, so `a < b == c >= d != e` parses as
        // `((a < b) == (c >= d)) != e`.
        let Expr::BinOp {
            op: BinOp::Ne,
            left,
            right,
        } = chain
        else {
            panic!("expected top-level inequality, got {chain:?}");
        };
        let Expr::BinOp {
            op: BinOp::Eq,
            left,
            right: mid,
        } = left.as_ref()
        else {
            panic!("expected chained equality, got {left:?}");
        };
        assert!(matches!(left.as_ref(), Expr::BinOp { op: BinOp::Lt, .. }));
        assert!(matches!(mid.as_ref(), Expr::BinOp { op: BinOp::Ge, .. }));
        assert!(matches!(right.as_ref(), Expr::Var(_)));
    }

    #[test]
    fn boolean_precedence_preserves_postfix_and_grouped_negation() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        return !f(1)[2].ready && a < b == true || !!done.\n        return !(a || b) != false.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        let Stmt::Return(Expr::BinOp {
            op: BinOp::Or,
            left,
            right,
        }) = &operation.body[0]
        else {
            panic!("expected disjunction");
        };
        assert!(matches!(right.as_ref(), Expr::Not(value)
            if matches!(value.as_ref(), Expr::Not(inner)
                if matches!(inner.as_ref(), Expr::Var(name) if name == "done"))));
        let Expr::BinOp {
            op: BinOp::And,
            left,
            right,
        } = left.as_ref()
        else {
            panic!("expected conjunction");
        };
        assert!(matches!(left.as_ref(), Expr::Not(value)
            if matches!(value.as_ref(), Expr::Field { base, field }
                if field == "ready" && matches!(base.as_ref(), Expr::Index { base, index }
                    if **index == Expr::Int(2) && matches!(base.as_ref(), Expr::Call { name, args }
                        if name == "f" && args == &[Expr::Int(1)])))));
        assert!(
            matches!(right.as_ref(), Expr::BinOp { op: BinOp::Eq, left, right }
            if **right == Expr::Bool(true) && matches!(left.as_ref(), Expr::BinOp { op: BinOp::Lt, .. }))
        );
        let Stmt::Return(Expr::BinOp {
            op: BinOp::Ne,
            left,
            right,
        }) = &operation.body[1]
        else {
            panic!("expected inequality");
        };
        assert_eq!(**right, Expr::Bool(false));
        assert!(matches!(left.as_ref(), Expr::Not(inner)
            if matches!(inner.as_ref(), Expr::BinOp { op: BinOp::Or, .. })));
    }

    #[test]
    fn rejects_malformed_grouping_let_set_and_use() {
        for source in [
            "operation Run:\n    body:\n        let mut = 1.\n        let good = 1.\n",
            "operation Run:\n    body:\n        let mut n 1.\n        let good = 1.\n",
            "operation Run:\n    body:\n        let n = (1 + 2.\n        let good = 1.\n",
            "operation Run:\n    body:\n        let n = ().\n        let good = 1.\n",
            "operation Run:\n    body:\n        let n = 1 +.\n        let good = 1.\n",
            "use \"ok/relative.sal\".\noperation Next:\n    returns Int.\n",
        ] {
            let (file, diagnostics) = parse(source);
            if source.starts_with("use ") {
                assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
                let Item::Use { path, .. } = &file.items[0] else {
                    panic!("expected use");
                };
                assert_eq!(path, "ok/relative.sal");
                continue;
            }
            assert_eq!(diagnostics.len(), 1, "{source}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "E0004", "{source}");
            let Item::Operation(operation) = &file.items[0] else {
                panic!("expected operation");
            };
            assert_eq!(
                operation.body,
                [Stmt::Let {
                    name: "good".into(),
                    mutable: false,
                    expr: Expr::Int(1),
                }],
                "{source}"
            );
        }
        for source in [
            "use \"\".\n",
            "use \"a\" \"b\".\n",
            "use \"a.sal\" extra.\n",
            "use a.sal.\n",
            "use \"unterminated.sal.\n",
            "use \"bad\0path.sal\".\n",
        ] {
            let (_, diagnostics) = parse(source);
            assert_eq!(diagnostics.len(), 1, "{source}: {diagnostics:?}");
            assert!(matches!(diagnostics[0].code, "E0002" | "E0004"), "{source}");
        }
    }

    #[test]
    fn legacy_typed_operation_body_tail() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        emit(\"hi,#.\", n + 2 - 1, item.name, rows[0]).\n        if ready:\n            return \"yes\".\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        let Stmt::ExprStmt(Expr::Call { name, args }) = &operation.body[0] else {
            panic!("expected effect call");
        };
        assert_eq!(name, "emit");
        assert_eq!(args[0], Expr::Lit("hi,#.".into()));
        assert!(matches!(&args[1], Expr::BinOp { op: BinOp::Sub, left, .. }
            if matches!(left.as_ref(), Expr::BinOp { op: BinOp::Add, .. })));
        assert!(matches!(&args[2], Expr::Field { base, field }
            if **base == Expr::Var("item".into()) && field == "name"));
        assert!(matches!(&args[3], Expr::Index { index, .. } if **index == Expr::Int(0)));
        assert!(matches!(&operation.body[1], Stmt::If { .. }));
    }

    #[test]
    fn legacy_response_is_the_same_return_node() {
        let (file, diagnostics) = parse(
            "operation Old:\n    responds with \"hello\".\noperation New:\n    body:\n        return \"hello\".\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let (Item::Operation(old), Item::Operation(new)) = (&file.items[0], &file.items[1]) else {
            panic!("expected operations");
        };
        assert_eq!(old.responds_literal.as_deref(), Some("hello"));
        assert_eq!(old.body, new.body);
        assert_eq!(new.responds_literal, None);
    }

    #[test]
    fn body_errors_recover_at_the_next_line() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        let x = 1\n        let y = broken(,).\n        unknown statement.\n        return \"ok\".\noperation Next:\n    returns Text.\n",
        );
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0002", "E0004", "E0001"]
        );
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.body, [Stmt::Return(Expr::Lit("ok".into()))]);
        assert_eq!(file.items.len(), 2);
    }

    #[test]
    fn nested_calls_indexes_and_precedence_are_structural() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        return outer(inner(), rows[lookup(1 + 2)].name) == a + b - c.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        let Stmt::Return(Expr::BinOp {
            op: BinOp::Eq,
            left,
            right,
        }) = &operation.body[0]
        else {
            panic!("expected comparison");
        };
        assert!(
            matches!(right.as_ref(), Expr::BinOp { op: BinOp::Sub, left, .. }
            if matches!(left.as_ref(), Expr::BinOp { op: BinOp::Add, .. }))
        );
        let Expr::Call { name, args } = left.as_ref() else {
            panic!("expected outer call");
        };
        assert_eq!(name, "outer");
        assert_eq!(
            args[0],
            Expr::Call {
                name: "inner".into(),
                args: Vec::new()
            }
        );
        assert!(matches!(&args[1], Expr::Field { base, field }
            if field == "name" && matches!(base.as_ref(), Expr::Index { .. })));
    }

    #[test]
    fn malformed_expressions_recover_without_losing_valid_bindings() {
        for expression in [
            "",
            "9223372036854775808",
            "-9223372036854775809",
            "3.14.5",
            "\"open",
            "f(,)",
            "f(1,)",
            "f(1",
            "f(1))",
            "rows[]",
            "rows[1",
            "rows[1,2]",
            "item.",
            "item.1",
            "1 +",
            "1 = 2",
            "é",
        ] {
            let source = format!(
                "operation Run:\n    body:\n        let broken = {expression}.\n        let good = 1.\n"
            );
            let (file, diagnostics) = parse(&source);
            assert_eq!(diagnostics.len(), 1, "{expression}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "E0004", "{expression}");
            let Item::Operation(operation) = &file.items[0] else {
                panic!("expected operation");
            };
            assert_eq!(
                operation.body,
                [Stmt::Let {
                    name: "good".into(),
                    mutable: false,
                    expr: Expr::Int(1)
                }]
            );
        }
    }

    #[test]
    fn malformed_deep_expressions_use_iterative_cleanup() {
        let nested = format!("{}1{}", "f(".repeat(20_000), ")".repeat(20_000));
        let chain = format!("1{}", " + 1".repeat(20_000));
        let negated = format!("{}true", "!".repeat(20_000));
        let source = format!(
            "operation Run:\n    body:\n        let bad = {nested} extra.\n        let bad = {chain} extra.\n        let bad = {negated} +.\n        let bad = f({negated},.\n        return 1.\n"
        );
        let (file, diagnostics) = parse(&source);
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0004"; 4]
        );
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.body, [Stmt::Return(Expr::Int(1))]);
    }

    #[test]
    fn nested_else_blocks_bind_to_the_matching_indent() {
        let (file, diagnostics) = parse(
            "operation Run:\n    body:\n        if true:\n            if false:\n                return 1.\n            else:\n                return 2.\n        else:\n            return 3.\n        return 4.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        let Stmt::If { then, else_, .. } = &operation.body[0] else {
            panic!("expected outer if");
        };
        assert_eq!(else_, &[Stmt::Return(Expr::Int(3))]);
        assert!(matches!(&then[0], Stmt::If { else_, .. }
            if else_ == &[Stmt::Return(Expr::Int(2))]));
        assert_eq!(operation.body[1], Stmt::Return(Expr::Int(4)));
    }

    #[test]
    fn body_headers_report_terminators_empty_blocks_and_orphan_else() {
        let (_, diagnostics) = parse(
            "operation Run:\n    body.\n        return 0.\n    body:\n        else:\n        if true.\n        while true:\n        return 1.\n        for row in rows.\n    returns Int.\n",
        );
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0002", "E0001", "E0002", "E0005", "E0002"]
        );
    }

    #[test]
    fn parses_every_declaration_and_statement() {
        let source = "\
application Shop.
entity Order:
    has id of type Id.
    has lines of type Map<Text, List<Line>>.
    invariant id is present.
enum State:
    Pending.
    Complete.
layer Domain:
    owns Order.
    may depend on Shared.
    must not depend on Web.
    must not depend on Storage directly.
service Checkout:
    belongs to Domain.
    implements PlaceOrder.
    requires:
        order exists.
    ensures:
        order is stored.
    ensures on success:
        receipt exists.
    execution must be atomic.
    allowed effects:
        persistence.
    forbidden effects:
        network.
operation PlaceOrder:
    accepts order of type Order.
    returns Result<Order, Error>.
    effects: persistence, clock.
    requires:
        order is valid.
    ensures:
        order is stored.
module Orders:
    belongs to Domain.
    owns Order.
    may read Catalog.
    may modify Order.
    cannot modify Catalog.
    forbids network.
    implements PlaceOrder.
";
        let (file, diagnostics) = parse(source);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        assert_eq!(file.items.len(), 7);
        let Item::Entity(entity) = &file.items[1] else {
            panic!("expected entity");
        };
        assert_eq!(entity.fields.len(), 2);
        assert_eq!(entity.invariants, ["id is present"]);
        assert_eq!(
            entity.fields[1].ty,
            TypeRef::Generic {
                name: "Map".into(),
                args: vec![
                    TypeRef::Named("Text".into()),
                    TypeRef::Generic {
                        name: "List".into(),
                        args: vec![TypeRef::Named("Line".into())],
                    },
                ],
            }
        );
        let Item::Service(service) = &file.items[4] else {
            panic!("expected service");
        };
        assert!(service.atomic);
        assert_eq!(service.requires, ["order exists"]);
        assert_eq!(service.ensures, ["order is stored", "receipt exists"]);
        assert_eq!(service.allowed_effects, ["persistence"]);
        assert_eq!(service.forbidden_effects, ["network"]);
        let Item::Operation(operation) = &file.items[5] else {
            panic!("expected operation");
        };
        assert_eq!(operation.effects, ["persistence", "clock"]);
        let Item::Module(module) = &file.items[6] else {
            panic!("expected module");
        };
        assert_eq!(module.cannot_modify, ["Catalog"]);
        assert_eq!(module.forbids, ["network"]);
    }

    #[test]
    fn recovers_from_each_diagnostic_category() {
        let source = "\
entity Broken:
    unknown statement.
    has missing of type Id
    has bad of type List<>.
        has nested of type Id.
    has good of type Id.
service Empty:
operation Good:
    returns Id.
";
        let (file, diagnostics) = parse(source);
        let codes: Vec<_> = diagnostics.iter().map(|d| d.code).collect();
        assert_eq!(codes, ["E0001", "E0002", "E0004", "E0003", "E0005"]);
        assert_eq!(diagnostics[0].span.line, 2);
        assert_eq!(diagnostics[0].span.col, 5);
        let Item::Entity(entity) = &file.items[0] else {
            panic!("expected entity");
        };
        assert_eq!(entity.fields.len(), 1);
        assert_eq!(entity.fields[0].name, "good");
        assert_eq!(file.items.len(), 3);
    }

    #[test]
    fn handles_tabs_comments_and_empty_subblocks() {
        let source = "# comment\nservice S: # header\n\trequires:\n\tensures:\n\t\tvalid. # item\n\tallowed effects:\n\t\tio.\n";
        let (file, diagnostics) = parse(source);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "E0005");
        assert_eq!(diagnostics[0].span.line, 3);
        let Item::Service(service) = &file.items[0] else {
            panic!("expected service");
        };
        assert_eq!(service.ensures, ["valid"]);
        assert_eq!(service.allowed_effects, ["io"]);
    }

    #[test]
    fn rejects_malformed_types_without_losing_following_statements() {
        for ty in [
            "",
            "9Id",
            "Id extra",
            "List<>",
            "List<Id,>",
            "List<,Id>",
            "List<Id",
            "Id>",
            "A<B>>",
            "A<B C>",
            "A<B><C>",
            "é",
        ] {
            let source =
                format!("entity E:\n    has bad of type {ty}.\n    has good of type Id.\n");
            let (file, diagnostics) = parse(&source);
            assert_eq!(diagnostics.len(), 1, "{ty}: {diagnostics:?}");
            assert_eq!(diagnostics[0].code, "E0004", "{ty}");
            let Item::Entity(entity) = &file.items[0] else {
                panic!("expected entity");
            };
            assert_eq!(entity.fields.len(), 1);
        }
    }

    #[test]
    fn rejects_deep_malformed_types_without_recursive_cleanup() {
        let nested = format!("{}Id{}", "List<".repeat(20_000), ">".repeat(20_000));
        let source = format!(
            "operation Op:\n    returns {nested} extra.\n    returns Outer<{nested},>.\n    returns {nested}.\n    returns Id.\n"
        );
        let (file, diagnostics) = parse(&source);
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0004", "E0004"]
        );
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.returns, Some(TypeRef::Named("Id".into())));
    }

    #[test]
    fn diagnoses_header_and_subblock_terminators() {
        let (_, diagnostics) = parse(
            "entity Wrong.\n    has x of type Id.\nservice S:\n    requires.\n        valid.\n    implements Op\napplication App:\n",
        );
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0002", "E0002", "E0002", "E0002"]
        );
    }

    #[test]
    fn renders_diagnostics_with_source_and_suggestions() {
        let diagnostic = Diagnostic {
            code: "E0001",
            severity: Severity::Error,
            message: "unknown statement".into(),
            span: Span {
                line: 2,
                col: 5,
                end_line: 2,
                end_col: 8,
            },
            suggestion: Some("use `owns NAME.`".into()),
        };
        assert_eq!(
            format_diagnostic(&diagnostic, "layer L:\n    bad.\n"),
            "error[E0001]: unknown statement\n --> 2:5\n |\n       bad.\n |     ^^^ use `owns NAME.`"
        );
    }

    #[test]
    fn renders_out_of_bounds_spans_without_unbounded_padding() {
        let diagnostic = Diagnostic {
            code: "E0001",
            severity: Severity::Warning,
            message: "bad span".into(),
            span: Span {
                line: usize::MAX,
                col: usize::MAX,
                end_line: usize::MAX,
                end_col: usize::MAX,
            },
            suggestion: None,
        };
        let rendered = format_diagnostic(&diagnostic, "");
        assert!(rendered.ends_with("\n |\n   \n | ^"));
    }

    #[test]
    fn parses_c_export_as_metadata_only() {
        let (file, diagnostics) = parse(
            "operation Double:\n    accepts n of type i64.\n    returns i64.\n    exports \"C\" as \"double_it\".\n    body:\n        return n.\n",
        );
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.name, "Double");
        assert_eq!(operation.c_export.as_deref(), Some("double_it"));
        assert_eq!(operation.accepts.len(), 1);
        // Exports are metadata: they never enter the executed body.
        assert_eq!(operation.body, [Stmt::Return(Expr::Var("n".into()))]);
    }

    #[test]
    fn rejects_duplicate_c_export() {
        let (file, diagnostics) =
            parse("operation F:\n    exports \"C\" as \"one\".\n    exports \"C\" as \"two\".\n");
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            ["E0004"]
        );
        let Item::Operation(operation) = &file.items[0] else {
            panic!("expected operation");
        };
        assert_eq!(operation.c_export.as_deref(), Some("one"));
    }

    #[test]
    fn rejects_bad_abi_and_symbol_c_exports() {
        for source in [
            "operation A:\n    exports \"Rust\" as \"good\".\n",
            "operation B:\n    exports \"C\" as \"bad name\".\n",
            "operation C:\n    exports \"C\" as \"9bad\".\n",
            "operation D:\n    exports \"C\".\n",
            "operation E:\n    exports \"C\" as \"good\" extra.\n",
        ] {
            let (file, diagnostics) = parse(source);
            assert_eq!(
                diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
                ["E0004"],
                "{source}"
            );
            let Item::Operation(operation) = &file.items[0] else {
                panic!("expected operation");
            };
            assert_eq!(operation.c_export, None, "{source}");
        }
    }
}
