//! Rust scaffold generator: deterministic SAL IR -> compilable Rust scaffolds +
//! architecture.json. This is a frontend/checker plus scaffold emitter, NOT a
//! behavioral compiler: service `execute` bodies and operation bodies are
//! `todo!()` stubs; requires/ensures/atomic/effects survive only as `///` doc
//! comments with no runtime enforcement. Behavior compilation and contract
//! enforcement at runtime are unimplemented.
//!
//! CONTRACT (do not change public signatures; implement bodies only):
//! - `emit_rust` returns files sorted by path, deterministic (sort items by name):
//!   `src/entities.rs`, `src/services.rs`, `src/operations.rs`, `src/lib.rs`,
//!   `architecture.json`.
//! - Type mapping: bool/String/ints/floats/usize/isize -> same; UUID -> String;
//!   Character -> char; Word -> String (no spaces, unchecked at runtime);
//!   Text -> String; Money<CUR> -> Money with `/// currency: CUR` doc;
//!   Option/Vec/Result map; entity/enum refs -> same name. Unknown names pass
//!   through verbatim (checker reports them; backend never fails).
//! - entities.rs: `#[allow(dead_code)]`, `pub struct Money { pub amount_minor:
//!   i64, pub currency: &'static str }`, one `pub struct` per entity (fields
//!   `pub name: Ty`), one `pub enum` per enum (variants verbatim).
//! - services.rs: `pub struct Name;` + impl with requires/ensures/atomic/effects
//!   as `///` docs (unenforced) and `pub fn execute(&self) ->
//!   Result<(), String> { todo!("SAL service Name not implemented") }`.
//! - operations.rs: `pub fn name(p: Ty, ...) -> Ret { todo!(...) }` with effects
//!   as docs; no-return -> `-> ()` omitted (plain `fn name(...)`).
//! - Executable routes/serve blocks (see sal_ir executable subset) are NOT
//!   emitted here; direct compilation to runnable programs lives in
//!   sal_backend_exec (new crate). This crate stays scaffold-only.
//! - lib.rs: `pub mod entities; pub mod operations; pub mod services;`
//! - architecture.json: hand-built JSON (no serde), `{"layers":{...},"services":
//!   {...},"modules":{...}}` with rules/effects; minimal escaping (`\` and `"`).
//! - Never panic on any IR input.

use sal_ir::Ir;
use sal_ir::TypeRef;
use sal_syntax::LayerRule;

#[derive(Debug, Clone)]
pub struct EmittedFile {
    pub path: String,
    pub content: String,
}

pub fn emit_rust(ir: &Ir) -> Vec<EmittedFile> {
    let mut files = vec![
        EmittedFile {
            path: "architecture.json".to_string(),
            content: emit_architecture_json(ir),
        },
        EmittedFile {
            path: "src/entities.rs".to_string(),
            content: emit_entities(ir),
        },
        EmittedFile {
            path: "src/lib.rs".to_string(),
            content: emit_lib_rs(),
        },
        EmittedFile {
            path: "src/operations.rs".to_string(),
            content: emit_operations(ir),
        },
        EmittedFile {
            path: "src/services.rs".to_string(),
            content: emit_services(ir),
        },
    ];
    files.sort_by(|a, b| a.path.cmp(&b.path));
    files
}

fn rust_ty(ty: &TypeRef) -> String {
    match ty {
        TypeRef::Named(name) => {
            if name == "UUID" {
                "String".to_string()
            } else if name == "Character" {
                "char".to_string()
            } else if name == "Word" || name == "Text" {
                "String".to_string()
            } else {
                name.clone()
            }
        }
        TypeRef::Generic { name, args } => {
            if name == "Money" {
                return "Money".to_string();
            }
            if args.is_empty() {
                return name.clone();
            }
            let mut out = String::new();
            out.push_str(name);
            out.push('<');
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&rust_ty(arg));
            }
            out.push('>');
            out
        }
    }
}

fn render_currency(ty: &TypeRef) -> String {
    match ty {
        TypeRef::Named(name) => name.clone(),
        TypeRef::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let mut out = String::new();
                out.push_str(name);
                out.push('<');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    out.push_str(&render_currency(arg));
                }
                out.push('>');
                out
            }
        }
    }
}

fn money_currencies(ty: &TypeRef, out: &mut Vec<String>) {
    if let TypeRef::Generic { name, args } = ty {
        if name == "Money" {
            if let Some(first) = args.first() {
                out.push(render_currency(first));
            }
        }
        for arg in args {
            money_currencies(arg, out);
        }
    }
}

fn emit_entities(ir: &Ir) -> String {
    let mut out = String::new();
    out.push_str("#[allow(dead_code)]\n\n");
    out.push_str("pub struct Money {\n");
    out.push_str("    pub amount_minor: i64,\n");
    out.push_str("    pub currency: &'static str,\n");
    out.push_str("}\n");
    let mut names: Vec<&String> = ir.entities.keys().collect();
    names.sort();
    for name in names {
        if let Some(entity) = ir.entities.get(name) {
            out.push_str("#[allow(dead_code)]\n");
            for invariant in &entity.invariants {
                out.push_str("/// invariant: ");
                out.push_str(invariant);
                out.push('\n');
            }
            out.push_str("pub struct ");
            out.push_str(name);
            out.push_str(" {\n");
            for field in &entity.fields {
                let mut currencies = Vec::new();
                money_currencies(&field.ty, &mut currencies);
                for currency in &currencies {
                    out.push_str("    /// currency: ");
                    out.push_str(currency);
                    out.push('\n');
                }
                out.push_str("    pub ");
                out.push_str(&field.name);
                out.push_str(": ");
                out.push_str(&rust_ty(&field.ty));
                out.push_str(",\n");
            }
            out.push_str("}\n");
        }
    }
    let mut enum_names: Vec<&String> = ir.enums.keys().collect();
    enum_names.sort();
    for name in enum_names {
        if let Some(en) = ir.enums.get(name) {
            out.push_str("#[allow(dead_code)]\n");
            out.push_str("pub enum ");
            out.push_str(name);
            out.push_str(" {\n");
            for variant in &en.variants {
                out.push_str("    ");
                out.push_str(variant);
                out.push_str(",\n");
            }
            out.push_str("}\n");
        }
    }
    out
}

fn emit_services(ir: &Ir) -> String {
    let mut out = String::new();
    out.push_str("#[allow(dead_code)]\n\n");
    let mut names: Vec<&String> = ir.services.keys().collect();
    names.sort();
    for name in names {
        if let Some(service) = ir.services.get(name) {
            out.push_str("pub struct ");
            out.push_str(name);
            out.push_str(";\n\n");
            out.push_str("impl ");
            out.push_str(name);
            out.push_str(" {\n");
            if let Some(belongs) = &service.belongs_to {
                out.push_str("    /// belongs to: ");
                out.push_str(belongs);
                out.push('\n');
            }
            if !service.implements.is_empty() {
                out.push_str("    /// implements: ");
                out.push_str(&service.implements.join(", "));
                out.push('\n');
            }
            for req in &service.requires {
                out.push_str("    /// requires: ");
                out.push_str(req);
                out.push('\n');
            }
            for ens in &service.ensures {
                out.push_str("    /// ensures: ");
                out.push_str(ens);
                out.push('\n');
            }
            if service.atomic {
                out.push_str("    /// atomic\n");
            }
            if !service.allowed_effects.is_empty() {
                out.push_str("    /// allowed effects: ");
                out.push_str(&service.allowed_effects.join(", "));
                out.push('\n');
            }
            if !service.forbidden_effects.is_empty() {
                out.push_str("    /// forbidden effects: ");
                out.push_str(&service.forbidden_effects.join(", "));
                out.push('\n');
            }
            out.push_str("    pub fn execute(&self) -> Result<(), String> {\n");
            out.push_str("        todo!(\"SAL service ");
            out.push_str(name);
            out.push_str(" not implemented\")\n");
            out.push_str("    }\n");
            out.push_str("}\n");
        }
    }
    out
}

fn emit_operations(ir: &Ir) -> String {
    let mut out = String::new();
    out.push_str("#[allow(dead_code)]\n\n");
    out.push_str("#[allow(unused_imports)]\n");
    out.push_str("use crate::entities::*;\n\n");
    let mut names: Vec<&String> = ir.operations.keys().collect();
    names.sort();
    for name in names {
        if let Some(op) = ir.operations.get(name) {
            let mut currencies = Vec::new();
            for param in &op.accepts {
                money_currencies(&param.ty, &mut currencies);
            }
            if let Some(ret) = &op.returns {
                money_currencies(ret, &mut currencies);
            }
            for currency in &currencies {
                out.push_str("/// currency: ");
                out.push_str(currency);
                out.push('\n');
            }
            for req in &op.requires {
                out.push_str("/// requires: ");
                out.push_str(req);
                out.push('\n');
            }
            for ens in &op.ensures {
                out.push_str("/// ensures: ");
                out.push_str(ens);
                out.push('\n');
            }
            if !op.effects.is_empty() {
                out.push_str("/// effects: ");
                out.push_str(&op.effects.join(", "));
                out.push('\n');
            }
            out.push_str("pub fn ");
            out.push_str(name);
            out.push('(');
            for (i, param) in op.accepts.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&param.name);
                out.push_str(": ");
                out.push_str(&rust_ty(&param.ty));
            }
            out.push(')');
            if let Some(ret) = &op.returns {
                out.push_str(" -> ");
                out.push_str(&rust_ty(ret));
            }
            out.push_str(" {\n");
            out.push_str("    todo!(\"SAL operation ");
            out.push_str(name);
            out.push_str(" not implemented\")\n");
            out.push_str("}\n");
        }
    }
    out
}

fn emit_lib_rs() -> String {
    "pub mod entities;\npub mod operations;\npub mod services;\n".to_string()
}

fn json_escape_into(out: &mut String, s: &str) {
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            _ => out.push(c),
        }
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    json_escape_into(&mut out, s);
    out.push('"');
    out
}

fn json_string_list(items: &[String]) -> String {
    let mut out = String::from("[");
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_string(item));
    }
    out.push(']');
    out
}

fn json_optional(value: &Option<String>) -> String {
    match value {
        Some(v) => json_string(v),
        None => "null".to_string(),
    }
}

fn emit_architecture_json(ir: &Ir) -> String {
    let mut out = String::from("{\"layers\":{");
    let mut layer_names: Vec<&String> = ir.layers.keys().collect();
    layer_names.sort();
    for (i, name) in layer_names.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_string(name));
        out.push(':');
        if let Some(layer) = ir.layers.get(*name) {
            let mut owns: Vec<String> = Vec::new();
            let mut may: Vec<String> = Vec::new();
            let mut must_not: Vec<String> = Vec::new();
            let mut must_not_direct: Vec<String> = Vec::new();
            for rule in &layer.rules {
                match rule {
                    LayerRule::Owns { name, .. } => owns.push(name.clone()),
                    LayerRule::MayDependOn { target, .. } => may.push(target.clone()),
                    LayerRule::MustNotDependOn {
                        target,
                        direct_only,
                        ..
                    } => {
                        if *direct_only {
                            must_not_direct.push(target.clone());
                        } else {
                            must_not.push(target.clone());
                        }
                    }
                }
            }
            out.push_str("{\"owns\":");
            out.push_str(&json_string_list(&owns));
            out.push_str(",\"may_depend_on\":");
            out.push_str(&json_string_list(&may));
            out.push_str(",\"must_not_depend_on\":");
            out.push_str(&json_string_list(&must_not));
            out.push_str(",\"must_not_depend_on_direct\":");
            out.push_str(&json_string_list(&must_not_direct));
            out.push('}');
        } else {
            out.push_str("{}");
        }
    }
    out.push_str("},\"services\":{");
    let mut service_names: Vec<&String> = ir.services.keys().collect();
    service_names.sort();
    for (i, name) in service_names.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_string(name));
        out.push(':');
        if let Some(service) = ir.services.get(*name) {
            out.push_str("{\"belongs_to\":");
            out.push_str(&json_optional(&service.belongs_to));
            out.push_str(",\"implements\":");
            out.push_str(&json_string_list(&service.implements));
            out.push_str(",\"requires\":");
            out.push_str(&json_string_list(&service.requires));
            out.push_str(",\"ensures\":");
            out.push_str(&json_string_list(&service.ensures));
            out.push_str(",\"atomic\":");
            out.push_str(if service.atomic { "true" } else { "false" });
            out.push_str(",\"allowed_effects\":");
            out.push_str(&json_string_list(&service.allowed_effects));
            out.push_str(",\"forbidden_effects\":");
            out.push_str(&json_string_list(&service.forbidden_effects));
            out.push('}');
        } else {
            out.push_str("{}");
        }
    }
    out.push_str("},\"modules\":{");
    let mut module_names: Vec<&String> = ir.modules.keys().collect();
    module_names.sort();
    for (i, name) in module_names.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push_str(&json_string(name));
        out.push(':');
        if let Some(module) = ir.modules.get(*name) {
            out.push_str("{\"belongs_to\":");
            out.push_str(&json_optional(&module.belongs_to));
            out.push_str(",\"owns\":");
            out.push_str(&json_string_list(&module.owns));
            out.push_str(",\"may_read\":");
            out.push_str(&json_string_list(&module.may_read));
            out.push_str(",\"may_modify\":");
            out.push_str(&json_string_list(&module.may_modify));
            out.push_str(",\"cannot_modify\":");
            out.push_str(&json_string_list(&module.cannot_modify));
            out.push_str(",\"forbids\":");
            out.push_str(&json_string_list(&module.forbids));
            out.push_str(",\"implements\":");
            out.push_str(&json_string_list(&module.implements));
            out.push('}');
        } else {
            out.push_str("{}");
        }
    }
    out.push_str("}}");
    out
}
