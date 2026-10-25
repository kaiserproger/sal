use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{error, is_primitive, sorted_entries, Diagnostic, Ir, TypeRef};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CAbiTarget {
    LinuxX86_64,
}

#[derive(Debug, Clone)]
pub struct CFieldLayout {
    pub name: String,
    pub offset: usize,
    pub ty: TypeRef,
}

#[derive(Debug, Clone)]
pub struct CRecordLayout {
    pub size: usize,
    pub align: usize,
    pub fields: Vec<CFieldLayout>,
}

fn scalar_layout(name: &str, target: CAbiTarget) -> Option<(usize, usize)> {
    let size = match (target, name) {
        (_, "bool" | "u8" | "i8") => 1,
        (_, "u16" | "i16") => 2,
        (_, "u32" | "i32") => 4,
        (CAbiTarget::LinuxX86_64, "u64" | "i64" | "usize" | "isize") => 8,
        _ => return None,
    };
    Some((size, size))
}

fn align_up(size: usize, align: usize) -> Option<usize> {
    size.checked_add(align - 1).map(|size| size & !(align - 1))
}

/// Computes natural C layouts without recursive traversal or host-dependent widths.
/// Invalid dependencies poison their containing records rather than supplying a
/// partial layout. Unmarked specification entities are not ABI-validated.
pub fn c_record_layouts(
    ir: &Ir,
    target: CAbiTarget,
) -> Result<BTreeMap<String, CRecordLayout>, Vec<Diagnostic>> {
    let mut layouts: BTreeMap<String, CRecordLayout> = BTreeMap::new();
    // 1 = visiting, 2 = finished (possibly invalid).
    let mut state: HashMap<&str, u8> = HashMap::new();
    let mut diagnostics = Vec::new();
    for (root, entity) in sorted_entries(&ir.entities) {
        if !entity.c_layout || state.contains_key(root.as_str()) {
            continue;
        }
        let mut pending = vec![(root.as_str(), false)];
        while let Some((name, finish)) = pending.pop() {
            let entity = &ir.entities[name];
            if !finish {
                match state.get(name) {
                    Some(1) => {
                        diagnostics.push(error(
                            "E2010",
                            format!("cyclic C record layout involving `{name}`"),
                            &entity.span,
                        ));
                        continue;
                    }
                    Some(_) => continue,
                    None => {}
                }
                state.insert(name, 1);
                pending.push((name, true));
                for field in entity.fields.iter().rev() {
                    if let TypeRef::Named(dependency) = &field.ty {
                        if !is_primitive(dependency)
                            && ir
                                .entities
                                .get(dependency)
                                .is_some_and(|entity| entity.c_layout)
                        {
                            pending.push((dependency, false));
                        }
                    }
                }
                continue;
            }
            state.insert(name, 2);
            let mut valid = true;
            if is_primitive(name) {
                diagnostics.push(error(
                    "E2010",
                    format!("C record `{name}` collides with a primitive type"),
                    &entity.span,
                ));
                valid = false;
            }
            if entity.fields.is_empty() {
                diagnostics.push(error(
                    "E2010",
                    format!("C record `{name}` must not be empty"),
                    &entity.span,
                ));
                valid = false;
            }
            let mut size = 0usize;
            let mut align = 1usize;
            let mut fields = Vec::with_capacity(entity.fields.len());
            let mut names = HashSet::new();
            for field in &entity.fields {
                if !names.insert(field.name.as_str()) {
                    diagnostics.push(error(
                        "E2010",
                        format!("duplicate field `{}` in C record `{name}`", field.name),
                        &field.span,
                    ));
                    valid = false;
                }
                let layout = match &field.ty {
                    TypeRef::Named(ty) => scalar_layout(ty, target)
                        .or_else(|| layouts.get(ty).map(|layout| (layout.size, layout.align))),
                    TypeRef::Generic { .. } => None,
                };
                let Some((field_size, field_align)) = layout else {
                    diagnostics.push(error(
                        "E2010",
                        format!("field `{}` in C record `{name}` requires a native integer, bool, or valid C record", field.name),
                        &field.span,
                    ));
                    valid = false;
                    continue;
                };
                let Some(offset) = align_up(size, field_align) else {
                    diagnostics.push(error(
                        "E2010",
                        format!("C record `{name}` layout overflows"),
                        &field.span,
                    ));
                    valid = false;
                    break;
                };
                let Some(end) = offset.checked_add(field_size) else {
                    diagnostics.push(error(
                        "E2010",
                        format!("C record `{name}` layout overflows"),
                        &field.span,
                    ));
                    valid = false;
                    break;
                };
                size = end;
                align = align.max(field_align);
                fields.push(CFieldLayout {
                    name: field.name.clone(),
                    offset,
                    ty: field.ty.clone(),
                });
            }
            let padded = align_up(size, align);
            if padded.is_none() {
                diagnostics.push(error(
                    "E2010",
                    format!("C record `{name}` layout overflows"),
                    &entity.span,
                ));
                valid = false;
            }
            if valid {
                layouts.insert(
                    name.to_owned(),
                    CRecordLayout {
                        size: padded.unwrap_or(size),
                        align,
                        fields,
                    },
                );
            }
        }
    }
    if diagnostics.is_empty() {
        Ok(layouts)
    } else {
        Err(diagnostics)
    }
}
