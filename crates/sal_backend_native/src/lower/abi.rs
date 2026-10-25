//! One integer-only SysV argument classifier, shared by callers and callees.
use sal_ir::CRecordLayout;
use std::collections::BTreeMap;

use super::Ty;

#[derive(Clone, Copy)]
pub(super) enum Place {
    Registers { first: usize, words: usize },
    Stack { offset: usize },
}

pub(super) fn record(layouts: &BTreeMap<String, CRecordLayout>, ty: Ty) -> Option<&CRecordLayout> {
    match ty {
        Ty::Record(index) => layouts.values().nth(index),
        _ => None,
    }
}

pub(super) fn memory_result(layouts: &BTreeMap<String, CRecordLayout>, ty: Ty) -> bool {
    record(layouts, ty).is_some_and(|layout| layout.size > 16)
}

pub(super) fn bytes(layouts: &BTreeMap<String, CRecordLayout>, ty: Ty) -> usize {
    record(layouts, ty).map_or(ty.slots() * 8, |layout| layout.size.div_ceil(8) * 8)
}

pub(super) fn arguments(
    layouts: &BTreeMap<String, CRecordLayout>,
    params: &[Ty],
    result: Ty,
) -> Option<(Vec<Place>, usize)> {
    let mut register = usize::from(memory_result(layouts, result));
    let mut stack = 0usize;
    let mut places = Vec::with_capacity(params.len());
    for &ty in params {
        let size = bytes(layouts, ty);
        let words = size / 8;
        if !memory_result(layouts, ty) && register + words <= 6 {
            places.push(Place::Registers {
                first: register,
                words,
            });
            register += words;
        } else {
            // An aggregate is indivisible: failure to fit does not consume
            // the remaining register, which may carry a later scalar.
            places.push(Place::Stack { offset: stack });
            stack = stack.checked_add(size)?;
        }
    }
    let stack = stack.checked_add(15)? / 16 * 16;
    (stack <= (i32::MAX as usize - 16)).then_some((places, stack))
}
