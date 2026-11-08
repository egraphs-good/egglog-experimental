//! Whole-binder alpha closing. Provisional identity is only Node.var text.
use super::{
    SortRef, TypedError, pb,
    storage::{Arena, Record},
};
use std::collections::{HashMap, HashSet};

pub(super) fn binder(roots: &[Record]) -> Result<HashMap<String, String>, TypedError> {
    let mut pending: Vec<_> = roots.iter().rev().cloned().collect();
    let mut visited = HashSet::new();
    let mut vars = HashMap::new();
    let mut order = vec![];
    let mut used = HashSet::new();
    let mut result = HashMap::new();
    while let Some(r) = pending.pop() {
        let owner = r.owner.as_ref().unwrap();
        if !visited.insert((owner.id, r.index)) {
            continue;
        }
        // A lazy initializer is not part of a query/code binder. Binding reads
        // remain global lookups; linking code never initializes a recipe.
        if r.capture()?.is_some() {
            continue;
        }
        let node = &owner.program().unwrap().nodes[r.index as usize];
        match &node.kind {
            Some(pb::node::Kind::Binding(_)) => (),
            Some(pb::node::Kind::Var(token)) => {
                let sort = SortRef(r.resolve(Arena::Sort, node.sort_id)?);
                if let Some(old) = vars.insert(token.clone(), sort.clone()) {
                    if old != sort {
                        return Err(TypedError::Invalid(
                            "conflicting sorts for one variable".into(),
                        ));
                    }
                    continue;
                }
                if let Some(hex) = token.strip_prefix("@typed:n:") {
                    if hex.len() % 2 != 0 {
                        return Err(TypedError::Invalid("invalid named token".into()));
                    }
                    let bytes = (0..hex.len())
                        .step_by(2)
                        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16))
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(|e| TypedError::Invalid(e.to_string()))?;
                    let name =
                        String::from_utf8(bytes).map_err(|e| TypedError::Invalid(e.to_string()))?;
                    used.insert(name.clone());
                    result.insert(token.clone(), name);
                } else if token.starts_with("@typed:f:") {
                    order.push((token.clone(), owner.variable_hint));
                } else {
                    return Err(TypedError::Invalid(
                        "foreign open binders require explicit adoption".into(),
                    ));
                }
            }
            Some(pb::node::Kind::Apply(apply)) => {
                for index in apply.args.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *index)?);
                }
                pending.push(
                    r.resolve(
                        Arena::Node,
                        apply.function.ok_or_else(|| {
                            TypedError::Invalid("missing function operand".into())
                        })?,
                    )?,
                );
            }
            Some(pb::node::Kind::Call(c)) => {
                for i in c.args.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *i)?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(lambda)),
            })) => {
                // A Lambda's environment belongs to this binder; its deferred
                // body owns positional parameters and is closed separately.
                for capture in lambda.captures.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *capture)?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(c)),
            })) => {
                for i in c.args.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *i)?);
                }
            }
            Some(pb::node::Kind::Eq(u)) => {
                for i in u.members.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *i)?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Map(map)),
            })) => {
                for entry in map.entries.iter().rev() {
                    for child in [entry.value, entry.key] {
                        pending.push(r.resolve(
                            Arena::Node,
                            child.ok_or_else(|| TypedError::Invalid("missing Map child".into()))?,
                        )?);
                    }
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Maybe(maybe)),
            })) => {
                if let Some(child) = maybe.value {
                    pending.push(r.resolve(Arena::Node, child)?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Pair(pair)),
            })) => {
                for child in [pair.second, pair.first] {
                    pending.push(r.resolve(
                        Arena::Node,
                        child.ok_or_else(|| TypedError::Invalid("missing Pair child".into()))?,
                    )?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value:
                    Some(
                        pb::primitive_value::Value::Vec(values)
                        | pb::primitive_value::Value::Set(values)
                        | pb::primitive_value::Value::Multiset(values),
                    ),
            })) => {
                for child in values.items.iter().rev() {
                    pending.push(r.resolve(Arena::Node, *child)?);
                }
            }
            Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value:
                    Some(
                        pb::primitive_value::Value::I64(_)
                        | pb::primitive_value::Value::F64Bits(_)
                        | pb::primitive_value::Value::String(_)
                        | pb::primitive_value::Value::Bool(_)
                        | pb::primitive_value::Value::Unit(_)
                        | pb::primitive_value::Value::BigInt(_)
                        | pb::primitive_value::Value::BigRat(_)
                        | pb::primitive_value::Value::Rational(_),
                    ),
            })) => {}
            _ => return Err(TypedError::Invalid("unsupported binder shape".into())),
        }
    }
    // Explicit named variables keep their spelling. Reserve available hints
    // before allocating generated names so a fresh scope never captures another.
    for (token, hint) in &order {
        if let Some(hint) = hint
            && used.insert((*hint).to_owned())
        {
            result.insert(token.clone(), (*hint).to_owned());
        }
    }
    let mut next = 0usize;
    for (token, _) in order {
        if result.contains_key(&token) {
            continue;
        }
        loop {
            let name = format!("__typed_v_{next}");
            next += 1;
            if used.insert(name.clone()) {
                result.insert(token, name);
                break;
            }
        }
    }
    Ok(result)
}
