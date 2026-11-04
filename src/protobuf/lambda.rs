//! Anonymous code is interned independently of its evaluated environment.
use super::{pb, source};
use prost::Message;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone)]
struct Code {
    program: pb::Program,
    captures: usize,
}

#[derive(Clone, Default)]
pub(super) struct Registry {
    keys: HashMap<Vec<u8>, usize>,
    names: HashMap<String, usize>,
    code: Vec<(String, Arc<Code>)>,
    next: usize,
}

impl Code {
    fn from_node(program: &pb::Program, index: u32) -> Result<Self, String> {
        let node = program
            .nodes
            .get(index as usize)
            .ok_or("Lambda node out of bounds")?;
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Lambda(lambda)),
        })) = &node.kind
        else {
            return Err("expected Lambda code".into());
        };
        let Some(pb::sort::Kind::Func(function)) = program
            .sorts
            .get(node.sort_id as usize)
            .and_then(|sort| sort.kind.as_ref())
        else {
            return Err("Lambda requires a function sort".into());
        };
        let mut result = pb::Program {
            files: program.files.clone(),
            ..Default::default()
        };
        let mut inputs = vec![];
        for sort in lambda
            .captures
            .iter()
            .map(|index| {
                program
                    .nodes
                    .get(*index as usize)
                    .map(|node| node.sort_id)
                    .ok_or_else(|| "Lambda capture out of bounds".to_owned())
            })
            .chain(function.params.iter().copied().map(Ok))
        {
            let sort = crate::builtin::import_sort(&program.sorts, sort?, &mut result.sorts)?;
            inputs.push(pb::Arg {
                name: String::new(),
                sort,
            });
        }
        let output =
            crate::builtin::import_sort(&program.sorts, function.result, &mut result.sorts)?;
        let binder = inputs.iter().map(|arg| arg.sort).collect::<Vec<_>>();
        let body = BodyCopier {
            source_program: program,
            result: &mut result,
            active: HashSet::new(),
            interned: HashMap::new(),
            memo: HashMap::new(),
        }
        .copy(lambda.body, &binder, index, 0)?;
        if result.nodes[body as usize].sort_id != output {
            return Err("Lambda body result sort mismatch".into());
        }
        result.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::UserDefinedPrimitive(
                pb::UserDefinedPrimitive {
                    name: String::new(),
                    inputs,
                    output,
                    body: Some(body),
                },
            )),
            ..Default::default()
        });
        Ok(Self {
            program: result,
            captures: lambda.captures.len(),
        })
    }

    fn key(&self) -> Vec<u8> {
        let mut program = self.program.clone();
        program.files.clear();
        for node in &mut program.nodes {
            node.span = None;
        }
        for sort in &mut program.sorts {
            sort.span = None;
            sort.doc = None;
        }
        let mut key = (self.captures as u64).to_le_bytes().to_vec();
        program
            .encode(&mut key)
            .expect("encoding into a Vec cannot fail");
        key
    }
}

// Bodies have positional binders, including a new binder at each nested Lambda.
// Union is deliberately excluded: ordinary Expr evaluation has no deferred fresh
// identity scope. Hashconsing syntax here therefore never merges fresh locations.
struct BodyCopier<'a> {
    source_program: &'a pb::Program,
    result: &'a mut pb::Program,
    active: HashSet<u32>,
    interned: HashMap<Vec<u8>, u32>,
    memo: HashMap<(u32, u32), u32>,
}

impl BodyCopier<'_> {
    fn copy(
        &mut self,
        index: u32,
        binder: &[u32],
        scope: u32,
        depth: usize,
    ) -> Result<u32, String> {
        if let Some(copied) = self.memo.get(&(index, scope)) {
            return Ok(*copied);
        }
        if depth >= 256 {
            return Err("Lambda body exceeds native expression depth".into());
        }
        if !self.active.insert(index) {
            return Err("cyclic Lambda code is unsupported".into());
        }
        let mut node = self
            .source_program
            .nodes
            .get(index as usize)
            .ok_or("Lambda body node out of bounds")?
            .clone();
        node.sort_id = crate::builtin::import_sort(
            &self.source_program.sorts,
            node.sort_id,
            &mut self.result.sorts,
        )?;
        match node.kind.as_mut().ok_or("missing Lambda body node kind")? {
            pb::node::Kind::Var(name) => {
                let position = name
                    .strip_prefix('_')
                    .and_then(|n| n.parse::<usize>().ok())
                    .filter(|position| name == &format!("_{position}"))
                    .ok_or("Lambda body variables must be positional binders")?;
                if binder.get(position) != Some(&node.sort_id) {
                    return Err("unbound or inconsistently typed Lambda variable".into());
                }
            }
            pb::node::Kind::Union(_) => {
                return Err("deferred Union bodies are not supported".into());
            }
            pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(lambda)),
            }) => {
                let Some(pb::sort::Kind::Func(function)) =
                    self.result.sorts[node.sort_id as usize].kind.clone()
                else {
                    return Err("nested Lambda requires a function sort".into());
                };
                let mut nested = vec![];
                for capture in &mut lambda.captures {
                    *capture = self.copy(*capture, binder, scope, depth + 1)?;
                    nested.push(self.result.nodes[*capture as usize].sort_id);
                }
                nested.extend(function.params);
                lambda.body = self.copy(lambda.body, &nested, index, depth + 1)?;
                if self.result.nodes[lambda.body as usize].sort_id != function.result {
                    return Err("nested Lambda body result sort mismatch".into());
                }
            }
            _ => source::source_node_refs(&mut node, |child| {
                *child = self.copy(*child, binder, scope, depth + 1)?;
                Ok(())
            })?,
        }
        self.active.remove(&index);
        let mut semantic = node.clone();
        semantic.span = None;
        let key = semantic.encode_to_vec();
        if let Some(copied) = self.interned.get(&key) {
            self.memo.insert((index, scope), *copied);
            return Ok(*copied);
        }
        let copied =
            u32::try_from(self.result.nodes.len()).map_err(|_| "too many Lambda body nodes")?;
        self.result.nodes.push(node);
        self.interned.insert(key, copied);
        self.memo.insert((index, scope), copied);
        Ok(copied)
    }
}

// Import code and its signature without importing any construction environment.
fn append_code(
    code: &Code,
    target: &mut pb::Program,
    diagnostics: bool,
) -> Result<pb::UserDefinedPrimitive, String> {
    let file_offset =
        u32::try_from(target.files.len()).map_err(|_| "too many Lambda source files")?;
    if diagnostics {
        target.files.extend(code.program.files.iter().cloned());
    }
    let mut source_sorts = code.program.sorts.clone();
    for sort in &mut source_sorts {
        if diagnostics {
            if let Some(span) = &mut sort.span {
                span.file = span
                    .file
                    .checked_add(file_offset)
                    .ok_or("too many Lambda source files")?;
            }
        } else {
            sort.span = None;
            sort.doc = None;
        }
    }
    let mut sorts = vec![];
    for index in 0..source_sorts.len() {
        sorts.push(crate::builtin::import_sort(
            &source_sorts,
            index as u32,
            &mut target.sorts,
        )?);
    }
    let offset = u32::try_from(target.nodes.len()).map_err(|_| "too many Lambda nodes")?;
    for mut node in code.program.nodes.iter().cloned() {
        node.sort_id = sorts[node.sort_id as usize];
        if diagnostics {
            if let Some(span) = &mut node.span {
                span.file = span
                    .file
                    .checked_add(file_offset)
                    .ok_or("too many Lambda source files")?;
            }
        } else {
            node.span = None;
        }
        source::source_node_refs(&mut node, |index| {
            *index = index.checked_add(offset).ok_or("too many Lambda nodes")?;
            Ok(())
        })?;
        target.nodes.push(node);
    }
    let Some(pb::declaration::Kind::UserDefinedPrimitive(mut definition)) =
        code.program.declarations[0].kind.clone()
    else {
        unreachable!("canonical anonymous code declaration")
    };
    for arg in &mut definition.inputs {
        arg.sort = sorts[arg.sort as usize];
    }
    definition.output = sorts[definition.output as usize];
    definition.body = definition.body.map(|index| index + offset);
    Ok(definition)
}

impl Registry {
    pub(super) fn lower(
        &mut self,
        program: &mut pb::Program,
        installed: &pb::Program,
    ) -> Result<(), String> {
        let authored = program.clone();
        let mut unavailable: HashSet<_> = installed
            .declarations
            .iter()
            .chain(&authored.declarations)
            .filter_map(|declaration| match &declaration.kind {
                Some(pb::declaration::Kind::UserDefinedPrimitive(p)) => Some(p.name.clone()),
                Some(pb::declaration::Kind::Function(f)) => Some(f.name.clone()),
                Some(pb::declaration::Kind::Constructor(c)) => Some(c.name.clone()),
                Some(pb::declaration::Kind::Relation(r)) => Some(r.name.clone()),
                _ => None,
            })
            .collect();
        for node in &authored.nodes {
            let call = match &node.kind {
                Some(pb::node::Kind::Call(call) | pb::node::Kind::GetCost(call)) => Some(call),
                Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::PartialCall(call)),
                })) => Some(call),
                _ => None,
            };
            if let Some(call) = call {
                if self.names.contains_key(&call.func) {
                    return Err("anonymous code targets are private".into());
                }
                unavailable.insert(call.func.clone());
            }
        }
        for declaration in &authored.declarations {
            if let Some(pb::declaration::Kind::UserDefinedPrimitive(p)) = &declaration.kind
                && self.names.contains_key(&p.name)
            {
                return Err("anonymous code targets are private".into());
            }
        }
        let mut emitted: HashSet<_> = installed
            .declarations
            .iter()
            .filter_map(|declaration| {
                if let Some(pb::declaration::Kind::UserDefinedPrimitive(p)) = &declaration.kind {
                    self.names.contains_key(&p.name).then(|| p.name.clone())
                } else {
                    None
                }
            })
            .collect();
        for (index, node) in authored.nodes.iter().enumerate() {
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(lambda)),
            })) = &node.kind
            else {
                continue;
            };
            let mut pending = lambda.captures.clone();
            let mut seen = HashSet::new();
            while let Some(capture) = pending.pop() {
                if capture == index as u32 {
                    return Err("self-referential Lambda captures are not supported".into());
                }
                if !seen.insert(capture) {
                    continue;
                }
                let mut value = authored
                    .nodes
                    .get(capture as usize)
                    .ok_or("Lambda capture out of bounds")?
                    .clone();
                if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Lambda(inner)),
                })) = &value.kind
                {
                    pending.extend(&inner.captures);
                } else {
                    source::source_node_refs(&mut value, |child| {
                        pending.push(*child);
                        Ok(())
                    })?;
                }
            }
            let name = self.intern(
                Code::from_node(&authored, index as u32)?,
                program,
                &mut emitted,
                &mut unavailable,
            )?;
            program.nodes[index].kind = Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                    func: name,
                    args: lambda.captures.clone(),
                })),
            }));
        }
        Ok(())
    }

    fn intern(
        &mut self,
        code: Code,
        target: &mut pb::Program,
        emitted: &mut HashSet<String>,
        unavailable: &mut HashSet<String>,
    ) -> Result<String, String> {
        let key = code.key();
        let index = if let Some(index) = self.keys.get(&key) {
            *index
        } else {
            let name = loop {
                let name = format!("__egglog_lambda_{}", self.next);
                self.next += 1;
                if unavailable.insert(name.clone()) {
                    break name;
                }
            };
            let index = self.code.len();
            self.keys.insert(key, index);
            self.names.insert(name.clone(), index);
            self.code.push((name, Arc::new(code)));
            index
        };
        let (name, code) = self.code[index].clone();
        if emitted.insert(name.clone()) {
            let mut lowered = code.program.clone();
            for (index, node) in code.program.nodes.iter().enumerate() {
                if let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Lambda(lambda)),
                })) = &node.kind
                {
                    let nested = self.intern(
                        Code::from_node(&code.program, index as u32)?,
                        target,
                        emitted,
                        unavailable,
                    )?;
                    lowered.nodes[index].kind =
                        Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                            value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                                func: nested,
                                args: lambda.captures.clone(),
                            })),
                        }));
                }
            }
            let mut definition = append_code(
                &Code {
                    program: lowered,
                    captures: code.captures,
                },
                target,
                true,
            )?;
            definition.name = name.clone();
            target.declarations.push(pb::Declaration {
                kind: Some(pb::declaration::Kind::UserDefinedPrimitive(definition)),
                ..Default::default()
            });
        }
        Ok(name)
    }

    pub(super) fn observe(
        &self,
        name: &str,
        captures: &[u32],
        program: &mut pb::Program,
    ) -> Result<Option<pb::PrimitiveValue>, String> {
        let Some(index) = self.names.get(name) else {
            return Ok(None);
        };
        let code = &self.code[*index].1;
        if captures.len() != code.captures {
            return Err("anonymous function capture count mismatch".into());
        }
        let body = append_code(code, program, false)?
            .body
            .expect("canonical anonymous body");
        Ok(Some(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                captures: captures.to_vec(),
                body,
            })),
        }))
    }

    pub(super) fn export_definitions(
        &self,
        definitions: &pb::Program,
    ) -> Result<pb::Program, String> {
        let mut result = definitions.clone();
        result.declarations.retain(|declaration| !matches!(&declaration.kind,
            Some(pb::declaration::Kind::UserDefinedPrimitive(p)) if self.names.contains_key(&p.name)));
        for index in 0..result.nodes.len() {
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(call)),
            })) = result.nodes[index].kind.clone()
            else {
                continue;
            };
            if let Some(value) = self.observe(&call.func, &call.args, &mut result)? {
                result.nodes[index].kind = Some(pb::node::Kind::PrimitiveValue(value));
            }
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lambda_code_key_visits_shared_body_once_per_binder() {
        let mut program = pb::Program {
            sorts: vec![
                pb::Sort {
                    kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                },
                pb::Sort {
                    kind: Some(pb::sort::Kind::Func(pb::FuncSort {
                        params: vec![0],
                        result: 0,
                    })),
                    ..Default::default()
                },
            ],
            nodes: vec![pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Var("_0".into())),
                ..Default::default()
            }],
            ..Default::default()
        };
        for previous in 0..32 {
            program.nodes.push(pb::Node {
                sort_id: 0,
                kind: Some(pb::node::Kind::Call(pb::Call {
                    func: "egglog.core.i64.add".into(),
                    args: vec![previous, previous],
                })),
                ..Default::default()
            });
        }
        program.nodes.push(pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                    captures: vec![],
                    body: 32,
                })),
            })),
            ..Default::default()
        });
        let code = Code::from_node(&program, 33).unwrap();
        assert_eq!(code.program.nodes.len(), 33);
        assert_eq!(code.key(), Code::from_node(&program, 33).unwrap().key());

        // The same source variable is valid in the outer capture+parameter
        // binder, but must be rechecked in a nested one-parameter binder.
        program.nodes[0].kind = Some(pb::node::Kind::Var("_1".into()));
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::I64(10)),
            })),
            ..Default::default()
        });
        program.nodes.push(pb::Node {
            sort_id: 1,
            kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::Lambda(pb::Lambda {
                    captures: vec![],
                    body: 0,
                })),
            })),
            ..Default::default()
        });
        program.nodes.push(pb::Node {
            sort_id: 0,
            kind: Some(pb::node::Kind::Apply(pb::Apply {
                function: Some(35),
                args: vec![34],
            })),
            ..Default::default()
        });
        let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
            value: Some(pb::primitive_value::Value::Lambda(lambda)),
        })) = &mut program.nodes[33].kind
        else {
            unreachable!()
        };
        lambda.captures.push(34);
        program.nodes[32].kind = Some(pb::node::Kind::Call(pb::Call {
            func: "egglog.core.i64.add".into(),
            args: vec![0, 36],
        }));
        assert!(matches!(Code::from_node(&program, 33), Err(message)
            if message == "unbound or inconsistently typed Lambda variable"));
    }
}
