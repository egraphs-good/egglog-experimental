//! Generate the Rust scalar and Vec surfaces from the actual native catalog.
//! Run without `--features typed` to bootstrap the generated source/resource;
//! use `--check` to detect either API or catalog drift. Nothing runs at import.
use egglog_experimental::proto as pb;
use prost::Message;
use std::{
    collections::{BTreeMap, HashSet},
    fmt::Write as _,
    io::Write as _,
    path::PathBuf,
    process::{Command, Stdio},
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let check = match std::env::args().skip(1).collect::<Vec<_>>().as_slice() {
        [] => false,
        [flag] if flag == "--check" => true,
        _ => return Err("usage: generate_typed_builtins [--check]".into()),
    };
    let catalog = egglog_experimental::new_experimental_egraph()
        .type_info()
        .builtin_catalog()
        .map_err(std::io::Error::other)?;
    let (source, deferred) = generate(&catalog.definitions).map_err(std::io::Error::other)?;
    let mut formatter = Command::new("rustfmt")
        .args(["--edition", "2024", "--emit", "stdout"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    formatter
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())?;
    let formatted = formatter.wait_with_output()?;
    if !formatted.status.success() {
        return Err("rustfmt rejected generated Rust".into());
    }
    let destination = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/typed/builtins");
    for (name, bytes) in [
        ("catalog.pb", catalog.definitions.encode_to_vec()),
        ("generated.rs", formatted.stdout),
    ] {
        let path = destination.join(name);
        if check {
            if std::fs::read(&path)? != bytes {
                return Err(format!(
                    "{} differs from the native catalog; regenerate",
                    path.display()
                )
                .into());
            }
        } else {
            std::fs::create_dir_all(&destination)?;
            std::fs::write(path, bytes)?;
        }
    }
    eprintln!(
        "Retained all {} native definitions; deferred Rust APIs: {deferred:?}",
        catalog.definitions.declarations.len()
    );
    eprintln!(
        "Undescribed primitives: {:?}",
        catalog.undescribed_primitives
    );
    eprintln!("Undescribed families: {:?}", catalog.undescribed_families);
    eprintln!(
        "Undescribed family operations: {:?}",
        catalog.undescribed_family_primitives
    );
    eprintln!("Undescribed sorts: {:?}", catalog.undescribed_sorts);
    Ok(())
}

// This first emitter accepts ordinary ASCII Rust names; unsupported spelling
// is an explicit generation error, never a silently normalized collision.
fn identifier(name: &str) -> Result<(), String> {
    let mut chars = name.chars();
    if !chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        || matches!(
            name,
            "_" | "as"
                | "async"
                | "await"
                | "break"
                | "const"
                | "continue"
                | "crate"
                | "dyn"
                | "else"
                | "enum"
                | "extern"
                | "false"
                | "fn"
                | "for"
                | "if"
                | "impl"
                | "in"
                | "let"
                | "loop"
                | "match"
                | "mod"
                | "move"
                | "mut"
                | "pub"
                | "ref"
                | "return"
                | "self"
                | "Self"
                | "static"
                | "struct"
                | "super"
                | "trait"
                | "true"
                | "type"
                | "unsafe"
                | "use"
                | "where"
                | "while"
                | "abstract"
                | "become"
                | "box"
                | "do"
                | "final"
                | "gen"
                | "macro"
                | "override"
                | "priv"
                | "try"
                | "typeof"
                | "unsized"
                | "virtual"
                | "yield"
        )
    {
        Err(format!("unsupported Rust identifier {name:?}"))
    } else {
        Ok(())
    }
}

// Generated binding patterns must not shadow an authored tuple constructor or
// operand. Rust paths alone cannot disambiguate a local binding pattern.
fn local_name(base: &str, occupied: &HashSet<&str>) -> String {
    let mut name = format!("__egglog_{base}");
    while occupied.contains(name.as_str()) {
        name.push('_');
    }
    name
}

fn generate(program: &pb::Program) -> Result<(String, Vec<String>), String> {
    if program.ir_version != 1
        || !program.nodes.is_empty()
        || !program.commands.is_empty()
        || !program.rules.is_empty()
        || !program.rulesets.is_empty()
        || !program.files.is_empty()
    {
        return Err("expected a declaration-only version-1 catalog".into());
    }
    let mut source = String::from(
        "// @generated by examples/generate_typed_builtins.rs. Do not edit.\n// The adjacent catalog.pb owns every semantic field; indices are locations only.\n",
    );
    let mut deferred = vec![];
    let mut types = BTreeMap::new(); // Derived presentation names, not signatures.
    let mut public_names = HashSet::new();
    let type_names: HashSet<&str> = program
        .declarations
        .iter()
        .filter_map(|d| {
            let Some(pb::declaration::Kind::HostSortFamily(f)) = &d.kind else {
                return None;
            };
            f.bindings
                .as_ref()?
                .rust
                .as_ref()?
                .path
                .last()
                .map(String::as_str)
        })
        .collect();
    let occupied: HashSet<&str> = type_names
        .iter()
        .copied()
        .chain(
            program
                .declarations
                .iter()
                .filter_map(|d| d.bindings.as_ref()?.rust.as_ref())
                .flat_map(|b| &b.views)
                .flat_map(|v| &v.params)
                .map(|p| p.name.as_str()),
        )
        .collect();
    let value_local = local_name("value", &occupied);
    let record_local = local_name("record", &occupied);
    let node_local = local_name("node", &occupied);
    let mut identities = HashSet::new();
    for (declaration_index, declaration) in program.declarations.iter().enumerate() {
        let (sort, name) = match &declaration.kind {
            Some(pb::declaration::Kind::HostSortFamily(f)) => (true, &f.name),
            Some(pb::declaration::Kind::HostPrimitive(p)) => (false, &p.name),
            _ => return Err("catalog contains a non-host definition".into()),
        };
        if name.is_empty() || !identities.insert((sort, name)) {
            return Err(format!("empty or duplicate catalog name {name:?}"));
        }
        let Some(pb::declaration::Kind::HostSortFamily(family)) = &declaration.kind else {
            continue;
        };
        let Some(binding) = family.bindings.as_ref().and_then(|b| b.rust.as_ref()) else {
            deferred.push(family.name.clone());
            continue;
        };
        if family.name == "Vec" {
            let name = binding.path.last().ok_or("missing Vec Rust path")?;
            identifier(name)?;
            if !public_names.insert(name.clone()) {
                return Err(format!("Rust type collision: {name}"));
            }
            emit_vec_type(program, declaration_index, &mut source, &occupied)?;
            continue;
        }
        // These are schema-defined value codecs, not a primitive signature or
        // a family-to-wrapper-name table. The Rust name comes from TypeBinding.
        let (host, arm, encode, decode) = match family.name.as_str() {
            "i64" => (
                "::core::primitive::i64",
                "I64",
                value_local.clone(),
                format!("*{value_local}"),
            ),
            "f64" => (
                "::core::primitive::f64",
                "F64Bits",
                format!("{value_local}.to_bits()"),
                format!("::core::primitive::f64::from_bits(*{value_local})"),
            ),
            _ => {
                deferred.push(family.name.clone());
                continue;
            }
        };
        if family.arity != 0
            || !binding.type_params.is_empty()
            || binding.path.len() != 4
            || binding.path[..3] != ["egglog_experimental", "typed", "builtins"]
        {
            return Err(format!(
                "unsupported scalar type binding for {}",
                family.name
            ));
        }
        let name = &binding.path[3];
        identifier(name)?;
        if !public_names.insert(name.clone()) {
            return Err(format!("Rust type collision: {name}"));
        }
        let index = program
            .sorts
            .iter()
            .position(|s| {
                matches!(&s.kind,
            Some(pb::sort::Kind::Family(f)) if f.name == family.name && f.args.is_empty())
            })
            .ok_or_else(|| format!("no concrete sort for {}", family.name))?;
        for (i, sort) in program.sorts.iter().enumerate() {
            if sort.kind == program.sorts[index].kind {
                types.insert(i as u32, name.clone());
            }
        }
        let doc = format!(
            "A protobuf-owned symbolic {} value. Structural equality preserves exact literal payloads.\n\n{}",
            family.name,
            declaration.doc.as_deref().unwrap_or_default()
        );
        writeln!(source, r#"
#[doc = {doc:?}]
#[derive(::core::clone::Clone, ::core::fmt::Debug, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
pub struct {name}(crate::typed::expr::Expr);
impl crate::typed::expr::ValueInput for self::{name} {{ type Owned = Self; }}
impl ::core::convert::From<&self::{name}> for self::{name} {{
    fn from({value_local}: &self::{name}) -> Self {{ ::core::clone::Clone::clone({value_local}) }}
}}
impl crate::typed::EgglogValue for self::{name} {{
    fn sort_ref() -> crate::typed::SortRef {{
        let mut {record_local} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record_local}.arena = crate::typed::storage::Arena::Sort;
        {record_local}.index = {index};
        crate::typed::SortRef({record_local})
    }}
    fn expression(&self) -> &crate::typed::expr::Expr {{ &self.0 }}
    fn from_expression({value_local}: crate::typed::expr::Expr) -> Self {{ Self({value_local}) }}
}}
impl ::core::convert::From<{host}> for self::{name} {{
    fn from({value_local}: {host}) -> Self {{
        Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }}).expect("generated scalar codec and catalog sort disagree"))
    }}
}}
impl ::core::convert::From<&{host}> for self::{name} {{
    fn from({value_local}: &{host}) -> Self {{
        let {value_local} = *{value_local};
        Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }}).expect("generated scalar codec and catalog sort disagree"))
    }}
}}
impl ::core::convert::TryFrom<&self::{name}> for {host} {{
    type Error = crate::typed::TypedError;
    fn try_from({value_local}: &self::{name}) -> ::core::result::Result<Self, Self::Error> {{
        let {record_local} = &{value_local}.0.0;
        let {node_local} = &{record_local}.owner.as_ref().unwrap().program.nodes[{record_local}.index as ::core::primitive::usize];
        if crate::typed::SortRef({record_local}.resolve(crate::typed::storage::Arena::Sort, {node_local}.sort_id)?) != <self::{name} as crate::typed::EgglogValue>::sort_ref() {{
            return ::core::result::Result::Err(crate::typed::TypedError::Decode(::std::borrow::ToOwned::to_owned("literal wrapper has another sort")));
        }}
        match &{node_local}.kind {{
            ::core::option::Option::Some(crate::typed::pb::node::Kind::PrimitiveValue(crate::typed::pb::PrimitiveValue {{
                value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({value_local})),
            }})) => ::core::result::Result::Ok({decode}),
            _ => ::core::result::Result::Err(crate::typed::TypedError::Decode(::std::borrow::ToOwned::to_owned("expected an exact {host} literal, not symbolic syntax"))),
        }}
    }}
}}
"#).unwrap();
    }
    let mut implementations = HashSet::new();
    for (index, declaration) in program.declarations.iter().enumerate() {
        let Some(pb::declaration::Kind::HostPrimitive(primitive)) = &declaration.kind else {
            continue;
        };
        let Some(rust) = declaration.bindings.as_ref().and_then(|b| b.rust.as_ref()) else {
            deferred.push(primitive.name.clone());
            continue;
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
            return Err(format!(
                "unsupported selected Rust typing: {}",
                primitive.name
            ));
        };
        if signature.varargs.len() > 1 {
            return Err(format!(
                "unsupported selected Rust tail width {} for {}",
                signature.varargs.len(),
                primitive.name
            ));
        }
        if !signature.type_params.is_empty() {
            emit_generic_views(program, index, &mut source, &mut implementations, &occupied)?;
            continue;
        }
        if !signature.type_params.is_empty()
            || !signature.varargs.is_empty()
            || signature.inputs.len() != 2
        {
            return Err(format!(
                "unsupported selected Rust signature: {}",
                primitive.name
            ));
        }
        let output = types
            .get(&signature.output.ok_or("missing output")?)
            .ok_or("unsupported Rust result sort")?;
        if rust.views.is_empty() {
            return Err(format!("empty Rust presentation for {}", primitive.name));
        }
        for view in &rust.views {
            let Some(pb::binding_owner::Kind::Sort(owner)) =
                view.owner.as_ref().and_then(|o| o.kind.as_ref())
            else {
                return Err("scalar operator needs a sort owner".into());
            };
            let owner = types.get(owner).ok_or("unsupported Rust owner sort")?;
            let receiver = view.receiver.as_ref().ok_or("missing receiver")?;
            let receiver_index = receiver.core_input.ok_or("missing receiver slot")? as usize;
            let trait_impl = view.trait_impl.as_ref().ok_or("missing Rust trait")?;
            if view.path != ["add"]
                || view.borrowed_self
                || receiver.borrowed
                || view.params.len() != 1
                || trait_impl.path != ["core", "ops", "Add"]
                || trait_impl.args.len() != 1
                || trait_impl.output_associated_type.as_deref() != Some("Output")
            {
                return Err(format!(
                    "unsupported scalar Rust view for {}",
                    primitive.name
                ));
            }
            let rhs = &view.params[0];
            identifier(&rhs.name)?;
            let rhs_index = rhs.core_input.ok_or("missing parameter slot")? as usize;
            if receiver_index >= 2
                || rhs_index >= 2
                || receiver_index == rhs_index
                || rhs.borrowed
                || trait_impl.args[0].borrowed
                || types.get(&signature.inputs[receiver_index].sort) != Some(owner)
                || types.get(
                    &trait_impl.args[0]
                        .sort
                        .ok_or("missing trait argument sort")?,
                ) != types.get(&signature.inputs[rhs_index].sort)
            {
                return Err(
                    "Rust receiver/parameter/trait mapping disagrees with signature".into(),
                );
            }
            let rhs_type = types
                .get(&signature.inputs[rhs_index].sort)
                .ok_or("unsupported RHS sort")?;
            // Metadata names remain in the protobuf descriptor, not binding
            // patterns: valid names such as Some are prelude variants in Rust.
            let rhs_name = local_name("rhs", &occupied);
            for borrowed_self in [false, true] {
                for borrowed_rhs in [false, true] {
                    let self_type =
                        format!("{}self::{owner}", if borrowed_self { "&" } else { "" });
                    let param_type =
                        format!("{}self::{rhs_type}", if borrowed_rhs { "&" } else { "" });
                    if !implementations.insert((self_type.clone(), param_type.clone())) {
                        return Err(format!(
                            "Rust Add implementation collision: {self_type} + {param_type}"
                        ));
                    }
                    let mut arguments = [String::new(), String::new()];
                    arguments[receiver_index] = "::core::clone::Clone::clone(&self.0)".into();
                    arguments[rhs_index] = format!("::core::clone::Clone::clone(&{rhs_name}.0)");
                    let arguments = arguments.join(", ");
                    writeln!(
                        source,
                        r#"
impl ::core::ops::Add<{param_type}> for {self_type} {{
    type Output = self::{output};
    fn add(self, {rhs_name}: {param_type}) -> Self::Output {{
        let mut {record_local} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record_local}.arena = crate::typed::storage::Arena::Declaration;
        {record_local}.index = {index};
        <self::{output} as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call(&crate::typed::decl::Callable({record_local}), ::std::vec![{arguments}]))
    }}
}}
"#
                    )
                    .unwrap();
                }
            }
        }
    }
    Ok((source, deferred))
}

// Translate the actual sort arena into Rust types. This derives presentation
// only: no family/callable signatures are restated in an emitter registry.
fn rust_type(program: &pb::Program, root: u32, parameters: &[String]) -> Result<String, String> {
    let mut rendered: BTreeMap<u32, String> = BTreeMap::new();
    let mut active = HashSet::new();
    let mut pending = vec![(root, false)];
    while let Some((index, finish)) = pending.pop() {
        if rendered.contains_key(&index) {
            continue;
        }
        let kind = program
            .sorts
            .get(index as usize)
            .and_then(|s| s.kind.as_ref())
            .ok_or("missing Rust sort pattern")?;
        if !finish {
            if !active.insert(index) {
                return Err("cyclic Rust sort pattern".into());
            }
            pending.push((index, true));
            if let pb::sort::Kind::Family(f) = kind {
                pending.extend(f.args.iter().rev().map(|child| (*child, false)));
            }
            continue;
        }
        let ty = match kind {
            pb::sort::Kind::Var(i) => parameters
                .get(*i as usize)
                .ok_or("unbound Rust type parameter")?
                .clone(),
            pb::sort::Kind::Family(f) => {
                let definition = program
                    .declarations
                    .iter()
                    .find_map(|d| match &d.kind {
                        Some(pb::declaration::Kind::HostSortFamily(h)) if h.name == f.name => {
                            Some(h)
                        }
                        _ => None,
                    })
                    .ok_or("missing Rust family definition")?;
                let binding = definition
                    .bindings
                    .as_ref()
                    .and_then(|b| b.rust.as_ref())
                    .ok_or("missing Rust family binding")?;
                if definition.arity as usize != f.args.len()
                    || binding.path.len() != 4
                    || binding.path[..3] != ["egglog_experimental", "typed", "builtins"]
                    || (!binding.type_params.is_empty()
                        && binding.type_params.len() != f.args.len())
                {
                    return Err("unsupported Rust family binding".into());
                }
                identifier(&binding.path[3])?;
                let mut name = format!("self::{}", binding.path[3]);
                if !f.args.is_empty() {
                    name.push('<');
                    name.push_str(
                        &f.args
                            .iter()
                            .map(|i| rendered[i].as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                    name.push('>');
                }
                name
            }
            _ => return Err("unsupported generated Rust sort pattern".into()),
        };
        active.remove(&index);
        rendered.insert(index, ty);
    }
    Ok(rendered.remove(&root).unwrap())
}

// Private generic identifiers cannot capture any authored public type. Core
// binder labels remain diagnostic; their positions determine the Rust mapping.
fn generic_parameters(program: &pb::Program, count: usize) -> Vec<String> {
    let mut occupied: HashSet<String> = program
        .declarations
        .iter()
        .filter_map(|d| {
            let Some(pb::declaration::Kind::HostSortFamily(f)) = &d.kind else {
                return None;
            };
            f.bindings.as_ref()?.rust.as_ref()?.path.last().cloned()
        })
        .collect();
    (0..count)
        .map(|index| {
            let mut name = format!("__EgglogType{index}");
            while !occupied.insert(name.clone()) {
                name.push('_');
            }
            name
        })
        .collect()
}

// Vec's payload codec is schema-defined, like the scalar codecs above. The
// public path/arity comes from the actual family declaration, not a method map.
fn emit_vec_type(
    program: &pb::Program,
    index: usize,
    source: &mut String,
    occupied: &HashSet<&str>,
) -> Result<(), String> {
    let Some(pb::declaration::Kind::HostSortFamily(family)) = &program.declarations[index].kind
    else {
        unreachable!()
    };
    let binding = family
        .bindings
        .as_ref()
        .and_then(|b| b.rust.as_ref())
        .ok_or("missing Vec binding")?;
    if family.arity != 1
        || binding.path.len() != 4
        || binding.path[..3] != ["egglog_experimental", "typed", "builtins"]
        || (!binding.type_params.is_empty() && binding.type_params.len() != 1)
    {
        return Err("unsupported Vec type binding".into());
    }
    let name = &binding.path[3];
    let t = &generic_parameters(program, 1)[0];
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let items = local_name("items", occupied);
    let child = local_name("child", occupied);
    writeln!(source, r#"
/// A protobuf-owned ordered vector expression. Native calls remain symbolic.
#[derive(::core::clone::Clone, ::core::fmt::Debug, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
pub struct {name}<{t}: crate::typed::EgglogValue>(crate::typed::expr::Expr, ::core::marker::PhantomData<fn() -> {t}>);
impl<{t}: crate::typed::EgglogValue> crate::typed::expr::ValueInput for self::{name}<{t}> {{ type Owned = Self; }}
impl<{t}: crate::typed::EgglogValue> ::core::convert::From<&self::{name}<{t}>> for self::{name}<{t}> {{
    fn from({value}: &Self) -> Self {{ ::core::clone::Clone::clone({value}) }}
}}
impl<{t}: crate::typed::EgglogValue> crate::typed::EgglogValue for self::{name}<{t}> {{
    fn sort_ref() -> crate::typed::SortRef {{
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {index};
        crate::typed::SortRef::family(&{record}, ::std::vec![<{t} as crate::typed::EgglogValue>::sort_ref()]).expect("generated family arity")
    }}
    fn expression(&self) -> &crate::typed::expr::Expr {{ &self.0 }}
    fn from_expression({value}: crate::typed::expr::Expr) -> Self {{ Self({value}, ::core::marker::PhantomData) }}
}}
impl<{t}: crate::typed::EgglogValue> ::core::convert::TryFrom<&self::{name}<{t}>> for ::std::vec::Vec<{t}> {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: &self::{name}<{t}>) -> ::core::result::Result<Self, Self::Error> {{
        let mut {items} = ::std::vec::Vec::new();
        for {child} in {value}.0.vec_elements(&<{t} as crate::typed::EgglogValue>::sort_ref())? {{
            {items}.push(<{t} as crate::typed::EgglogValue>::from_expression({child}));
        }}
        ::core::result::Result::Ok({items})
    }}
}}
"#).unwrap();
    Ok(())
}

fn emit_generic_views(
    program: &pb::Program,
    index: usize,
    source: &mut String,
    implementations: &mut HashSet<(String, String)>,
    occupied: &HashSet<&str>,
) -> Result<(), String> {
    let declaration = &program.declarations[index];
    let Some(pb::declaration::Kind::HostPrimitive(primitive)) = &declaration.kind else {
        unreachable!()
    };
    let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
        return Err("unsupported generic typing".into());
    };
    let rust = declaration
        .bindings
        .as_ref()
        .and_then(|b| b.rust.as_ref())
        .ok_or("missing generic Rust views")?;
    if rust.views.is_empty() {
        return Err("empty generic Rust views".into());
    }
    let parameters = generic_parameters(program, signature.type_params.len());
    let generics = parameters
        .iter()
        .map(|t| format!("{t}: crate::typed::EgglogValue"))
        .collect::<Vec<_>>()
        .join(", ");
    let output = rust_type(
        program,
        signature.output.ok_or("missing generic output")?,
        &parameters,
    )?;
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let args = local_name("args", occupied);
    for view in &rust.views {
        let Some(pb::binding_owner::Kind::Sort(owner)) =
            view.owner.as_ref().and_then(|o| o.kind.as_ref())
        else {
            return Err("generic Rust view requires a family owner".into());
        };
        let Some(pb::sort::Kind::Family(family)) = program
            .sorts
            .get(*owner as usize)
            .and_then(|s| s.kind.as_ref())
        else {
            return Err("generic Rust owner must be a family application".into());
        };
        if family.name != "Vec"
            || family.args.len() != parameters.len()
            || view.path.len() != 1
            || view.trait_impl.is_some()
            || view.borrowed_self
        {
            return Err("unsupported generic Rust member view".into());
        }
        for (position, sort) in family.args.iter().enumerate() {
            if !matches!(program.sorts[*sort as usize].kind, Some(pb::sort::Kind::Var(i)) if i as usize == position)
            {
                return Err("generic owner must determine its binder in family order".into());
            }
        }
        let owner = rust_type(program, *owner, &parameters)?;
        let method = &view.path[0];
        identifier(method)?;
        if !implementations.insert((owner.clone(), method.clone())) {
            return Err("duplicate generic Rust method".into());
        }
        let mut inputs = vec![None; signature.inputs.len()];
        let mut tail = None;
        let mut params = vec![];
        if let Some(receiver) = &view.receiver {
            let slot = receiver.core_input.ok_or("missing receiver slot")? as usize;
            let input = signature
                .inputs
                .get(slot)
                .ok_or("receiver slot out of range")?;
            if rust_type(program, input.sort, &parameters)? != owner {
                return Err("receiver differs from owner".into());
            }
            inputs[slot] = Some("::core::clone::Clone::clone(&self.0)".to_string());
            params.push(if receiver.borrowed {
                "&self".into()
            } else {
                "self".into()
            });
        }
        for (position, param) in view.params.iter().enumerate() {
            identifier(&param.name)?;
            if param.borrowed {
                return Err("borrowed generic parameter views are not supported yet".into());
            }
            let slot = param.core_input.ok_or("missing parameter slot")? as usize;
            let name = local_name(&format!("arg_{position}"), occupied);
            if slot < inputs.len() {
                let ty = rust_type(program, signature.inputs[slot].sort, &parameters)?;
                if inputs[slot].is_some() {
                    return Err("repeated generic input slot".into());
                }
                params.push(format!("{name}: impl ::core::convert::Into<{ty}>"));
                inputs[slot] = Some(format!(
                    "{{ let {value}: {ty} = ::core::convert::Into::into({name}); ::core::clone::Clone::clone(<{ty} as crate::typed::EgglogValue>::expression(&{value})) }}"
                ));
            } else if slot == inputs.len() && position + 1 == view.params.len() && tail.is_none() {
                let ty = rust_type(
                    program,
                    signature
                        .varargs
                        .first()
                        .ok_or("unexpected tail slot")?
                        .sort,
                    &parameters,
                )?;
                params.push(format!("{name}: impl ::core::iter::IntoIterator<Item = impl ::core::convert::Into<{ty}>>"));
                tail = Some((name, ty));
            } else {
                return Err("invalid generic input mapping".into());
            }
        }
        if inputs.iter().any(Option::is_none) || tail.is_none() != signature.varargs.is_empty() {
            return Err("generic Rust view omits a core input".into());
        }
        let inputs = inputs
            .into_iter()
            .map(Option::unwrap)
            .collect::<Vec<_>>()
            .join(", ");
        let mutability = if tail.is_some() { "mut " } else { "" };
        let tail_code = tail.map_or_else(String::new, |(name, ty)| format!("for {value} in ::core::iter::IntoIterator::into_iter({name}) {{ let {value}: {ty} = ::core::convert::Into::into({value}); {args}.push(::core::clone::Clone::clone(<{ty} as crate::typed::EgglogValue>::expression(&{value}))); }}"));
        let params = params.join(", ");
        writeln!(source, r#"
impl<{generics}> {owner} {{
    /// Author a catalog-defined call without evaluating its arguments.
    pub fn {method}({params}) -> {output} {{
        let {mutability}{args} = ::std::vec![{inputs}];
        {tail_code}
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {index};
        <{output} as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(
            &crate::typed::decl::Callable({record}), {args},
            <{output} as crate::typed::EgglogValue>::sort_ref(),
        ).expect("generated generic call disagrees with its descriptor"))
    }}
}}
"#).unwrap();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn optional_documentation_renders_without_rewriting_records() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        let index = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
                Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "i64")
            })
            .unwrap();
        let mut sources = vec![];
        let mut encodings = vec![];
        for doc in [None, Some(""), Some("Quoted \"docs\"\nsecond line")] {
            let mut program = original.clone();
            program.declarations[index].doc = doc.map(str::to_owned);
            let before = program.encode_to_vec();
            let (source, _) = generate(&program).unwrap();
            let expected = format!(
                "A protobuf-owned symbolic i64 value. Structural equality preserves exact literal payloads.\n\n{}",
                doc.unwrap_or_default()
            );
            assert!(source.contains(&format!("#[doc = {expected:?}]")));
            assert_eq!(program.encode_to_vec(), before);
            assert_eq!(
                pb::Program::decode(before.as_slice()).unwrap().declarations[index]
                    .doc
                    .as_deref(),
                doc
            );
            sources.push(source);
            encodings.push(before);
        }
        assert_eq!(sources[0], sources[1], "absent and empty docs render alike");
        assert_ne!(sources[1], sources[2]);
        assert_ne!(
            encodings[0], encodings[1],
            "documentation presence stays on the wire"
        );
        assert_ne!(encodings[1], encodings[2]);
    }

    #[test]
    fn grouped_tail_views_are_explicitly_rejected_but_records_are_retained() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        let (source, _) = generate(&original).unwrap();
        let of = source
            .split_once("pub fn of(")
            .unwrap()
            .1
            .split_once(" {")
            .unwrap()
            .0;
        assert!(of.contains("impl ::core::iter::IntoIterator<Item = impl ::core::convert::Into<"));
        let integer = original
            .sorts
            .iter()
            .position(|s| {
                matches!(&s.kind,
            Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty())
            })
            .unwrap() as u32;
        for name in ["egglog.core.vec.of", "egglog.core.i64.add"] {
            let index = original
                .declarations
                .iter()
                .position(|d| {
                    matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == name)
                })
                .unwrap();
            for width in [2, 3] {
                let mut program = original.clone();
                let Some(pb::declaration::Kind::HostPrimitive(primitive)) =
                    &mut program.declarations[index].kind
                else {
                    panic!()
                };
                let Some(pb::host_primitive::Typing::Signature(signature)) = &mut primitive.typing
                else {
                    panic!()
                };
                let pattern = signature
                    .varargs
                    .first()
                    .or_else(|| signature.inputs.first())
                    .unwrap()
                    .clone();
                signature.varargs = vec![pattern; width];
                if width == 3 {
                    signature.varargs[1].sort = integer;
                }
                assert_eq!(
                    generate(&program).unwrap_err(),
                    format!("unsupported selected Rust tail width {width} for {name}")
                );
                // Removing only Rust selection must retain every native field,
                // including all group positions, docs, and other language views.
                program.declarations[index].bindings.as_mut().unwrap().rust = None;
                program.declarations[index].doc = Some(String::new());
                let before = program.encode_to_vec();
                let (_, deferred) = generate(&program).unwrap();
                assert!(deferred.iter().any(|deferred| deferred == name));
                assert_eq!(program.encode_to_vec(), before);
                assert_eq!(pb::Program::decode(before.as_slice()).unwrap(), program);
            }
        }
    }

    #[test]
    fn ordinary_metadata_names_cannot_capture_generated_support() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        for (integer, float, parameter) in [
            ("i64", "f64", "catalog"),
            ("From", "TryFrom", "Callable"),
            ("Result", "Some", "__egglog_record"),
            ("Expr", "SortRef", "record"),
            ("Clone", "Into", "value"),
            ("value", "__egglog_value", "__egglog_record_"),
            ("catalog", "Callable", "catalog"),
        ] {
            let mut program = original.clone();
            for d in &mut program.declarations {
                if let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut d.kind {
                    let name = match f.name.as_str() {
                        "i64" => integer,
                        "f64" => float,
                        _ => continue,
                    };
                    f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3] = name.into();
                }
                if let Some(rust) = d.bindings.as_mut().and_then(|b| b.rust.as_mut()) {
                    for view in rust
                        .views
                        .iter_mut()
                        .filter(|view| view.trait_impl.is_some())
                    {
                        view.params[0].name = parameter.into();
                    }
                }
            }
            let (source, _) = generate(&program).unwrap();
            assert!(source.contains("::core::primitive::i64"));
            assert!(source.contains("::core::primitive::f64"));
            assert!(source.contains("::core::convert::From<"));
            assert!(source.contains("::core::convert::TryFrom<"));
            assert!(source.contains("::core::result::Result<"));
            assert!(source.contains("::core::option::Option::Some("));
            assert!(source.contains("crate::typed::decl::Callable("));
            assert!(!source.contains("= catalog()"));
            assert!(!source.contains("(Expr)"));
        }
    }

    #[test]
    fn operand_metadata_names_never_become_rust_binding_patterns() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        for parameter in ["Some", "None", "Ok", "Err", "__egglog_rhs"] {
            let mut program = original.clone();
            for d in &mut program.declarations {
                if let Some(rust) = d.bindings.as_mut().and_then(|b| b.rust.as_mut()) {
                    for view in rust
                        .views
                        .iter_mut()
                        .filter(|view| view.trait_impl.is_some())
                    {
                        view.params[0].name = parameter.into();
                    }
                }
            }
            let (source, _) = generate(&program).unwrap();
            assert!(source.contains("pub struct I64"));
            assert!(source.contains("pub struct F64"));
            assert!(!source.contains(&format!("fn add(self, {parameter}:")));
            let expected = if parameter == "__egglog_rhs" {
                "__egglog_rhs_"
            } else {
                "__egglog_rhs"
            };
            assert_eq!(
                source.matches(&format!("fn add(self, {expected}:")).count(),
                8
            );
        }
    }

    // Check the numeric slot inside the exact wrapper/operator implementation,
    // not output ordering or unrelated presentation changes.
    fn assert_locations(program: &pb::Program, source: &str) {
        for (index, sort) in program.sorts.iter().enumerate() {
            let Some(pb::sort::Kind::Family(f)) = &sort.kind else {
                continue;
            };
            if !f.args.is_empty() || !matches!(f.name.as_str(), "i64" | "f64") {
                continue;
            }
            let family = program
                .declarations
                .iter()
                .find_map(|d| match &d.kind {
                    Some(pb::declaration::Kind::HostSortFamily(h)) if h.name == f.name => Some(h),
                    _ => None,
                })
                .unwrap();
            let name = &family
                .bindings
                .as_ref()
                .unwrap()
                .rust
                .as_ref()
                .unwrap()
                .path[3];
            let marker = format!("EgglogValue for self::{name} {{");
            let tail = source.split_once(&marker).unwrap().1;
            let body = tail.split_once("fn expression").unwrap().0;
            assert!(
                body.contains(&format!(".index = {index};")),
                "wrong sort location for {name}: {body}"
            );
        }
        for (index, d) in program.declarations.iter().enumerate() {
            let Some(view) = d
                .bindings
                .as_ref()
                .and_then(|b| b.rust.as_ref())
                .and_then(|r| r.views.first())
                .filter(|view| view.trait_impl.is_some())
            else {
                continue;
            };
            let Some(pb::binding_owner::Kind::Sort(owner)) = view.owner.as_ref().unwrap().kind
            else {
                panic!()
            };
            let Some(pb::sort::Kind::Family(f)) = &program.sorts[owner as usize].kind else {
                panic!()
            };
            let family = program
                .declarations
                .iter()
                .find_map(|d| match &d.kind {
                    Some(pb::declaration::Kind::HostSortFamily(h)) if h.name == f.name => Some(h),
                    _ => None,
                })
                .unwrap();
            let name = &family
                .bindings
                .as_ref()
                .unwrap()
                .rust
                .as_ref()
                .unwrap()
                .path[3];
            for lhs in ["", "&"] {
                for rhs in ["", "&"] {
                    let marker = format!(
                        "impl ::core::ops::Add<{rhs}self::{name}> for {lhs}self::{name} {{"
                    );
                    let tail = source.split_once(&marker).unwrap().1;
                    let body = tail.split_once("\n}\n").unwrap().0;
                    assert!(
                        body.contains(&format!(".index = {index};")),
                        "wrong declaration location for {name}: {body}"
                    );
                }
            }
        }
    }

    #[test]
    fn native_records_determine_paths_locations_and_argument_order() {
        let mut p = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        let (source, deferred) = generate(&p).unwrap();
        assert!(source.contains("pub struct I64"));
        assert!(source.contains("pub struct F64"));
        let has_vec_view = p.declarations.iter().any(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Vec" && f.bindings.as_ref().is_some_and(|b| b.rust.is_some())));
        assert_eq!(
            deferred.len(),
            if has_vec_view { 0 } else { 4 },
            "unbound Vec APIs remain explicitly deferred"
        );
        assert_eq!(source.matches("fn add(self,").count(), 8);
        assert_locations(&p, &source);
        let index = p
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "egglog.core.i64.add")
            })
            .unwrap();
        let declaration = &mut p.declarations[index];
        let Some(pb::declaration::Kind::HostPrimitive(h)) = &mut declaration.kind else {
            unreachable!()
        };
        h.name = "test.renamed.scalar.add".into();
        let view = &mut declaration
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0];
        view.receiver.as_mut().unwrap().core_input = Some(1);
        view.params[0].core_input = Some(0);
        let (changed, _) = generate(&p).unwrap();
        assert_locations(&p, &changed);
        assert!(changed.contains(
            "::std::vec![::core::clone::Clone::clone(&__egglog_rhs.0), ::core::clone::Clone::clone(&self.0)]"
        ));
        assert!(
            !changed.contains("egglog.core.i64.add"),
            "generated execution reads the record's name"
        );
        p.declarations.reverse();
        let (permuted, _) = generate(&p).unwrap();
        assert_locations(&p, &permuted);
        assert!(
            std::panic::catch_unwind(|| assert_locations(&p, &changed)).is_err(),
            "stale declaration locations must fail independently of output order"
        );
        assert!(permuted.contains(
            "::std::vec![::core::clone::Clone::clone(&__egglog_rhs.0), ::core::clone::Clone::clone(&self.0)]"
        ));
        let family = p
            .declarations
            .iter_mut()
            .find_map(|d| match &mut d.kind {
                Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "i64" => Some(f),
                _ => None,
            })
            .unwrap();
        family
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .path[3] = "RenamedI64".into();
        let same_name_baseline = generate(&p).unwrap().0;
        assert!(same_name_baseline.contains("pub struct RenamedI64"));
        assert_locations(&p, &same_name_baseline);
        // A physical sort permutation must relocate every semantic reference,
        // including presentation owners/trait arguments, before generation.
        let last = p.sorts.len() as u32 - 1;
        p.sorts.reverse();
        for sort in &mut p.sorts {
            if let Some(pb::sort::Kind::Family(f)) = &mut sort.kind {
                for arg in &mut f.args {
                    *arg = last - *arg;
                }
            }
        }
        for d in &mut p.declarations {
            if let Some(pb::declaration::Kind::HostPrimitive(h)) = &mut d.kind {
                let Some(pb::host_primitive::Typing::Signature(s)) = &mut h.typing else {
                    panic!()
                };
                for a in s.inputs.iter_mut().chain(s.varargs.iter_mut()) {
                    a.sort = last - a.sort;
                }
                let output = s.output.as_mut().unwrap();
                *output = last - *output;
            }
            if let Some(b) = &mut d.bindings {
                for owner in b
                    .python
                    .iter_mut()
                    .flat_map(|p| &mut p.views)
                    .filter_map(|v| v.owner.as_mut())
                    .chain(
                        b.rust
                            .iter_mut()
                            .flat_map(|r| &mut r.views)
                            .filter_map(|v| v.owner.as_mut()),
                    )
                {
                    let Some(pb::binding_owner::Kind::Sort(s)) = &mut owner.kind else {
                        panic!()
                    };
                    *s = last - *s;
                }
                for arg in b
                    .rust
                    .iter_mut()
                    .flat_map(|r| &mut r.views)
                    .filter_map(|v| v.trait_impl.as_mut())
                    .flat_map(|t| &mut t.args)
                {
                    let sort = arg.sort.as_mut().unwrap();
                    *sort = last - *sort;
                }
            }
        }
        let (relocated, _) = generate(&p).unwrap();
        assert_ne!(relocated, same_name_baseline);
        assert_locations(&p, &relocated);
        assert!(
            std::panic::catch_unwind(|| assert_locations(&p, &same_name_baseline)).is_err(),
            "stale sort locations must fail with identical presentation names"
        );
        assert!(relocated.contains("pub struct RenamedI64"));
    }

    #[test]
    fn malformed_mapping_and_generated_borrow_collisions_are_errors() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        let index = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(h)) if h.name == "egglog.core.i64.add")
            })
            .unwrap();
        for slot in [0, 2] {
            let mut p = original.clone();
            p.declarations[index]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0]
                .params[0]
                .core_input = Some(slot);
            assert!(generate(&p).is_err());
        }
        let mut p = original;
        let rust = p.declarations[index]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap();
        rust.views.push(rust.views[0].clone());
        assert!(generate(&p).is_err());
    }

    #[test]
    fn native_vec_views_drive_generic_members_and_relocated_declarations() {
        let mut program = egglog_experimental::new_experimental_egraph()
            .type_info()
            .builtin_catalog()
            .unwrap()
            .definitions;
        let family = program
            .declarations
            .iter()
            .find_map(|d| match &d.kind {
                Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Vec" => Some(f),
                _ => None,
            })
            .unwrap();
        assert!(
            family.bindings.as_ref().is_some_and(|b| b.rust.is_some()),
            "this gate requires the actual engine-owned Vec Rust metadata checkpoint"
        );
        let original = program.clone();
        for permute in [false, true] {
            if permute {
                program.declarations.reverse();
            }
            let (source, deferred) = generate(&program).unwrap();
            assert!(deferred.is_empty());
            let parameters = generic_parameters(&program, 1);
            for (index, d) in program.declarations.iter().enumerate() {
                if let Some(pb::declaration::Kind::HostSortFamily(f)) = &d.kind {
                    if f.name == "Vec" {
                        let name = &f.bindings.as_ref().unwrap().rust.as_ref().unwrap().path[3];
                        let start = format!(
                            "crate::typed::EgglogValue for self::{name}<{}>",
                            parameters[0]
                        );
                        let body = source.split_once(&start).unwrap().1;
                        let body = body.split_once("fn expression").unwrap().0;
                        assert!(body.contains(&format!(".index = {index};")));
                    }
                }
                let Some(pb::declaration::Kind::HostPrimitive(p)) = &d.kind else {
                    continue;
                };
                let Some(pb::host_primitive::Typing::Signature(s)) = &p.typing else {
                    continue;
                };
                if s.type_params.is_empty() {
                    continue;
                }
                let views = &d.bindings.as_ref().unwrap().rust.as_ref().unwrap().views;
                for view in views {
                    let Some(pb::binding_owner::Kind::Sort(owner)) =
                        view.owner.as_ref().unwrap().kind
                    else {
                        panic!()
                    };
                    let owner = rust_type(&program, owner, &parameters).unwrap();
                    let start = format!(
                        "impl<{}: crate::typed::EgglogValue> {owner} {{",
                        parameters[0]
                    );
                    let method = format!("pub fn {}(", view.path[0]);
                    let body = source
                        .split(&start)
                        .skip(1)
                        .find(|part| part.contains(&method))
                        .unwrap();
                    let body = body.split_once("\n}\n").unwrap().0;
                    assert!(
                        body.contains(&format!(".index = {index};")),
                        "wrong record location for {}",
                        p.name
                    );
                    assert!(body.contains(&format!(
                        "-> {}",
                        rust_type(&program, s.output.unwrap(), &parameters).unwrap()
                    )));
                }
            }
        }
        let mut renamed = original.clone();
        let get = renamed
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.vec.get")
            })
            .unwrap();
        renamed.declarations[get]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0]
            .path[0] = "pick".into();
        assert!(generate(&renamed).unwrap().0.contains("pub fn pick("));
        renamed.declarations[get]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0]
            .receiver
            .as_mut()
            .unwrap()
            .core_input = Some(1);
        assert!(
            generate(&renamed).is_err(),
            "wrong receiver must not be ignored"
        );

        let mut changed_output = original.clone();
        let integer = changed_output
            .sorts
            .iter()
            .position(|s| {
                matches!(&s.kind,
                Some(pb::sort::Kind::Family(f)) if f.name == "i64" && f.args.is_empty())
            })
            .unwrap() as u32;
        let Some(pb::declaration::Kind::HostPrimitive(p)) =
            &mut changed_output.declarations[get].kind
        else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &mut p.typing else {
            panic!()
        };
        signature.output = Some(integer);
        let source = generate(&changed_output).unwrap().0;
        let header = source.split_once("pub fn get(").unwrap().1;
        let header = header.split_once(" {").unwrap().0;
        assert!(header.contains(&format!(
            "-> {}",
            rust_type(&changed_output, integer, &generic_parameters(&changed_output, 1)).unwrap()
        )));
        let mut labels = original.clone();
        for d in &mut labels.declarations {
            if let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut d.kind {
                if let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing {
                    for label in &mut s.type_params {
                        *label = "RenamedDiagnostic".into();
                    }
                }
            }
        }
        assert_eq!(generate(&labels).unwrap().0, generate(&original).unwrap().0);
    }
}
