//! Generate the Rust scalar and container surfaces from the actual native catalog.
//! Run without `--features typed` to bootstrap the generated source/resource;
//! use `--check` to detect either API or catalog drift. Nothing runs at import.
use egglog_experimental::PortableTypeInfo;
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
        .portable_builtin_catalog()
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
    if !program.nodes.is_empty()
        || !program.commands.is_empty()
        || !program.rules.is_empty()
        || !program.files.is_empty()
    {
        return Err("expected a declaration-only catalog".into());
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
    let error_local = local_name("error", &occupied);
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
        if matches!(
            family.name.as_str(),
            "Vec" | "Set" | "MultiSet" | "Pair" | "Map" | "Maybe"
        ) {
            let name = binding.path.last().ok_or("missing container Rust path")?;
            identifier(name)?;
            if !public_names.insert(name.clone()) {
                return Err(format!("Rust type collision: {name}"));
            }
            emit_container_type(program, declaration_index, &mut source, &occupied)?;
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
            "String" => (
                "::std::string::String",
                "String",
                value_local.clone(),
                format!("::core::clone::Clone::clone({value_local})"),
            ),
            "bool" => (
                "::core::primitive::bool",
                "Bool",
                value_local.clone(),
                format!("*{value_local}"),
            ),
            "Unit" => (
                "()",
                "Unit",
                "crate::typed::pb::Unit {}".into(),
                "()".into(),
            ),
            "BigInt" => (
                "::num::BigInt",
                "BigInt",
                format!("::std::string::ToString::to_string(&{value_local})"),
                format!(
                    "{value_local}.parse::<::num::BigInt>().map_err(|{error_local}| crate::typed::TypedError::Decode(::std::string::ToString::to_string(&{error_local})))?"
                ),
            ),
            "BigRat" => (
                "::num::BigRational",
                "BigRat",
                format!(
                    "crate::typed::pb::BigRat {{ numerator: ::std::string::ToString::to_string({value_local}.numer()), denominator: ::std::string::ToString::to_string({value_local}.denom()) }}"
                ),
                format!(
                    "::num::BigRational::new_raw({value_local}.numerator.parse::<::num::BigInt>().map_err(|{error_local}| crate::typed::TypedError::Decode(::std::string::ToString::to_string(&{error_local})))?, {value_local}.denominator.parse::<::num::BigInt>().map_err(|{error_local}| crate::typed::TypedError::Decode(::std::string::ToString::to_string(&{error_local})))?)"
                ),
            ),
            "Rational" => (
                "::num::rational::Rational64",
                "Rational",
                format!(
                    "crate::typed::pb::Rational {{ numerator: *{value_local}.numer(), denominator: *{value_local}.denom() }}"
                ),
                format!(
                    "::num::rational::Rational64::new_raw({value_local}.numerator, {value_local}.denominator)"
                ),
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
        let concrete = program.sorts.iter().position(|s| {
            matches!(&s.kind,
            Some(pb::sort::Kind::Family(f)) if f.name == family.name && f.args.is_empty())
        });
        for (i, sort) in program.sorts.iter().enumerate() {
            if matches!(&sort.kind, Some(pb::sort::Kind::Family(f)) if f.name == family.name && f.args.is_empty())
            {
                types.insert(i as u32, name.clone());
            }
        }
        // A literal-only family need not occur in any callable's sort arena.
        // Instantiate its actual declaration, just as container wrappers do.
        let (arena, index, sort_ref) = if let Some(index) = concrete {
            (
                "Sort",
                index,
                format!("crate::typed::SortRef({record_local})"),
            )
        } else {
            (
                "Declaration",
                declaration_index,
                format!(
                    "crate::typed::SortRef::family(&{record_local}, ::std::vec![]).expect(\"generated scalar family arity\")"
                ),
            )
        };
        let mut doc = format!(
            "A protobuf-owned symbolic {} value. Structural equality preserves exact literal payloads.\n\n{}",
            family.name,
            declaration.doc.as_deref().unwrap_or_default()
        );
        if matches!(family.name.as_str(), "BigInt" | "BigRat" | "Rational") {
            write!(doc, "\n\nHost conversion creates inert exact data; catalog methods create symbolic Calls. Decoding inspects only literal payloads, never evaluates a Call. No implicit float conversion is provided.\n\n```compile_fail,E0277\nuse egglog_experimental::typed::builtins::{name};\nlet _ = {name}::try_from(0.5_f64);\n```\n").unwrap();
            if family.name != "BigInt" {
                write!(doc, "\nA host ratio may have been built with `new_raw`; use checked `TryFrom`, which rejects nonreduced values and nonpositive denominators without normalization.\n\n```compile_fail,E0277\nuse egglog_experimental::typed::builtins::{name};\nlet _: {name} = {host}::new(1.into(), 2.into()).into();\n```\n").unwrap();
            }
        }
        let borrowed_value = if matches!(family.name.as_str(), "Unit" | "BigInt") {
            String::new()
        } else if family.name == "String" {
            format!("let {value_local} = ::core::clone::Clone::clone({value_local});")
        } else {
            format!("let {value_local} = *{value_local};")
        };
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
        {record_local}.arena = crate::typed::storage::Arena::{arena};
        {record_local}.index = {index};
        {sort_ref}
    }}
    fn expression(&self) -> &crate::typed::expr::Expr {{ &self.0 }}
    fn from_expression({value_local}: crate::typed::expr::Expr) -> Self {{ Self({value_local}) }}
}}
"#).unwrap();
        // Ratio::new_raw admits malformed host values. Unlike a BigInt, a host
        // ratio therefore needs the same checked boundary as its wire payload.
        if matches!(family.name.as_str(), "BigRat" | "Rational") {
            writeln!(source, r#"
impl ::core::convert::TryFrom<{host}> for self::{name} {{
    type Error = crate::typed::TypedError;
    fn try_from({value_local}: {host}) -> ::core::result::Result<Self, Self::Error> {{
        ::core::result::Result::Ok(Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }})?))
    }}
}}
impl ::core::convert::TryFrom<&{host}> for self::{name} {{
    type Error = crate::typed::TypedError;
    fn try_from({value_local}: &{host}) -> ::core::result::Result<Self, Self::Error> {{
        ::core::result::Result::Ok(Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }})?))
    }}
}}
"#).unwrap();
        } else {
            writeln!(source, r#"
impl ::core::convert::From<{host}> for self::{name} {{
    fn from({value_local}: {host}) -> Self {{
        Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }}).expect("generated scalar codec and catalog sort disagree"))
    }}
}}
impl ::core::convert::From<&{host}> for self::{name} {{
    fn from({value_local}: &{host}) -> Self {{
        {borrowed_value}
        Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({encode})),
        }}).expect("generated scalar codec and catalog sort disagree"))
    }}
}}
"#).unwrap();
        }
        if family.name == "i64" {
            writeln!(source, r#"
impl ::core::convert::From<::core::primitive::i32> for self::{name} {{
    fn from({value_local}: ::core::primitive::i32) -> Self {{
        <Self as ::core::convert::From<::core::primitive::i64>>::from(::core::primitive::i64::from({value_local}))
    }}
}}
impl ::core::convert::From<&::core::primitive::i32> for self::{name} {{
    fn from({value_local}: &::core::primitive::i32) -> Self {{
        <Self as ::core::convert::From<::core::primitive::i64>>::from(::core::primitive::i64::from(*{value_local}))
    }}
}}
"#).unwrap();
        }
        let decode_validation = if matches!(family.name.as_str(), "BigInt" | "BigRat" | "Rational")
        {
            format!(
                "if let ::core::option::Option::Some(crate::typed::pb::node::Kind::PrimitiveValue({value_local})) = &{node_local}.kind {{ crate::typed::expr::validate_literal(&<self::{name} as crate::typed::EgglogValue>::sort_ref(), {value_local})?; }}"
            )
        } else {
            String::new()
        };
        writeln!(source, r#"
impl ::core::convert::TryFrom<&self::{name}> for {host} {{
    type Error = crate::typed::TypedError;
    fn try_from({value_local}: &self::{name}) -> ::core::result::Result<Self, Self::Error> {{
        let {record_local} = &{value_local}.0.0;
        let {node_local} = &{record_local}.owner.as_ref().unwrap().program.nodes[{record_local}.index as ::core::primitive::usize];
        if crate::typed::SortRef({record_local}.resolve(crate::typed::storage::Arena::Sort, {node_local}.sort_id)?) != <self::{name} as crate::typed::EgglogValue>::sort_ref() {{
            return ::core::result::Result::Err(crate::typed::TypedError::Decode(::std::borrow::ToOwned::to_owned("literal wrapper has another sort")));
        }}
        {decode_validation}
        match &{node_local}.kind {{
            ::core::option::Option::Some(crate::typed::pb::node::Kind::PrimitiveValue(crate::typed::pb::PrimitiveValue {{
                value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::{arm}({value_local})),
            }})) => ::core::result::Result::Ok({decode}),
            _ => ::core::result::Result::Err(crate::typed::TypedError::Decode(::std::borrow::ToOwned::to_owned("expected an exact {host} literal, not symbolic syntax"))),
        }}
    }}
}}
"#).unwrap();
        if family.name == "String" {
            writeln!(source, r#"
impl ::core::convert::From<&::core::primitive::str> for self::{name} {{
    fn from({value_local}: &::core::primitive::str) -> Self {{
        Self(crate::typed::expr::Expr::literal(<Self as crate::typed::EgglogValue>::sort_ref(), crate::typed::pb::PrimitiveValue {{
            value: ::core::option::Option::Some(crate::typed::pb::primitive_value::Value::String(::std::borrow::ToOwned::to_owned({value_local}))),
        }}).expect("generated scalar codec and catalog sort disagree"))
    }}
}}
"#).unwrap();
        }
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
        let signature = match &primitive.typing {
            Some(pb::host_primitive::Typing::Signature(signature)) => signature,
            Some(pb::host_primitive::Typing::Application(_)) => {
                for view in &rust.views {
                    if view.path.len() != 1
                        || !matches!(
                            view.owner.as_ref().and_then(|owner| owner.kind.as_ref()),
                            Some(pb::binding_owner::Kind::Function(_))
                        )
                        || view.receiver
                            != Some(pb::RustReceiver {
                                core_input: Some(0),
                                borrowed: true,
                            })
                        || view.params.len() != 1
                        || view.params[0].core_input != Some(1)
                        || view.params[0].borrowed
                        || view.trait_impl.is_some()
                        || view.borrowed_self
                        || view.tail_repetitions.is_some()
                    {
                        return Err("unsupported Rust function application view".into());
                    }
                    identifier(&view.path[0])?;
                    writeln!(source, "function_application!({}, {index});", view.path[0]).unwrap();
                }
                continue;
            }
            _ => {
                return Err(format!(
                    "unsupported selected Rust typing: {}",
                    primitive.name
                ));
            }
        };
        if signature
            .equality_type_params
            .iter()
            .any(|&i| i as usize >= signature.type_params.len())
            || signature
                .equality_type_params
                .windows(2)
                .any(|w| w[0] >= w[1])
        {
            return Err("equality binders must be strictly increasing and in range".into());
        }
        if signature.varargs.len() > 1 {
            return Err(format!(
                "unsupported selected Rust tail width {} for {}",
                signature.varargs.len(),
                primitive.name
            ));
        }
        if !signature.type_params.is_empty() {
            emit_generic_views(
                program,
                index,
                &mut source,
                &mut implementations,
                &mut public_names,
                &occupied,
            )?;
            continue;
        }
        let output = rust_type(program, signature.output.ok_or("missing output")?, &[])?;
        if rust.views.is_empty() {
            return Err(format!("empty Rust presentation for {}", primitive.name));
        }
        for view in &rust.views {
            let mapped = view.params.len() + usize::from(view.receiver.is_some());
            let (input_count, tail) = if let Some(repetitions) = view.tail_repetitions {
                if signature.varargs.is_empty() {
                    return Err("fixed-tail Rust view requires a canonical tail".into());
                }
                let count = signature
                    .varargs
                    .len()
                    .checked_mul(repetitions as usize)
                    .and_then(|tail| signature.inputs.len().checked_add(tail))
                    .ok_or("Rust fixed-tail input count overflow")?;
                if count != mapped {
                    return Err("Rust fixed-tail view omits or adds core inputs".into());
                }
                (count, None)
            } else {
                let tail = signature.varargs.first();
                let consumes_tail = view
                    .receiver
                    .is_some_and(|r| r.core_input == Some(signature.inputs.len() as u32));
                if consumes_tail && signature.varargs.len() != 1 {
                    return Err("tail receiver requires a homogeneous variadic signature".into());
                }
                let input_count = signature.inputs.len() + usize::from(consumes_tail);
                if mapped != input_count + usize::from(tail.is_some()) {
                    return Err("Rust view omits or adds core inputs".into());
                }
                (input_count, tail)
            };
            let inputs = signature
                .inputs
                .iter()
                .chain(signature.varargs.iter().cycle())
                .take(input_count)
                .collect::<Vec<_>>();
            if view.trait_impl.is_none() {
                if view.borrowed_self {
                    return Err("borrowed Self requires a Rust trait view".into());
                }
                let owner = match &view.owner {
                    Some(pb::BindingOwner {
                        kind: Some(pb::binding_owner::Kind::Sort(sort)),
                    }) => Some(types.get(sort).ok_or("unsupported Rust member owner")?),
                    None => None,
                    _ => return Err("unsupported Rust member owner".into()),
                };
                let method = if let Some(owner) = owner {
                    if view.path.len() != 1 {
                        return Err("Rust member requires one path component".into());
                    }
                    if !implementations.insert((
                        format!("self::{owner}"),
                        String::new(),
                        vec![view.path[0].clone()],
                    )) {
                        return Err("duplicate scalar Rust method".into());
                    }
                    &view.path[0]
                } else {
                    if view.path.len() != 4
                        || view.path[..3] != ["egglog_experimental", "typed", "builtins"]
                        || view.receiver.is_some()
                    {
                        return Err("unsupported closed Rust free function path".into());
                    }
                    if !public_names.insert(view.path[3].clone()) {
                        return Err("Rust free function name collision".into());
                    }
                    &view.path[3]
                };
                identifier(method)?;
                let mut arguments = vec![None; inputs.len()];
                let mut params = vec![];
                if let Some(receiver) = &view.receiver {
                    let slot = receiver.core_input.ok_or("missing receiver slot")? as usize;
                    let input = inputs.get(slot).ok_or("receiver slot out of range")?;
                    if types.get(&input.sort) != owner {
                        return Err("Rust receiver differs from owner".into());
                    }
                    arguments[slot] = Some("::core::clone::Clone::clone(&self.0)".to_string());
                    params.push(if receiver.borrowed { "&self" } else { "self" }.into());
                }
                let mut tail_argument = None;
                for (position, param) in view.params.iter().enumerate() {
                    identifier(&param.name)?;
                    if param.borrowed {
                        return Err("borrowed scalar parameter views are not supported yet".into());
                    }
                    let slot = param.core_input.ok_or("missing parameter slot")? as usize;
                    let name = local_name(&format!("arg_{position}"), &occupied);
                    if let Some(input) = inputs.get(slot) {
                        if arguments[slot].is_some() {
                            return Err("repeated scalar Rust input slot".into());
                        }
                        let ty = types
                            .get(&input.sort)
                            .ok_or("unsupported scalar Rust input")?;
                        params.push(format!("{name}: impl ::core::convert::Into<self::{ty}>"));
                        arguments[slot] = Some(format!(
                            "{{ let {value_local}: self::{ty} = ::core::convert::Into::into({name}); ::core::clone::Clone::clone(&{value_local}.0) }}"
                        ));
                    } else if slot == inputs.len()
                        && position + 1 == view.params.len()
                        && tail_argument.is_none()
                        && let Some(tail) = tail
                    {
                        let ty = types
                            .get(&tail.sort)
                            .ok_or("unsupported scalar Rust tail")?;
                        params.push(format!("{name}: impl ::core::iter::IntoIterator<Item = impl ::core::convert::Into<self::{ty}>>"));
                        tail_argument = Some((name, ty));
                    } else {
                        return Err("invalid scalar Rust input mapping".into());
                    }
                }
                if arguments.iter().any(Option::is_none)
                    || tail_argument.is_some() != tail.is_some()
                {
                    return Err("scalar Rust view omits a core input".into());
                }
                let arguments = arguments
                    .into_iter()
                    .map(Option::unwrap)
                    .collect::<Vec<_>>()
                    .join(", ");
                let args = local_name("args", &occupied);
                let mutability = if tail_argument.is_some() { "mut " } else { "" };
                let tail_code = tail_argument.map_or_else(String::new, |(name, ty)| format!("for {value_local} in ::core::iter::IntoIterator::into_iter({name}) {{ let {value_local}: self::{ty} = ::core::convert::Into::into({value_local}); {args}.push(::core::clone::Clone::clone(&{value_local}.0)); }}"));
                if let Some(owner) = owner {
                    writeln!(source, "impl self::{owner} {{").unwrap();
                }
                let params = params.join(", ");
                writeln!(source, r#"
    /// Author a catalog-defined call without evaluating its arguments.
    pub fn {method}({params}) -> {output} {{
        let {mutability}{args} = ::std::vec![{arguments}];
        {tail_code}
        let mut {record_local} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record_local}.arena = crate::typed::storage::Arena::Declaration;
        {record_local}.index = {index};
        <{output} as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(
            &crate::typed::decl::Callable({record_local}), {args},
            <{output} as crate::typed::EgglogValue>::sort_ref(),
        ).expect("generated scalar call disagrees with its descriptor"))
    }}
"#).unwrap();
                if owner.is_some() {
                    writeln!(source, "}}").unwrap();
                }
                continue;
            }
            let Some(pb::binding_owner::Kind::Sort(owner)) =
                view.owner.as_ref().and_then(|o| o.kind.as_ref())
            else {
                return Err("scalar operator needs a sort owner".into());
            };
            let owner = types.get(owner).ok_or("unsupported Rust owner sort")?;
            let receiver = view.receiver.as_ref().ok_or("missing receiver")?;
            let receiver_index = receiver.core_input.ok_or("missing receiver slot")? as usize;
            let trait_impl = view.trait_impl.as_ref().ok_or("missing Rust trait")?;
            let (trait_name, method, arity) = match trait_impl.path.as_slice() {
                [root, ops, name] if root == "core" && ops == "ops" => match name.as_str() {
                    "Add" => (name, "add", 2),
                    "Sub" => (name, "sub", 2),
                    "Mul" => (name, "mul", 2),
                    "Div" => (name, "div", 2),
                    "Rem" => (name, "rem", 2),
                    "Neg" => (name, "neg", 1),
                    "Not" => (name, "not", 1),
                    "BitAnd" => (name, "bitand", 2),
                    "BitOr" => (name, "bitor", 2),
                    "BitXor" => (name, "bitxor", 2),
                    "Shl" => (name, "shl", 2),
                    "Shr" => (name, "shr", 2),
                    _ => return Err("unsupported scalar Rust trait".into()),
                },
                _ => return Err("unsupported scalar Rust trait path".into()),
            };
            if view.path != [method]
                || view.borrowed_self
                || receiver.borrowed
                || view.params.len() != arity - 1
                || inputs.len() != arity
                || tail.is_some()
                || trait_impl.args.len() != arity - 1
                || trait_impl.output_associated_type.as_deref() != Some("Output")
            {
                return Err(format!(
                    "unsupported scalar Rust view for {}",
                    primitive.name
                ));
            }
            if receiver_index >= arity || types.get(&inputs[receiver_index].sort) != Some(owner) {
                return Err("Rust receiver mapping disagrees with signature".into());
            }
            if arity == 1 {
                for borrowed_self in [false, true] {
                    let self_type =
                        format!("{}self::{owner}", if borrowed_self { "&" } else { "" });
                    if !implementations.insert((
                        self_type.clone(),
                        trait_impl.path.join("::"),
                        vec![],
                    )) {
                        return Err(format!(
                            "Rust {trait_name} implementation collision: {self_type}"
                        ));
                    }
                    writeln!(source, r#"
impl ::core::ops::{trait_name} for {self_type} {{
    type Output = {output};
    fn {method}(self) -> Self::Output {{
        let mut {record_local} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record_local}.arena = crate::typed::storage::Arena::Declaration;
        {record_local}.index = {index};
        <{output} as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(
            &crate::typed::decl::Callable({record_local}), ::std::vec![::core::clone::Clone::clone(&self.0)],
            <{output} as crate::typed::EgglogValue>::sort_ref(),
        ).expect("generated scalar operator disagrees with its descriptor"))
    }}
}}
"#).unwrap();
                }
                continue;
            }
            let rhs = &view.params[0];
            identifier(&rhs.name)?;
            let rhs_index = rhs.core_input.ok_or("missing parameter slot")? as usize;
            if receiver_index >= 2
                || rhs_index >= 2
                || receiver_index == rhs_index
                || rhs.borrowed
                || trait_impl.args[0].borrowed
                || types.get(
                    &trait_impl.args[0]
                        .sort
                        .ok_or("missing trait argument sort")?,
                ) != types.get(&inputs[rhs_index].sort)
            {
                return Err(
                    "Rust receiver/parameter/trait mapping disagrees with signature".into(),
                );
            }
            let rhs_type = types
                .get(&inputs[rhs_index].sort)
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
                    if !implementations.insert((
                        self_type.clone(),
                        trait_impl.path.join("::"),
                        vec![param_type.clone()],
                    )) {
                        return Err(format!(
                            "Rust {trait_name} implementation collision: {self_type}, {param_type}"
                        ));
                    }
                    let mut arguments = [String::new(), String::new()];
                    arguments[receiver_index] = "::core::clone::Clone::clone(&self.0)".into();
                    arguments[rhs_index] = format!("::core::clone::Clone::clone(&{rhs_name}.0)");
                    let arguments = arguments.join(", ");
                    let call = if signature.varargs.is_empty() {
                        format!(
                            "crate::typed::expr::Expr::call(&crate::typed::decl::Callable({record_local}), ::std::vec![{arguments}])"
                        )
                    } else {
                        format!(
                            "crate::typed::expr::Expr::call_with_result(&crate::typed::decl::Callable({record_local}), ::std::vec![{arguments}], <{output} as crate::typed::EgglogValue>::sort_ref()).expect(\"generated scalar operator disagrees with its descriptor\")"
                        )
                    };
                    writeln!(
                        source,
                        r#"
impl ::core::ops::{trait_name}<{param_type}> for {self_type} {{
    type Output = {output};
    fn {method}(self, {rhs_name}: {param_type}) -> Self::Output {{
        let mut {record_local} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record_local}.arena = crate::typed::storage::Arena::Declaration;
        {record_local}.index = {index};
        <{output} as crate::typed::EgglogValue>::from_expression({call})
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
            } else if let pb::sort::Kind::Func(f) = kind {
                pending.extend(
                    f.params
                        .iter()
                        .chain([&f.result])
                        .rev()
                        .map(|child| (*child, false)),
                );
            }
            continue;
        }
        let ty = match kind {
            pb::sort::Kind::Var(i) => parameters
                .get(*i as usize)
                .ok_or("unbound Rust type parameter")?
                .clone(),
            pb::sort::Kind::Family(f) => {
                if !matches!(
                    f.name.as_str(),
                    "i64"
                        | "f64"
                        | "String"
                        | "bool"
                        | "Unit"
                        | "BigInt"
                        | "BigRat"
                        | "Rational"
                        | "Vec"
                        | "Set"
                        | "MultiSet"
                        | "Pair"
                        | "Map"
                        | "Maybe"
                ) {
                    return Err("Rust sort has no supported value codec".into());
                }
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
            pb::sort::Kind::Func(f) => {
                let args = f
                    .params
                    .iter()
                    .map(|i| format!("{},", rendered[i]))
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("self::Function<({args}), {}>", rendered[&f.result])
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

// Container payload codecs are schema-defined, like the scalar codecs above. The
// public path/arity comes from the actual family declaration, not a method map.
fn emit_container_type(
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
        .ok_or("missing container binding")?;
    let arity = match family.name.as_str() {
        "Vec" | "Set" | "MultiSet" | "Maybe" => 1,
        "Pair" | "Map" => 2,
        _ => return Err("unsupported container codec".into()),
    };
    if family.arity as usize != arity
        || binding.path.len() != 4
        || binding.path[..3] != ["egglog_experimental", "typed", "builtins"]
        || (!binding.type_params.is_empty() && binding.type_params.len() != arity)
    {
        return Err("unsupported container type binding".into());
    }
    let name = &binding.path[3];
    let parameters = generic_parameters(program, arity);
    let types = parameters.join(", ");
    let generics = parameters
        .iter()
        .map(|t| format!("{t}: crate::typed::EgglogValue"))
        .collect::<Vec<_>>()
        .join(", ");
    let sorts = parameters
        .iter()
        .map(|t| format!("<{t} as crate::typed::EgglogValue>::sort_ref()"))
        .collect::<Vec<_>>()
        .join(", ");
    let phantom = if arity == 1 {
        types.clone()
    } else {
        format!("({types})")
    };
    let description = match family.name.as_str() {
        "Vec" => "ordered vector",
        "Set" => "set with unspecified native enumeration",
        "MultiSet" => "multiset preserving repeated values",
        "Pair" => "ordered pair",
        "Map" => "map",
        "Maybe" => "optional value",
        _ => unreachable!(),
    };
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let items = local_name("items", occupied);
    let child = local_name("child", occupied);
    writeln!(source, r#"
/// A protobuf-owned {description} expression. Native calls remain symbolic.
#[derive(::core::clone::Clone, ::core::fmt::Debug, ::core::cmp::PartialEq, ::core::cmp::Eq, ::core::hash::Hash)]
pub struct {name}<{generics}>(crate::typed::expr::Expr, ::core::marker::PhantomData<fn() -> {phantom}>);
impl<{generics}> crate::typed::expr::ValueInput for self::{name}<{types}> {{ type Owned = Self; }}
impl<{generics}> ::core::convert::From<&self::{name}<{types}>> for self::{name}<{types}> {{
    fn from({value}: &Self) -> Self {{ ::core::clone::Clone::clone({value}) }}
}}
impl<{generics}> crate::typed::EgglogValue for self::{name}<{types}> {{
    fn sort_ref() -> crate::typed::SortRef {{
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {index};
        crate::typed::SortRef::family(&{record}, ::std::vec![{sorts}]).expect("generated family arity")
    }}
    fn expression(&self) -> &crate::typed::expr::Expr {{ &self.0 }}
    fn from_expression({value}: crate::typed::expr::Expr) -> Self {{ Self({value}, ::core::marker::PhantomData) }}
}}
"#).unwrap();
    if family.name == "Map" {
        emit_map_codec(program, name, &parameters, source, occupied)?;
    } else if family.name == "Maybe" {
        let mut constructors = vec![];
        let owner = format!("self::{name}<{types}>");
        for (key, arity) in [("none", 0), ("some", 1)] {
            let identity = format!("egglog.experimental.maybe.{key}");
            let (index, signature) = program
                .declarations
                .iter()
                .enumerate()
                .find_map(|(i, d)| {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) = &d.kind else {
                        return None;
                    };
                    if p.name != identity {
                        return None;
                    }
                    let Some(pb::host_primitive::Typing::Signature(s)) = &p.typing else {
                        return None;
                    };
                    Some((i, s))
                })
                .ok_or("missing catalog Maybe constructor")?;
            if signature.type_params.len() != 1
                || !signature.equality_type_params.is_empty()
                || signature.inputs.len() != arity
                || !signature.varargs.is_empty()
                || rust_type(
                    program,
                    signature.output.ok_or("missing Maybe result")?,
                    &parameters,
                )? != owner
                || signature
                    .inputs
                    .iter()
                    .any(|a| rust_type(program, a.sort, &parameters).as_ref() != Ok(&parameters[0]))
            {
                return Err(
                    "catalog Maybe constructor does not match the optional-child codec".into(),
                );
            }
            constructors.push(index);
        }
        let t = &parameters[0];
        let none = local_name("none", occupied);
        let some = local_name("some", occupied);
        let [none_index, some_index] = constructors.as_slice() else {
            unreachable!()
        };
        writeln!(source, r#"
impl<{t}: crate::typed::EgglogValue> ::core::convert::TryFrom<&{owner}> for ::core::option::Option<{t}> {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: &{owner}) -> ::core::result::Result<Self, Self::Error> {{
        let mut {none} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {none}.arena = crate::typed::storage::Arena::Declaration;
        {none}.index = {none_index};
        let mut {some} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {some}.arena = crate::typed::storage::Arena::Declaration;
        {some}.index = {some_index};
        ::core::result::Result::Ok({value}.0.maybe_value(
            [&crate::typed::decl::Callable({none}), &crate::typed::decl::Callable({some})],
            &<{t} as crate::typed::EgglogValue>::sort_ref(),
        )?.map(<{t} as crate::typed::EgglogValue>::from_expression))
    }}
}}
"#).unwrap();
    } else if matches!(family.name.as_str(), "Vec" | "Set" | "MultiSet") {
        let t = &parameters[0];
        let family_name = &family.name;
        writeln!(source, r#"
impl<{t}: crate::typed::EgglogValue> ::core::convert::TryFrom<&self::{name}<{t}>> for ::std::vec::Vec<{t}> {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: &self::{name}<{t}>) -> ::core::result::Result<Self, Self::Error> {{
        let mut {items} = ::std::vec::Vec::new();
        for {child} in {value}.0.sequence_elements(&<{t} as crate::typed::EgglogValue>::sort_ref(), {family_name:?})? {{
            {items}.push(<{t} as crate::typed::EgglogValue>::from_expression({child}));
        }}
        ::core::result::Result::Ok({items})
    }}
}}
"#).unwrap();
    } else {
        // This identity is the schema Pair codec's native constructor, not a
        // presentation name. Check its actual scheme before emitting tuples.
        let (make, signature) = program
            .declarations
            .iter()
            .enumerate()
            .find_map(|(index, d)| {
                let Some(pb::declaration::Kind::HostPrimitive(p)) = &d.kind else {
                    return None;
                };
                if p.name != "egglog.core.pair.make" {
                    return None;
                }
                let Some(pb::host_primitive::Typing::Signature(s)) = &p.typing else {
                    return None;
                };
                Some((index, s))
            })
            .ok_or("missing catalog Pair constructor")?;
        let owner = format!("self::{name}<{types}>");
        if signature.type_params.len() != arity
            || !signature.equality_type_params.is_empty()
            || signature.inputs.len() != arity
            || !signature.varargs.is_empty()
            || rust_type(
                program,
                signature.output.ok_or("missing Pair output")?,
                &parameters,
            )? != owner
            || signature
                .inputs
                .iter()
                .zip(&parameters)
                .any(|(arg, ty)| rust_type(program, arg.sort, &parameters).as_ref() != Ok(ty))
        {
            return Err("catalog Pair constructor does not match the two-child codec".into());
        }
        let left = local_name("left", occupied);
        let right = local_name("right", occupied);
        let l = &parameters[0];
        let r = &parameters[1];
        let input_parameters = generic_parameters(program, 4);
        let a = &input_parameters[2];
        let b = &input_parameters[3];
        writeln!(source, r#"
impl<{generics}> {owner} {{
    /// Inspect direct ordered fields without evaluating symbolic children.
    pub fn fields(&self) -> ::core::result::Result<({types}), crate::typed::TypedError> {{
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {make};
        let [{left}, {right}] = self.0.pair_fields(&crate::typed::decl::Callable({record}), &<{l} as crate::typed::EgglogValue>::sort_ref(), &<{r} as crate::typed::EgglogValue>::sort_ref())?;
        ::core::result::Result::Ok((<{l} as crate::typed::EgglogValue>::from_expression({left}), <{r} as crate::typed::EgglogValue>::from_expression({right})))
    }}
}}
impl<{generics}, {a}: ::core::convert::Into<{l}>, {b}: ::core::convert::Into<{r}>> ::core::convert::From<({a}, {b})> for {owner} {{
    fn from({value}: ({a}, {b})) -> Self {{
        let {left}: {l} = ::core::convert::Into::into({value}.0);
        let {right}: {r} = ::core::convert::Into::into({value}.1);
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {make};
        <Self as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(
            &crate::typed::decl::Callable({record}), ::std::vec![::core::clone::Clone::clone(<{l} as crate::typed::EgglogValue>::expression(&{left})), ::core::clone::Clone::clone(<{r} as crate::typed::EgglogValue>::expression(&{right}))],
            <Self as crate::typed::EgglogValue>::sort_ref(),
        ).expect("generated Pair codec disagrees with its descriptor"))
    }}
}}
impl<{generics}> ::core::convert::TryFrom<&{owner}> for ({types}) {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: &{owner}) -> ::core::result::Result<Self, Self::Error> {{ {value}.fields() }}
}}
impl<{generics}> ::core::convert::TryFrom<{owner}> for ({types}) {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: {owner}) -> ::core::result::Result<Self, Self::Error> {{ {value}.fields() }}
}}
"#).unwrap();
    }
    Ok(())
}

// Map's host tuple packing and direct inspection share the actual catalog
// constructors. Validate their nested codec shapes, independently of public
// presentation names and physical declaration/sort locations.
fn emit_map_codec(
    program: &pb::Program,
    name: &str,
    parameters: &[String],
    source: &mut String,
    occupied: &HashSet<&str>,
) -> Result<(), String> {
    let mut constructors = vec![];
    for identity in [
        "egglog.core.map.empty",
        "egglog.core.map.of",
        "egglog.core.vec.empty",
        "egglog.core.vec.of",
        "egglog.core.pair.make",
    ] {
        let constructor = program
            .declarations
            .iter()
            .enumerate()
            .find_map(|(i, d)| {
                let Some(pb::declaration::Kind::HostPrimitive(p)) = &d.kind else {
                    return None;
                };
                let Some(pb::host_primitive::Typing::Signature(s)) = &p.typing else {
                    return None;
                };
                (p.name == identity).then_some((i, s))
            })
            .ok_or_else(|| format!("missing catalog Map codec constructor {identity}"))?;
        constructors.push(constructor);
    }
    let [
        (_, empty),
        (of_index, of),
        (_, vec_empty),
        (vec_of_index, vec_of),
        (_, pair_make),
    ] = constructors.as_slice()
    else {
        unreachable!()
    };
    let types = parameters.join(", ");
    let owner = format!("self::{name}<{types}>");
    let pair_type = rust_type(
        program,
        pair_make.output.ok_or("missing Pair output")?,
        parameters,
    )?;
    let Some(pb::sort::Kind::Family(pair_family)) = program
        .sorts
        .get(pair_make.output.unwrap() as usize)
        .and_then(|s| s.kind.as_ref())
    else {
        return Err("Map codec requires a Pair family result".into());
    };
    if pair_family.name != "Pair"
        || pair_family.args.len() != 2
        || pair_make.type_params.len() != 2
        || !pair_make.equality_type_params.is_empty()
        || pair_make.inputs.len() != 2
        || !pair_make.varargs.is_empty()
        || pair_make
            .inputs
            .iter()
            .zip(parameters)
            .any(|(arg, ty)| rust_type(program, arg.sort, parameters).as_ref() != Ok(ty))
        || pair_family
            .args
            .iter()
            .zip(parameters)
            .any(|(arg, ty)| rust_type(program, *arg, parameters).as_ref() != Ok(ty))
    {
        return Err("catalog Pair constructor does not match Map's tuple codec".into());
    }
    let vec_type = rust_type(
        program,
        vec_of.output.ok_or("missing Vec output")?,
        std::slice::from_ref(&pair_type),
    )?;
    let Some(pb::sort::Kind::Family(vec_family)) = program
        .sorts
        .get(vec_of.output.unwrap() as usize)
        .and_then(|s| s.kind.as_ref())
    else {
        return Err("Map codec requires a Vec family result".into());
    };
    if vec_family.name != "Vec"
        || vec_family.args.len() != 1
        || vec_of.type_params.len() != 1
        || !vec_of.equality_type_params.is_empty()
        || !vec_of.inputs.is_empty()
        || vec_of.varargs.len() != 1
        || rust_type(
            program,
            vec_family.args[0],
            std::slice::from_ref(&pair_type),
        )? != pair_type
        || rust_type(
            program,
            vec_of.varargs[0].sort,
            std::slice::from_ref(&pair_type),
        )? != pair_type
        || vec_empty.type_params.len() != 1
        || !vec_empty.equality_type_params.is_empty()
        || !vec_empty.inputs.is_empty()
        || !vec_empty.varargs.is_empty()
        || rust_type(
            program,
            vec_empty.output.ok_or("missing Vec empty output")?,
            std::slice::from_ref(&pair_type),
        )? != vec_type
        || empty.type_params.len() != 2
        || !empty.equality_type_params.is_empty()
        || !empty.inputs.is_empty()
        || !empty.varargs.is_empty()
        || rust_type(
            program,
            empty.output.ok_or("missing Map empty output")?,
            parameters,
        )? != owner
        || of.type_params.len() != 2
        || !of.equality_type_params.is_empty()
        || of.inputs.len() != 1
        || !of.varargs.is_empty()
        || rust_type(program, of.output.ok_or("missing Map output")?, parameters)? != owner
        || rust_type(program, of.inputs[0].sort, parameters)? != vec_type
    {
        return Err("catalog Map constructor does not match the Vec-of-Pair codec".into());
    }
    let generics = parameters
        .iter()
        .map(|t| format!("{t}: crate::typed::EgglogValue"))
        .collect::<Vec<_>>()
        .join(", ");
    let inputs = generic_parameters(program, 5);
    let (k, v, a, b, i) = (
        &parameters[0],
        &parameters[1],
        &inputs[2],
        &inputs[3],
        &inputs[4],
    );
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let items = local_name("items", occupied);
    let left = local_name("left", occupied);
    let right = local_name("right", occupied);
    let pair = local_name("pair", occupied);
    let index = local_name("index", occupied);
    let callables = local_name("constructors", occupied);
    let indices = constructors
        .iter()
        .map(|(i, _)| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(source, r#"
impl<{generics}> {owner} {{
    /// Pack tuples once in iterator order, preserving symbolic children and duplicates.
    pub fn of<{i}, {a}, {b}>({value}: {i}) -> Self
    where {i}: ::core::iter::IntoIterator<Item = ({a}, {b})>, {a}: ::core::convert::Into<{k}>, {b}: ::core::convert::Into<{v}> {{
        let {items} = ::core::iter::IntoIterator::into_iter({value}).map(|({left}, {right})| {{
            let {pair}: {pair_type} = ::core::convert::From::from(({left}, {right}));
            ::core::clone::Clone::clone(<{pair_type} as crate::typed::EgglogValue>::expression(&{pair}))
        }}).collect();
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {vec_of_index};
        let {value} = crate::typed::expr::Expr::call_with_result(&crate::typed::decl::Callable({record}), {items}, <{vec_type} as crate::typed::EgglogValue>::sort_ref()).expect("generated Map Vec packing disagrees with its descriptor");
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Declaration;
        {record}.index = {of_index};
        <Self as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(&crate::typed::decl::Callable({record}), ::std::vec![{value}], <Self as crate::typed::EgglogValue>::sort_ref()).expect("generated Map packing disagrees with its descriptor"))
    }}
    /// Inspect direct entries without evaluating computations or normalizing keys.
    pub fn entries(&self) -> ::core::result::Result<::std::vec::Vec<({types})>, crate::typed::TypedError> {{
        let {callables} = [{indices}].map(|{index}| {{
            let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
            {record}.arena = crate::typed::storage::Arena::Declaration;
            {record}.index = {index};
            crate::typed::decl::Callable({record})
        }});
        ::core::result::Result::Ok(self.0.map_entries({callables}.each_ref(), &<{k} as crate::typed::EgglogValue>::sort_ref(), &<{v} as crate::typed::EgglogValue>::sort_ref())?.into_iter().map(|[{left}, {right}]| (<{k} as crate::typed::EgglogValue>::from_expression({left}), <{v} as crate::typed::EgglogValue>::from_expression({right}))).collect())
    }}
}}
impl<{generics}, {a}: ::core::convert::Into<{k}>, {b}: ::core::convert::Into<{v}>> ::core::convert::From<::std::vec::Vec<({a}, {b})>> for {owner} {{
    fn from({value}: ::std::vec::Vec<({a}, {b})>) -> Self {{ Self::of({value}) }}
}}
impl<{generics}> ::core::convert::TryFrom<&{owner}> for ::std::vec::Vec<({types})> {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: &{owner}) -> ::core::result::Result<Self, Self::Error> {{ {value}.entries() }}
}}
impl<{generics}> ::core::convert::TryFrom<{owner}> for ::std::vec::Vec<({types})> {{
    type Error = crate::typed::TypedError;
    fn try_from({value}: {owner}) -> ::core::result::Result<Self, Self::Error> {{ {value}.entries() }}
}}
"#).unwrap();
    Ok(())
}

fn emit_generic_views(
    program: &pb::Program,
    index: usize,
    source: &mut String,
    implementations: &mut HashSet<(String, String, Vec<String>)>,
    public_names: &mut HashSet<String>,
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
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let args = local_name("args", occupied);
    for view in &rust.views {
        if view.tail_repetitions.is_some() {
            return Err("specialized generic Rust views are not supported yet".into());
        }
        let mut anchors = vec![None; parameters.len()];
        let mut concrete_inputs = false;
        let mut owner_parameter_count = 0;
        let (owner, method, types, bound) = if view.owner.is_none() {
            if view.path.len() != 4
                || view.path[..3] != ["egglog_experimental", "typed", "builtins"]
                || view.receiver.is_some()
                || view.trait_impl.is_some()
                || view.borrowed_self
                || !signature.varargs.is_empty()
            {
                return Err("unsupported generic Rust free function view".into());
            }
            if !public_names.insert(view.path[3].clone()) {
                return Err("Rust free function name collision".into());
            }
            // A direct input fixes each binder's Owned type. Repeated occurrences
            // can then use Into without ambiguous all-Into generic inference.
            for (position, param) in view.params.iter().enumerate() {
                let slot = param.core_input.ok_or("missing parameter slot")? as usize;
                let input = signature
                    .inputs
                    .get(slot)
                    .ok_or("invalid generic input mapping")?;
                if let Some(pb::sort::Kind::Var(binder)) = program
                    .sorts
                    .get(input.sort as usize)
                    .and_then(|s| s.kind.as_ref())
                {
                    anchors
                        .get_mut(*binder as usize)
                        .ok_or("unbound Rust type parameter")?
                        .get_or_insert(position);
                }
            }
            concrete_inputs = anchors.iter().any(Option::is_none);
            if concrete_inputs {
                let mut determined = vec![false; parameters.len()];
                let mut pending = signature
                    .inputs
                    .iter()
                    .map(|arg| arg.sort)
                    .collect::<Vec<_>>();
                let mut seen = HashSet::new();
                while let Some(index) = pending.pop() {
                    if !seen.insert(index) {
                        continue;
                    }
                    match program
                        .sorts
                        .get(index as usize)
                        .and_then(|sort| sort.kind.as_ref())
                    {
                        Some(pb::sort::Kind::Var(i)) => {
                            *determined
                                .get_mut(*i as usize)
                                .ok_or("unbound Rust type parameter")? = true
                        }
                        Some(pb::sort::Kind::Family(f)) => pending.extend(&f.args),
                        Some(pb::sort::Kind::Func(f)) => {
                            pending.extend(f.params.iter().chain([&f.result]))
                        }
                        _ => (),
                    }
                }
                if determined.iter().any(|value| !value) {
                    return Err(
                        "generic Rust free function requires an input anchor for every binder"
                            .into(),
                    );
                }
            }
            if concrete_inputs {
                anchors.fill(None);
            }
            let types = parameters
                .iter()
                .map(|t| {
                    if concrete_inputs {
                        t.clone()
                    } else {
                        format!("<{t} as crate::typed::expr::ValueInput>::Owned")
                    }
                })
                .collect::<Vec<_>>();
            (
                None,
                &view.path[3],
                types,
                if concrete_inputs {
                    "crate::typed::EgglogValue"
                } else {
                    "crate::typed::expr::ValueInput"
                },
            )
        } else {
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
            if !matches!(
                family.name.as_str(),
                "Vec" | "Set" | "MultiSet" | "Pair" | "Map" | "Maybe"
            ) || family.args.len() > parameters.len()
                || view.path.len() != 1
                || view.trait_impl.is_some()
                || view.borrowed_self
            {
                return Err("unsupported generic Rust member view".into());
            }
            owner_parameter_count = family.args.len();
            for (position, sort) in family.args.iter().enumerate() {
                if !matches!(program.sorts.get(*sort as usize).and_then(|s| s.kind.as_ref()), Some(pb::sort::Kind::Var(i)) if *i as usize == position)
                {
                    return Err("generic owner must determine its binder in family order".into());
                }
            }
            let owner = rust_type(program, *owner, &parameters)?;
            let method = &view.path[0];
            identifier(method)?;
            if family.name == "Pair" && method == "fields" {
                return Err("generic Rust method collides with Pair codec fields".into());
            }
            if family.name == "Map" && matches!(method.as_str(), "of" | "entries") {
                return Err("generic Rust method collides with Map codec".into());
            }
            if !implementations.insert((owner.clone(), String::new(), vec![method.clone()])) {
                return Err("duplicate generic Rust method".into());
            }
            (
                Some(owner),
                method,
                parameters.clone(),
                "crate::typed::EgglogValue",
            )
        };
        identifier(method)?;
        let generics = parameters
            .iter()
            .enumerate()
            .map(|(i, t)| {
                if (owner.is_some() || concrete_inputs)
                    && signature.equality_type_params.contains(&(i as u32))
                {
                    format!("{t}: crate::typed::EqualitySort")
                } else {
                    format!("{t}: {bound}")
                }
            })
            .collect::<Vec<_>>();
        let output = rust_type(
            program,
            signature.output.ok_or("missing generic output")?,
            &types,
        )?;
        let consumes_tail = view
            .receiver
            .is_some_and(|r| r.core_input == Some(signature.inputs.len() as u32));
        if consumes_tail && signature.varargs.len() != 1 {
            return Err("tail receiver requires a homogeneous variadic signature".into());
        }
        let mut inputs = vec![None; signature.inputs.len() + usize::from(consumes_tail)];
        let mut tail = None;
        let mut params = vec![];
        if let Some(receiver) = &view.receiver {
            let slot = receiver.core_input.ok_or("missing receiver slot")? as usize;
            let input = signature
                .inputs
                .get(slot)
                .or_else(|| consumes_tail.then(|| &signature.varargs[0]))
                .ok_or("receiver slot out of range")?;
            if Some(rust_type(program, input.sort, &types)?) != owner {
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
                let ty = rust_type(
                    program,
                    signature
                        .inputs
                        .get(slot)
                        .unwrap_or_else(|| &signature.varargs[0])
                        .sort,
                    &types,
                )?;
                if inputs[slot].is_some() {
                    return Err("repeated generic input slot".into());
                }
                if let Some(binder) = anchors.iter().position(|anchor| *anchor == Some(position)) {
                    params.push(format!("{name}: {}", parameters[binder]));
                    inputs[slot] = Some(format!(
                        "::core::clone::Clone::clone(<{ty} as crate::typed::EgglogValue>::expression(::std::borrow::Borrow::borrow(&{name})))"
                    ));
                } else if concrete_inputs
                    || (owner.is_some() && owner_parameter_count < parameters.len())
                {
                    params.push(format!("{name}: {ty}"));
                    inputs[slot] = Some(format!(
                        "::core::clone::Clone::clone(<{ty} as crate::typed::EgglogValue>::expression(&{name}))"
                    ));
                } else {
                    params.push(format!("{name}: impl ::core::convert::Into<{ty}>"));
                    inputs[slot] = Some(format!(
                        "{{ let {value}: {ty} = ::core::convert::Into::into({name}); ::core::clone::Clone::clone(<{ty} as crate::typed::EgglogValue>::expression(&{value})) }}"
                    ));
                }
            } else if slot == inputs.len() && position + 1 == view.params.len() && tail.is_none() {
                let ty = rust_type(
                    program,
                    signature
                        .varargs
                        .first()
                        .ok_or("unexpected tail slot")?
                        .sort,
                    &types,
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
        let restrictions =
            if owner.is_none() && !concrete_inputs && !signature.equality_type_params.is_empty() {
                format!(
                    " where {}",
                    signature
                        .equality_type_params
                        .iter()
                        .map(|i| { format!("{}: crate::typed::EqualitySort", types[*i as usize]) })
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                String::new()
            };
        let (prefix, suffix, method_generics) = match owner {
            Some(owner) => (
                format!(
                    "impl<{}> {owner} {{",
                    generics[..owner_parameter_count].join(", ")
                ),
                "}",
                if owner_parameter_count == generics.len() {
                    String::new()
                } else {
                    format!("<{}>", generics[owner_parameter_count..].join(", "))
                },
            ),
            None => (String::new(), "", format!("<{}>", generics.join(", "))),
        };
        writeln!(source, r#"
{prefix}
    /// Author a catalog-defined call without evaluating its arguments.
    pub fn {method}{method_generics}({params}) -> {output}{restrictions} {{
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
{suffix}
"#).unwrap();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const DEFERRED: [&str; 0] = [];

    #[test]
    fn complete_native_catalog_uses_existing_generic_and_function_views() {
        let program = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let before = program.encode_to_vec();
        let (source, deferred) = generate(&program).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert_eq!(program.encode_to_vec(), before);
        for method in [
            "pub fn guard(&self)",
            "pub fn bool_eq(&self,",
            "pub fn bool_ne<__EgglogType0: crate::typed::expr::ValueInput>",
            "pub fn value_eq<__EgglogType0: crate::typed::expr::ValueInput>",
            "pub fn map<__EgglogType1: crate::typed::EgglogValue>(&self, __egglog_arg_0: self::Function<(__EgglogType0,), __EgglogType1>) -> self::Vec<__EgglogType1>",
            "pub fn fold_kv<__EgglogType2: crate::typed::EgglogValue>(&self, __egglog_arg_0: self::Function<(__EgglogType2, __EgglogType0, __EgglogType1,), __EgglogType2>, __egglog_arg_1: __EgglogType2) -> __EgglogType2",
            "pub fn catch(__egglog_arg_0: impl ::core::convert::Into<self::Function<(), __EgglogType0>>) -> self::Maybe<__EgglogType0>",
            "pub fn match_<__EgglogType1: crate::typed::EgglogValue>(&self, __egglog_arg_0: self::Function<(__EgglogType0,), __EgglogType1>, __egglog_arg_1: __EgglogType1) -> __EgglogType1",
            "pub fn get_node_size() -> self::I64",
            "pub fn get_table_size(__egglog_arg_0: impl ::core::iter::IntoIterator<Item = impl ::core::convert::Into<self::String>>) -> self::I64",
            "pub fn subst<__EgglogType0: crate::typed::EqualitySort, __EgglogType1: crate::typed::EqualitySort>(__egglog_arg_0: __EgglogType0, __egglog_arg_1: self::Map<__EgglogType1, __EgglogType1>) -> __EgglogType0",
        ] {
            assert!(
                source.contains(method),
                "missing generated method: {method}"
            );
        }
    }

    #[test]
    fn generic_free_functions_follow_binders_slots_names_and_results() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let index = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
                    Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.ne"
                )
            })
            .unwrap();
        let bytes = original.encode_to_vec();
        let baseline = generate(&original).unwrap().0;
        assert_eq!(original.encode_to_vec(), bytes);
        assert!(baseline.contains("pub fn ne<__EgglogType0: crate::typed::expr::ValueInput>(__egglog_arg_0: __EgglogType0, __egglog_arg_1: impl ::core::convert::Into<<__EgglogType0 as crate::typed::expr::ValueInput>::Owned>) -> self::Unit"));
        let mut restricted = original.clone();
        let Some(pb::declaration::Kind::HostPrimitive(primitive)) =
            &mut restricted.declarations[index].kind
        else {
            unreachable!()
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &mut primitive.typing else {
            unreachable!()
        };
        signature.equality_type_params = vec![0];
        let generated = generate(&restricted).unwrap().0;
        assert!(generated.contains("-> self::Unit where <__EgglogType0 as crate::typed::expr::ValueInput>::Owned: crate::typed::EqualitySort"));
        assert!(!baseline.contains("-> self::Unit where <__EgglogType0 as crate::typed::expr::ValueInput>::Owned: crate::typed::EqualitySort"));
        let mut closed = original.clone();
        let primitive = closed
            .declarations
            .iter_mut()
            .find_map(|d| match &mut d.kind {
                Some(pb::declaration::Kind::HostPrimitive(p))
                    if p.name == "egglog.core.i64.add" =>
                {
                    Some(p)
                }
                _ => None,
            })
            .unwrap();
        let Some(pb::host_primitive::Typing::Signature(signature)) = &mut primitive.typing else {
            unreachable!()
        };
        assert!(signature.type_params.is_empty());
        signature.equality_type_params = vec![0];
        assert!(
            generate(&closed)
                .unwrap_err()
                .contains("equality binders must be strictly increasing and in range")
        );
        for (binders, restrictions) in [(1, vec![1]), (1, vec![0, 0]), (2, vec![1, 0])] {
            let mut malformed = original.clone();
            let Some(pb::declaration::Kind::HostPrimitive(p)) =
                &mut malformed.declarations[index].kind
            else {
                unreachable!()
            };
            let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                unreachable!()
            };
            s.type_params.resize(binders, "U".into());
            s.equality_type_params = restrictions;
            assert!(
                generate(&malformed)
                    .unwrap_err()
                    .contains("equality binders must be strictly increasing and in range")
            );
        }
        // Removing just this view leaves every existing family/member body exact.
        let mut absent = original.clone();
        absent.declarations[index].bindings.as_mut().unwrap().rust = None;
        let function = baseline.split_once("\n\n    /// Author a catalog-defined call without evaluating its arguments.\n    pub fn ne<").unwrap();
        let (_, rest) = function.1.split_once("\n    }\n\n\n").unwrap();
        assert!(generate(&absent).unwrap().0 == format!("{}{}", function.0, rest));

        for reverse in [false, true] {
            let mut changed = original.clone();
            let declaration = &mut changed.declarations[index];
            let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind else {
                panic!()
            };
            p.name = "test.generic.renamed".into();
            let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                panic!()
            };
            s.type_params[0] = "not a Rust identifier 🦀".into();
            let view = &mut declaration
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0];
            view.path[3] = "renamed_generic".into();
            view.params.reverse();
            view.params[0].name = "__egglog_record".into();
            if reverse {
                changed.declarations.reverse();
            }
            let bytes = changed.encode_to_vec();
            let source = generate(&changed).unwrap().0;
            assert_eq!(changed.encode_to_vec(), bytes);
            let body = source
                .split_once("pub fn renamed_generic<")
                .unwrap()
                .1
                .split_once("\n    }\n")
                .unwrap()
                .0;
            assert!(body.contains("__egglog_arg_0: __EgglogType0"));
            assert!(body.contains("__egglog_arg_1: impl ::core::convert::Into<<__EgglogType0 as crate::typed::expr::ValueInput>::Owned>"));
            assert!(body.contains("::std::vec![{ let __egglog_value:"));
            assert!(
                body.find("Into::into(__egglog_arg_1)").unwrap()
                    < body.find("Borrow::borrow(&__egglog_arg_0)").unwrap()
            );
            let location = if reverse {
                changed.declarations.len() - 1 - index
            } else {
                index
            };
            assert!(body.contains(&format!(".index = {location};")));
            assert!(!source.contains("test.generic.renamed"));
        }

        // Emitter-only variations: no fabricated provider is executed. Output
        // projection, nested input conversion and separate binders are generic.
        let mut changed = original.clone();
        let var1 = changed.sorts.len() as u32;
        changed.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Var(1)),
            ..Default::default()
        });
        let nested = changed.sorts.len() as u32;
        changed.sorts.push(pb::Sort {
            kind: Some(pb::sort::Kind::Family(pb::HostSort {
                name: "Vec".into(),
                args: vec![var1],
            })),
            ..Default::default()
        });
        let declaration = &mut changed.declarations[index];
        let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
            panic!()
        };
        s.type_params.push("also diagnostic".into());
        s.inputs[1].sort = var1;
        let mut input = s.inputs[1].clone();
        input.sort = nested;
        s.inputs.push(input);
        s.output = Some(nested);
        let view = &mut declaration
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0];
        view.params.push(pb::RustParameter {
            name: "values".into(),
            core_input: Some(2),
            borrowed: false,
        });
        let source = generate(&changed).unwrap().0;
        assert!(source.contains("__EgglogType1: crate::typed::expr::ValueInput"));
        assert!(source.contains("__egglog_arg_1: __EgglogType1"));
        assert!(source.contains("__egglog_arg_2: impl ::core::convert::Into<self::Vec<<__EgglogType1 as crate::typed::expr::ValueInput>::Owned>>"));
        assert!(
            source
                .contains("-> self::Vec<<__EgglogType1 as crate::typed::expr::ValueInput>::Owned>")
        );
    }

    #[test]
    fn generic_free_functions_reject_unsupported_or_ambiguous_views() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let index = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
                    Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.ne"
                )
            })
            .unwrap();
        // Application views select the structural function protocol, rather
        // than treating the marker as a homogeneous generic signature.
        let mut selected_application = original.clone();
        let application = selected_application.declarations.iter_mut().find(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.fn.apply"
        )).unwrap();
        application.bindings.as_mut().unwrap().rust = original.declarations[index]
            .bindings
            .as_ref()
            .unwrap()
            .rust
            .clone();
        assert_eq!(
            generate(&selected_application).unwrap_err(),
            "unsupported Rust function application view"
        );
        for (case, expected) in [
            (0, "missing parameter slot"),
            (1, "repeated generic input slot"),
            (2, "invalid generic input mapping"),
            (3, "generic Rust view omits a core input"),
            (4, "Rust free function name collision"),
            (5, "unsupported generic Rust free function view"),
            (6, "borrowed generic parameter views are not supported yet"),
            (7, "unsupported generic Rust free function view"),
            (8, "unsupported generic Rust free function view"),
            (9, "specialized generic Rust views are not supported yet"),
            (
                10,
                "generic Rust free function requires an input anchor for every binder",
            ),
            (11, "unsupported generic Rust free function view"),
            (12, "Rust free function name collision"),
            (13, "unsupported Rust identifier"),
        ] {
            let mut changed = original.clone();
            let declaration = &mut changed.declarations[index];
            let view = &mut declaration
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0];
            match case {
                0 => view.params[0].core_input = None,
                1 => view.params[1].core_input = Some(0),
                2 => view.params[1].core_input = Some(2),
                3 => {
                    view.params.pop();
                }
                4 => view.path[3] = "I64".into(),
                5 => view.path[0] = "wrong_namespace".into(),
                6 => view.params[1].borrowed = true,
                7 => view.borrowed_self = true,
                8 => view.trait_impl = Some(Default::default()),
                9 => view.tail_repetitions = Some(0),
                10 | 11 => {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind
                    else {
                        panic!()
                    };
                    let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                        panic!()
                    };
                    if case == 10 {
                        s.type_params.push("unanchored".into());
                    } else {
                        s.varargs.push(s.inputs[0].clone());
                    }
                }
                12 => {
                    let view = view.clone();
                    declaration
                        .bindings
                        .as_mut()
                        .unwrap()
                        .rust
                        .as_mut()
                        .unwrap()
                        .views
                        .push(view);
                }
                13 => view.path[3] = "not-a-name".into(),
                _ => unreachable!(),
            }
            let error = generate(&changed).unwrap_err();
            assert!(error.starts_with(expected), "case {case}: {error}");
        }
    }

    #[test]
    fn bignum_operator_traits_follow_actual_input_and_output_sorts() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let bytes = original.encode_to_vec();
        let (source, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert_eq!(original.encode_to_vec(), bytes);
        for borrowed_self in ["", "&"] {
            assert!(source.contains(&format!(
                "impl ::core::ops::Neg for {borrowed_self}self::BigRat"
            )));
            for borrowed_rhs in ["", "&"] {
                for name in ["Shl", "Shr"] {
                    assert!(source.contains(&format!(
                        "impl ::core::ops::{name}<{borrowed_rhs}self::I64> for {borrowed_self}self::BigInt"
                    )));
                    assert!(!source.contains(&format!(
                        "impl ::core::ops::{name}<{borrowed_rhs}self::BigInt> for {borrowed_self}self::BigInt"
                    )));
                }
            }
        }
        for method in ["numer", "denom", "lt", "gt", "le", "ge"] {
            assert!(source.contains(&format!("pub fn {method}(&self")));
        }
        for provider in [
            "egglog.core.bigrat.neg",
            "egglog.core.bigint.shl",
            "egglog.core.bigint.shr",
        ] {
            let mut changed = original.clone();
            let view = changed.declarations.iter_mut().find_map(|declaration| {
                matches!(&declaration.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == provider)
                    .then(|| &mut declaration.bindings.as_mut().unwrap().rust.as_mut().unwrap().views[0])
            }).unwrap();
            view.receiver.as_mut().unwrap().core_input = Some(1);
            assert!(
                generate(&changed).is_err(),
                "invalid receiver admitted for {provider}"
            );
        }
    }

    #[test]
    fn exact_number_codecs_leave_constructor_views_and_records_authoritative() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let bytes = original.encode_to_vec();
        let (source, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert_eq!(original.encode_to_vec(), bytes);
        for (family, host) in [
            ("BigInt", "::num::BigInt"),
            ("BigRat", "::num::BigRational"),
            ("Rational", "::num::rational::Rational64"),
        ] {
            assert!(source.contains(&format!("pub struct {family}(")));
            assert!(source.contains(&format!("TryFrom<&self::{family}> for {host}")));
            let conversion = if family == "BigInt" {
                "From"
            } else {
                "TryFrom"
            };
            assert!(source.contains(&format!(
                "impl ::core::convert::{conversion}<{host}> for self::{family}"
            )));
            assert!(source.contains(&format!(
                "impl ::core::convert::{conversion}<&{host}> for self::{family}"
            )));
            if family != "BigInt" {
                assert!(!source.contains(&format!(
                    "impl ::core::convert::From<{host}> for self::{family}"
                )));
            }
        }
        assert!(source.contains("impl ::core::ops::Add<self::Rational> for self::Rational"));
        for (provider, method) in [
            ("egglog.core.bigint.from_i64", "new"),
            ("egglog.core.bigint.from_string", "from_string"),
            ("egglog.core.bigrat.make", "new"),
            ("egglog.experimental.rational.make", "new"),
        ] {
            let index = original
                .declarations
                .iter()
                .position(|d| {
                    matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == provider)
                })
                .unwrap();
            let view = &original.declarations[index]
                .bindings
                .as_ref()
                .unwrap()
                .rust
                .as_ref()
                .unwrap()
                .views[0];
            assert_eq!(view.path, [method]);
            assert_eq!(view.receiver, None);
            let mut changed = original.clone();
            changed.declarations[index]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0]
                .path = vec!["renamed_constructor".into()];
            assert!(
                generate(&changed)
                    .unwrap()
                    .0
                    .contains("pub fn renamed_constructor(")
            );
        }
        // Host numeric paths must remain qualified even when wrapper names move.
        let mut changed = original.clone();
        for declaration in &mut changed.declarations {
            if let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut declaration.kind
                && matches!(f.name.as_str(), "BigInt" | "BigRat" | "Rational")
            {
                f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3].push_str("Value");
            }
        }
        let renamed = generate(&changed).unwrap().0;
        assert!(renamed.contains("From<::num::BigInt> for self::BigIntValue"));
        assert!(renamed.contains("TryFrom<::num::BigRational> for self::BigRatValue"));
        assert!(renamed.contains("TryFrom<::num::rational::Rational64> for self::RationalValue"));
    }

    #[test]
    fn map_codec_uses_actual_nested_records_and_presentation_metadata() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let map = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Map")).expect("actual native Map catalog required");
        let of = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.map.of")).unwrap();
        let get = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.map.get")).unwrap();
        let (baseline, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert!(baseline.contains("pub struct Map<"));
        assert!(baseline.contains("pub fn from_pairs("));
        assert!(baseline.contains("pub fn entries(&self)"));
        assert!(baseline.contains("pub fn get(&self,"));
        assert!(baseline.contains("pub fn insert(&self,"));
        for reverse in [false, true] {
            let mut renamed = original.clone();
            for d in &mut renamed.declarations {
                if let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut d.kind {
                    if matches!(f.name.as_str(), "Map" | "Vec" | "Pair") {
                        f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3] =
                            format!("Renamed{}", f.name);
                    }
                }
                if let Some(bindings) = &mut d.bindings {
                    if let Some(rust) = &mut bindings.rust {
                        for view in &mut rust.views {
                            if matches!(view.path[0].as_str(), "from_pairs" | "of" | "new") {
                                view.path[0] = format!("renamed_{}", view.path[0]);
                            }
                        }
                    }
                    if let Some(egglog) = &mut bindings.egglog {
                        for view in &mut egglog.views {
                            view.symbol = format!("renamed-{}", view.symbol);
                        }
                    }
                }
            }
            if reverse {
                renamed.declarations.reverse();
            }
            let before = renamed.encode_to_vec();
            let source = generate(&renamed).unwrap().0;
            assert_eq!(renamed.encode_to_vec(), before);
            assert!(source.contains("pub struct RenamedMap<"));
            assert!(source.contains("pub fn renamed_from_pairs("));
            let packing = source
                .split_once("/// Pack tuples once")
                .unwrap()
                .1
                .split_once("/// Inspect direct entries")
                .unwrap()
                .0;
            assert!(packing.contains("self::RenamedVec<self::RenamedPair<"));
            assert!(!packing.contains("::renamed_"));
            for identity in ["egglog.core.vec.of", "egglog.core.map.of"] {
                let index = renamed.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == identity)).unwrap();
                assert!(packing.contains(&format!(".index = {index};")));
            }
        }
        let mut aliases = original.clone();
        aliases.declarations[of]
            .bindings
            .as_mut()
            .unwrap()
            .egglog
            .as_mut()
            .unwrap()
            .views[0]
            .symbol = "user-map".into();
        assert_eq!(generate(&aliases).unwrap().0, baseline);
        let mut result = original.clone();
        let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut result.declarations[get].kind
        else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
            panic!()
        };
        s.output = Some(s.inputs[1].sort);
        assert!(generate(&result).unwrap().0.contains("pub fn get(&self, __egglog_arg_0: impl ::core::convert::Into<__EgglogType0>) -> __EgglogType0"));
        for case in 0..8 {
            let mut malformed = original.clone();
            match case {
                0 => {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) =
                        &mut malformed.declarations[of].kind
                    else {
                        panic!()
                    };
                    p.name = "user.map".into();
                }
                1..=3 => {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) =
                        &mut malformed.declarations[of].kind
                    else {
                        panic!()
                    };
                    let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                        panic!()
                    };
                    if case == 1 {
                        s.inputs.push(s.inputs[0].clone());
                    } else if case == 2 {
                        s.varargs.push(s.inputs[0].clone());
                    } else {
                        let Some(pb::sort::Kind::Family(vector)) =
                            &malformed.sorts[s.inputs[0].sort as usize].kind
                        else {
                            panic!()
                        };
                        let Some(pb::sort::Kind::Family(pair)) =
                            &malformed.sorts[vector.args[0] as usize].kind
                        else {
                            panic!()
                        };
                        let mut wrong_pair = pair.clone();
                        wrong_pair.args.swap(0, 1);
                        let index = malformed.sorts.len() as u32;
                        malformed.sorts.push(pb::Sort {
                            kind: Some(pb::sort::Kind::Family(wrong_pair)),
                            ..Default::default()
                        });
                        malformed.sorts.push(pb::Sort {
                            kind: Some(pb::sort::Kind::Family(pb::HostSort {
                                name: "Vec".into(),
                                args: vec![index],
                            })),
                            ..Default::default()
                        });
                        s.inputs[0].sort = index + 1;
                    }
                }
                4..=6 => {
                    let view = &mut malformed.declarations[of]
                        .bindings
                        .as_mut()
                        .unwrap()
                        .rust
                        .as_mut()
                        .unwrap()
                        .views[0];
                    match case {
                        4 => view.path[0] = "of".into(),
                        5 => view.path[0] = "entries".into(),
                        _ => view.params[0].borrowed = true,
                    }
                }
                _ => {
                    let Some(pb::declaration::Kind::HostSortFamily(f)) =
                        &mut malformed.declarations[map].kind
                    else {
                        panic!()
                    };
                    f.arity = 1;
                }
            }
            assert!(generate(&malformed).is_err(), "Map negative control {case}");
        }
    }

    #[test]
    fn maybe_codec_follows_catalog_identity_and_checks_optional_child_scheme() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let family = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Maybe")).unwrap();
        let none = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.experimental.maybe.none")).unwrap();
        let some = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.experimental.maybe.some")).unwrap();
        let before = original.encode_to_vec();
        let baseline = generate(&original).unwrap().0;
        assert_eq!(original.encode_to_vec(), before);
        assert!(baseline.contains(
            "TryFrom<&self::Maybe<__EgglogType0>> for ::core::option::Option<__EgglogType0>"
        ));
        assert!(baseline.contains("pub fn none()"));
        assert!(baseline.contains("pub fn some("));
        assert!(baseline.contains("pub fn unwrap(&self)"));
        assert!(baseline.contains("pub fn unwrap_or(&self,"));
        let mut renamed = original.clone();
        let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut renamed.declarations[family].kind
        else {
            panic!()
        };
        f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3] = "__EgglogType0".into();
        for (index, name) in [(none, "absent"), (some, "present")] {
            let bindings = renamed.declarations[index].bindings.as_mut().unwrap();
            bindings.rust.as_mut().unwrap().views[0].path[0] = name.into();
            bindings.egglog.as_mut().unwrap().views[0].symbol = format!("alternate-{name}");
        }
        let source = generate(&renamed).unwrap().0;
        assert!(source.contains("pub struct __EgglogType0<__EgglogType0_:"));
        assert!(source.contains("pub fn absent()"));
        assert!(source.contains("pub fn present("));
        for reversed in [false, true] {
            let mut program = original.clone();
            if reversed {
                program.declarations.reverse();
            }
            let source = generate(&program).unwrap().0;
            let conversion = source
                .split_once("TryFrom<&self::Maybe<")
                .unwrap()
                .1
                .split_once("\n}\n")
                .unwrap()
                .0;
            for key in [
                "egglog.experimental.maybe.none",
                "egglog.experimental.maybe.some",
            ] {
                let index = program.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == key)).unwrap();
                assert!(conversion.contains(&format!(".index = {index};")));
            }
            assert!(!conversion.contains("::none("));
            assert!(!conversion.contains("::some("));
        }
        for case in 0..6 {
            let mut malformed = original.clone();
            let Some(pb::declaration::Kind::HostPrimitive(p)) =
                &mut malformed.declarations[some].kind
            else {
                panic!()
            };
            let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                panic!()
            };
            match case {
                0 => s.inputs.clear(),
                1 => s.inputs[0].sort = s.output.unwrap(),
                2 => s.output = Some(s.inputs[0].sort),
                3 => s.equality_type_params = vec![0],
                4 => p.name = "user.maybe.some".into(),
                _ => s.varargs = s.inputs.clone(),
            }
            assert!(
                generate(&malformed).is_err(),
                "Maybe negative control {case}"
            );
        }
    }

    #[test]
    fn pair_codec_follows_catalog_identity_paths_and_two_binders() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let make = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.pair.make")).unwrap();
        let first = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.pair.first")).unwrap();
        let pair = original.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Pair")).unwrap();
        let (baseline, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert!(baseline.contains("pub struct Pair<"));
        assert!(baseline.contains("pub fn fields(&self)"));
        let mut renamed = original.clone();
        let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut renamed.declarations[pair].kind
        else {
            panic!()
        };
        f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3] = "__EgglogType0".into();
        for (index, name) in [(make, "assemble"), (first, "left")] {
            let bindings = renamed.declarations[index].bindings.as_mut().unwrap();
            bindings.rust.as_mut().unwrap().views[0].path[0] = name.into();
            bindings.egglog.as_mut().unwrap().views[0].symbol = format!("alternate-{name}");
        }
        let before = renamed.encode_to_vec();
        let source = generate(&renamed).unwrap().0;
        assert_eq!(renamed.encode_to_vec(), before);
        assert!(source.contains("pub struct __EgglogType0<__EgglogType0_:"));
        assert!(source.contains("pub fn assemble("));
        assert!(source.contains("pub fn left(&self)"));
        assert!(!source.contains("Self::new"));
        let conversion = source
            .split_once("::core::convert::From<(__EgglogType2, __EgglogType3)>")
            .unwrap()
            .1;
        let conversion = conversion.split_once("\n}\n").unwrap().0;
        assert!(conversion.contains(&format!(".index = {make};")));
        assert!(
            !conversion.contains("assemble"),
            "tuple authoring must not call a public presentation name"
        );
        let mut aliases = original.clone();
        aliases.declarations[make]
            .bindings
            .as_mut()
            .unwrap()
            .egglog
            .as_mut()
            .unwrap()
            .views[0]
            .symbol = "not-pair".into();
        assert_eq!(generate(&aliases).unwrap().0, baseline);

        let mut output = original.clone();
        let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut output.declarations[first].kind
        else {
            panic!()
        };
        let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
            panic!()
        };
        let Some(pb::sort::Kind::Family(owner)) = &output.sorts[s.inputs[0].sort as usize].kind
        else {
            panic!()
        };
        s.output = Some(owner.args[1]);
        let output_source = generate(&output).unwrap().0;
        assert!(
            output_source.contains("pub fn first(&self) -> __EgglogType1"),
            "projection result derives from the actual record"
        );
        for permute in [false, true] {
            let mut program = original.clone();
            if permute {
                program.declarations.reverse();
            }
            let index = program.declarations.iter().position(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.pair.make")).unwrap();
            let source = generate(&program).unwrap().0;
            for start in [
                "pub fn fields(&self)",
                "fn from(__egglog_value: (__EgglogType2, __EgglogType3))",
            ] {
                let body = source
                    .split_once(start)
                    .unwrap()
                    .1
                    .split_once("\n}\n")
                    .unwrap()
                    .0;
                assert!(body.contains(&format!(".index = {index};")));
            }
        }
        for case in 0..7 {
            let mut malformed = original.clone();
            match case {
                0 => {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) =
                        &mut malformed.declarations[make].kind
                    else {
                        panic!()
                    };
                    p.name = "user.pair".into();
                }
                1 => {
                    let Some(pb::declaration::Kind::HostPrimitive(p)) =
                        &mut malformed.declarations[make].kind
                    else {
                        panic!()
                    };
                    let Some(pb::host_primitive::Typing::Signature(s)) = &mut p.typing else {
                        panic!()
                    };
                    s.inputs.swap(0, 1);
                }
                2..=4 => {
                    let view = &mut malformed.declarations[make]
                        .bindings
                        .as_mut()
                        .unwrap()
                        .rust
                        .as_mut()
                        .unwrap()
                        .views[0];
                    match case {
                        2 => {
                            view.params[1].core_input = Some(0);
                        }
                        3 => {
                            view.params.pop();
                        }
                        _ => {
                            view.path[0] = "fields".into();
                        }
                    }
                }
                5 => {
                    malformed.declarations[first]
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
                }
                _ => {
                    let Some(pb::declaration::Kind::HostSortFamily(f)) =
                        &mut malformed.declarations[pair].kind
                    else {
                        panic!()
                    };
                    f.arity = 1;
                }
            }
            assert!(
                generate(&malformed).is_err(),
                "Pair negative control {case}"
            );
        }
    }

    #[test]
    fn scalar_tail_views_derive_slots_and_trait_identity_from_actual_records() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let before = original.encode_to_vec();
        let (source, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert_eq!(original.encode_to_vec(), before);
        for name in ["String", "Bool", "Unit"] {
            assert!(source.contains(&format!("pub struct {name}(")));
        }
        for method in ["join", "replace", "implies", "to_string"] {
            assert!(source.contains(&format!("pub fn {method}(")));
        }
        for name in ["BitAnd", "BitOr", "BitXor"] {
            assert!(source.contains(&format!(
                "impl ::core::ops::{name}<self::Bool> for self::Bool"
            )));
        }
        assert!(source.contains("impl ::core::ops::Not for &self::Bool"));
        let concat = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.string.concat")
            })
            .unwrap();
        let views = &original.declarations[concat]
            .bindings
            .as_ref()
            .unwrap()
            .rust
            .as_ref()
            .unwrap()
            .views;
        assert_eq!(views[0].tail_repetitions, None);
        assert_eq!(views[1].tail_repetitions, Some(2));
        for count in [None, Some(0), Some(1), Some(3), Some(u32::MAX)] {
            let mut program = original.clone();
            program.declarations[concat]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[1]
                .tail_repetitions = count;
            assert!(
                generate(&program).is_err(),
                "invalid binary count {count:?}"
            );
        }
        // Slot zero is a fixed scalar when a count is present, even though it
        // is the logical tail slot on the unspecialized free-function view.
        for count in [0, 1] {
            let mut program = original.clone();
            let rust = program.declarations[concat]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap();
            rust.views.truncate(1);
            rust.views[0].tail_repetitions = Some(count);
            if count == 0 {
                rust.views[0].params.clear();
            }
            let bytes = program.encode_to_vec();
            let specialized = generate(&program).unwrap().0;
            assert_eq!(program.encode_to_vec(), bytes);
            let decoded = pb::Program::decode(bytes.as_slice()).unwrap();
            assert_eq!(
                decoded.declarations[concat]
                    .bindings
                    .as_ref()
                    .unwrap()
                    .rust
                    .as_ref()
                    .unwrap()
                    .views[0]
                    .tail_repetitions,
                Some(count)
            );
            let join = specialized
                .split_once("pub fn join(")
                .unwrap()
                .1
                .split_once(" -> ")
                .unwrap()
                .0;
            assert!(!join.contains("IntoIterator"));
            if count == 0 {
                assert_eq!(join, ")");
            } else {
                assert!(join.contains("Into<self::String>"));
            }
        }
        let mut swapped = original.clone();
        let view = &mut swapped.declarations[concat]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[1];
        view.receiver.as_mut().unwrap().core_input = Some(1);
        view.params[0].core_input = Some(0);
        assert!(generate(&swapped).unwrap().0.contains("::std::vec![::core::clone::Clone::clone(&__egglog_rhs.0), ::core::clone::Clone::clone(&self.0)]"));
        for slot in [0, 2] {
            let mut program = original.clone();
            program.declarations[concat]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[1]
                .params[0]
                .core_input = Some(slot);
            assert!(generate(&program).is_err());
        }
        let boolean_or = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
                Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.bool.or")
            })
            .unwrap();
        let mut consuming = original.clone();
        let view = &mut consuming.declarations[boolean_or]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0];
        view.tail_repetitions = None;
        view.trait_impl = None;
        view.path = vec!["or_all".into()];
        view.receiver.as_mut().unwrap().borrowed = true;
        let bytes = consuming.encode_to_vec();
        let source = generate(&consuming).unwrap().0;
        assert_eq!(consuming.encode_to_vec(), bytes);
        assert!(source.contains("pub fn or_all(&self, __egglog_arg_0: impl ::core::iter::IntoIterator<Item = impl ::core::convert::Into<self::Bool>>"));
        assert!(source.contains(
            "let mut __egglog_args = ::std::vec![::core::clone::Clone::clone(&self.0)];"
        ));
        for slot in [0, 2] {
            let mut malformed = consuming.clone();
            malformed.declarations[boolean_or]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0]
                .params[0]
                .core_input = Some(slot);
            assert!(generate(&malformed).is_err());
        }
        let mut open_trait = original.clone();
        open_trait.declarations[boolean_or]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0]
            .tail_repetitions = None;
        assert!(
            generate(&open_trait)
                .unwrap_err()
                .contains("unsupported scalar Rust view")
        );

        let mut duplicated = original.clone();
        let rust = duplicated
            .declarations
            .iter_mut()
            .find_map(|d| match &d.kind {
                Some(pb::declaration::Kind::HostPrimitive(p))
                    if p.name == "egglog.core.bool.or" =>
                {
                    d.bindings.as_mut().unwrap().rust.as_mut()
                }
                _ => None,
            })
            .unwrap();
        rust.views.push(rust.views[0].clone());
        assert!(
            generate(&duplicated)
                .unwrap_err()
                .contains("implementation collision")
        );
        let fixed = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.i64.add")
            })
            .unwrap();
        let mut program = original.clone();
        program.declarations[fixed]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0]
            .tail_repetitions = Some(0);
        assert!(
            generate(&program)
                .unwrap_err()
                .contains("requires a canonical tail")
        );
    }

    #[test]
    fn optional_documentation_renders_without_rewriting_records() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
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
            .portable_builtin_catalog()
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
                if name == "egglog.core.vec.of" {
                    assert_eq!(
                        generate(&program).unwrap_err(),
                        "catalog Map constructor does not match the Vec-of-Pair codec"
                    );
                    // Isolate the Vec presentation control from its selected
                    // Map codec consumer without removing canonical records.
                    for declaration in &mut program.declarations {
                        match &mut declaration.kind {
                            Some(pb::declaration::Kind::HostSortFamily(family))
                                if family.name == "Map" =>
                            {
                                family.bindings.as_mut().unwrap().rust = None;
                            }
                            Some(pb::declaration::Kind::HostPrimitive(primitive))
                                if primitive.name.starts_with("egglog.core.map.")
                                    || matches!(
                                        primitive.name.as_str(),
                                        "egglog.experimental.map.fold_kv"
                                            | "egglog.experimental.subst"
                                    ) =>
                            {
                                declaration.bindings.as_mut().unwrap().rust = None;
                            }
                            _ => {}
                        }
                    }
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
            .portable_builtin_catalog()
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
                        for param in &mut view.params {
                            param.name = parameter.into();
                        }
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
    fn i64_i32_inputs_follow_catalog_binding() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        for name in ["I64", "RenamedI64"] {
            let mut program = original.clone();
            let family = program
                .declarations
                .iter_mut()
                .find_map(|declaration| match &mut declaration.kind {
                    Some(pb::declaration::Kind::HostSortFamily(family)) if family.name == "i64" => {
                        Some(family)
                    }
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
                .path[3] = name.into();
            let (source, _) = generate(&program).unwrap();
            for input in ["::core::primitive::i32", "&::core::primitive::i32"] {
                assert!(source.contains(&format!(
                    "impl ::core::convert::From<{input}> for self::{name}"
                )));
                assert!(!source.contains(&format!(
                    "impl ::core::convert::From<{input}> for self::F64"
                )));
            }
            assert!(source.contains("::core::primitive::i64::from(__egglog_value)"));
            assert!(source.contains("::core::primitive::i64::from(*__egglog_value)"));
            assert_eq!(source.matches("From<::core::primitive::i32>").count(), 1);
            assert_eq!(source.matches("From<&::core::primitive::i32>").count(), 1);
            assert!(source.contains(&format!(
                "impl ::core::convert::From<::core::primitive::i64> for self::{name}"
            )));
        }
    }

    #[test]
    fn operand_metadata_names_never_become_rust_binding_patterns() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
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
                        for param in &mut view.params {
                            param.name = parameter.into();
                        }
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
                program
                    .declarations
                    .iter()
                    .filter_map(|d| d.bindings.as_ref()?.rust.as_ref())
                    .flat_map(|rust| &rust.views)
                    .filter(|view| view.path == ["add"])
                    .count()
                    * 4
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
            if !f.args.is_empty()
                || !matches!(f.name.as_str(), "i64" | "f64" | "String" | "bool" | "Unit")
            {
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
            let Some(rust) = d.bindings.as_ref().and_then(|b| b.rust.as_ref()) else {
                continue;
            };
            for view in rust.views.iter().filter(|view| view.trait_impl.is_some()) {
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
                        Some(pb::declaration::Kind::HostSortFamily(h)) if h.name == f.name => {
                            Some(h)
                        }
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
                    let trait_impl = view.trait_impl.as_ref().unwrap();
                    let trait_path = trait_impl.path.join("::");
                    for rhs in if trait_impl.args.is_empty() {
                        &[""][..]
                    } else {
                        &["", "&"][..]
                    } {
                        let args = if trait_impl.args.is_empty() {
                            String::new()
                        } else {
                            let ty =
                                rust_type(program, trait_impl.args[0].sort.unwrap(), &[]).unwrap();
                            format!("<{rhs}{ty}>")
                        };
                        let marker = format!("impl ::{trait_path}{args} for {lhs}self::{name} {{");
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
    }

    #[test]
    fn closed_i64_operator_views_preserve_slots_and_all_ownership_forms() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        for (key, method) in [
            ("Sub", "sub"),
            ("Mul", "mul"),
            ("Div", "div"),
            ("Rem", "rem"),
        ] {
            let mut program = original.clone();
            let index = program.declarations.iter().position(|d| matches!(
                &d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == format!("egglog.core.i64.{method}")
            )).unwrap();
            let (source, _) = generate(&program).unwrap();
            assert_locations(&program, &source);
            for left in ["", "&"] {
                for right in ["", "&"] {
                    let marker =
                        format!("impl ::core::ops::{key}<{right}self::I64> for {left}self::I64 {{");
                    let body = source
                        .split_once(&marker)
                        .unwrap()
                        .1
                        .split_once("\n}")
                        .unwrap()
                        .0;
                    assert!(body.contains(&format!("fn {method}(self,")));
                    assert!(body.contains("::std::vec![::core::clone::Clone::clone(&self.0), ::core::clone::Clone::clone(&__egglog_rhs.0)]"));
                }
            }
            let declaration = &mut program.declarations[index];
            let Some(pb::declaration::Kind::HostPrimitive(p)) = &mut declaration.kind else {
                unreachable!()
            };
            p.name = format!("test.renamed.{method}");
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
            program.declarations.reverse();
            let (source, _) = generate(&program).unwrap();
            assert_locations(&program, &source);
            for left in ["", "&"] {
                for right in ["", "&"] {
                    let marker =
                        format!("impl ::core::ops::{key}<{right}self::I64> for {left}self::I64 {{");
                    let body = source
                        .split_once(&marker)
                        .unwrap()
                        .1
                        .split_once("\n}")
                        .unwrap()
                        .0;
                    assert!(body.contains("::std::vec![::core::clone::Clone::clone(&__egglog_rhs.0), ::core::clone::Clone::clone(&self.0)]"));
                }
            }
            let index = program.declarations.len() - index - 1;
            program.declarations[index]
                .bindings
                .as_mut()
                .unwrap()
                .rust
                .as_mut()
                .unwrap()
                .views[0]
                .params[0]
                .core_input = Some(1);
            assert!(generate(&program).is_err(), "duplicate slots for {key}");
        }
    }

    #[test]
    fn native_records_determine_paths_locations_and_argument_order() {
        let mut p = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let (source, deferred) = generate(&p).unwrap();
        assert!(source.contains("pub struct I64"));
        assert!(source.contains("pub struct F64"));
        assert_eq!(deferred, DEFERRED);
        // I64, F64, String, Rational, BigInt and BigRat each expose four ownership forms.
        assert_eq!(source.matches("fn add(self,").count(), 24);
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
            } else if let Some(pb::sort::Kind::Func(f)) = &mut sort.kind {
                for arg in &mut f.params {
                    *arg = last - *arg;
                }
                f.result = last - f.result;
            }
        }
        for d in &mut p.declarations {
            if let Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
                typing: Some(pb::host_primitive::Typing::Signature(s)),
                ..
            })) = &mut d.kind
            {
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
                    if let Some(pb::binding_owner::Kind::Sort(s)) = &mut owner.kind {
                        *s = last - *s;
                    }
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
            .portable_builtin_catalog()
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
    fn native_set_catalog_drives_every_method_and_rejects_invalid_views() {
        let original = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
            .unwrap()
            .definitions;
        let before = original.encode_to_vec();
        let family = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostSortFamily(f)) if f.name == "Set")
            })
            .expect("actual native Set catalog required");
        let set_methods: Vec<_> = original
            .declarations
            .iter()
            .filter_map(|d| match &d.kind {
                Some(pb::declaration::Kind::HostPrimitive(p)) => {
                    p.name.strip_prefix("egglog.core.set.")
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            set_methods,
            [
                "contains",
                "diff",
                "empty",
                "get",
                "insert",
                "intersect",
                "length",
                "not_contains",
                "of",
                "remove",
                "union"
            ]
        );
        let (source, deferred) = generate(&original).unwrap();
        assert_eq!(deferred, DEFERRED);
        assert!(source.contains("pub struct Set<"));
        assert!(source.contains(
            ".sequence_elements(&<__EgglogType0 as crate::typed::EgglogValue>::sort_ref(), \"Set\")"
        ));
        assert_locations(&original, &source);
        assert_eq!(original.encode_to_vec(), before);

        let get = original
            .declarations
            .iter()
            .position(|d| {
                matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.set.get")
            })
            .unwrap();
        let mut renamed = original.clone();
        let Some(pb::declaration::Kind::HostSortFamily(f)) = &mut renamed.declarations[family].kind
        else {
            panic!()
        };
        f.bindings.as_mut().unwrap().rust.as_mut().unwrap().path[3] = "RenamedSet".into();
        renamed.declarations[get]
            .bindings
            .as_mut()
            .unwrap()
            .rust
            .as_mut()
            .unwrap()
            .views[0]
            .path[0] = "pick".into();
        renamed.declarations.reverse();
        let renamed_before = renamed.encode_to_vec();
        let (source, _) = generate(&renamed).unwrap();
        assert!(source.contains("pub struct RenamedSet<"));
        assert!(source.contains("pub fn pick("));
        assert_locations(&renamed, &source);
        let parameters = generic_parameters(&renamed, 1);
        let marker = format!(
            "impl<{}: crate::typed::EgglogValue> self::RenamedSet<{}> {{",
            parameters[0], parameters[0]
        );
        for (index, declaration) in renamed.declarations.iter().enumerate() {
            let Some(pb::declaration::Kind::HostPrimitive(p)) = &declaration.kind else {
                continue;
            };
            if !p.name.starts_with("egglog.core.set.") {
                continue;
            }
            let Some(pb::host_primitive::Typing::Signature(signature)) = &p.typing else {
                panic!()
            };
            for view in &declaration
                .bindings
                .as_ref()
                .unwrap()
                .rust
                .as_ref()
                .unwrap()
                .views
            {
                let method = format!("pub fn {}(", view.path[0]);
                let body = source
                    .split(&marker)
                    .skip(1)
                    .map(|part| part.split_once("\n}\n").unwrap().0)
                    .find(|body| body.contains(&method))
                    .unwrap();
                assert!(body.contains(&format!(".index = {index};")));
                assert!(body.contains(&format!(
                    "-> {}",
                    rust_type(&renamed, signature.output.unwrap(), &parameters).unwrap()
                )));
            }
        }
        assert_eq!(renamed.encode_to_vec(), renamed_before);

        for case in 0..9 {
            let mut malformed = original.clone();
            if case == 0 {
                let Some(pb::declaration::Kind::HostSortFamily(f)) =
                    &mut malformed.declarations[family].kind
                else {
                    panic!()
                };
                f.arity = 2;
            } else {
                let rust = malformed.declarations[get]
                    .bindings
                    .as_mut()
                    .unwrap()
                    .rust
                    .as_mut()
                    .unwrap();
                let view = &mut rust.views[0];
                match case {
                    1 => view.receiver.as_mut().unwrap().core_input = Some(1),
                    2 => view.params[0].core_input = Some(0),
                    3 => view.params[0].borrowed = true,
                    4 => view.borrowed_self = true,
                    5 => view.tail_repetitions = Some(1),
                    6 => view.owner = None,
                    7 => view.trait_impl = Some(Default::default()),
                    8 => rust.views.push(rust.views[0].clone()),
                    _ => unreachable!(),
                }
            }
            assert!(generate(&malformed).is_err(), "Set view negative {case}");
        }
    }

    #[test]
    fn native_vec_views_drive_generic_members_and_relocated_declarations() {
        let mut program = egglog_experimental::new_experimental_egraph()
            .type_info()
            .portable_builtin_catalog()
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
        assert_eq!(program.declarations.iter().filter(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.vec.range"
        )).count(), 1);
        for permute in [false, true] {
            if permute {
                program.declarations.reverse();
            }
            let (source, deferred) = generate(&program).unwrap();
            let mut expected = DEFERRED;
            if permute {
                expected.reverse();
            }
            assert_eq!(deferred, expected);
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
                if p.name == "egglog.core.vec.range" {
                    assert!(s.type_params.is_empty() && s.varargs.is_empty());
                    assert_eq!(s.inputs.len(), 1);
                    assert_eq!(
                        rust_type(&program, s.inputs[0].sort, &[]).unwrap(),
                        "self::I64"
                    );
                    assert_eq!(
                        rust_type(&program, s.output.unwrap(), &[]).unwrap(),
                        "self::Vec<self::I64>"
                    );
                    let body = source
                        .split_once("pub fn range(&self)")
                        .unwrap()
                        .1
                        .split_once("\n}\n")
                        .unwrap()
                        .0;
                    assert!(body.starts_with(" -> self::Vec<self::I64>"));
                    assert!(body.contains(&format!(".index = {index};")));
                    assert!(body.contains(
                        "<self::Vec<self::I64> as crate::typed::EgglogValue>::sort_ref()"
                    ));
                }
                if s.type_params.is_empty() {
                    continue;
                }
                let Some(rust) = d.bindings.as_ref().and_then(|b| b.rust.as_ref()) else {
                    continue;
                };
                let parameters = generic_parameters(&program, s.type_params.len());
                let generics = parameters
                    .iter()
                    .enumerate()
                    .map(|(index, t)| {
                        format!(
                            "{t}: crate::typed::{}",
                            if s.equality_type_params.contains(&(index as u32)) {
                                "EqualitySort"
                            } else {
                                "EgglogValue"
                            }
                        )
                    })
                    .collect::<Vec<_>>();
                let views = &rust.views;
                for view in views.iter().filter(|view| view.owner.is_some()) {
                    let Some(pb::binding_owner::Kind::Sort(owner)) =
                        view.owner.as_ref().unwrap().kind
                    else {
                        panic!()
                    };
                    let Some(pb::sort::Kind::Family(family)) = &program.sorts[owner as usize].kind
                    else {
                        panic!()
                    };
                    let owner_arity = family.args.len();
                    let owner = rust_type(&program, owner, &parameters).unwrap();
                    let start = format!("impl<{}> {owner} {{", generics[..owner_arity].join(", "));
                    let method = format!(
                        "pub fn {}{}",
                        view.path[0],
                        if owner_arity == generics.len() {
                            "("
                        } else {
                            "<"
                        }
                    );
                    let body = source
                        .split(&start)
                        .skip(1)
                        .map(|part| part.split_once("\n}\n").unwrap().0)
                        .find(|part| part.contains(&method))
                        .unwrap();
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
        let header = source
            .split("pub fn get(")
            .skip(1)
            .map(|part| part.split_once("\n}\n").unwrap().0)
            .find(|body| body.contains(&format!(".index = {get};")))
            .unwrap();
        let header = header.split_once(" {").unwrap().0;
        assert!(header.contains(&format!(
            "-> {}",
            rust_type(&changed_output, integer, &generic_parameters(&changed_output, 1)).unwrap()
        )));
        let range = original.declarations.iter().position(|d| matches!(&d.kind,
            Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == "egglog.core.vec.range"
        )).unwrap();
        let root = original.sorts.len() as u32;
        for (kind, error) in [
            (None, "missing Rust sort pattern"),
            (Some(pb::sort::Kind::Var(0)), "unbound Rust type parameter"),
            (
                Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Vec".into(),
                    args: vec![root],
                })),
                "cyclic Rust sort pattern",
            ),
            (
                Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Vec".into(),
                    args: vec![],
                })),
                "unsupported Rust family binding",
            ),
            (
                Some(pb::sort::Kind::Family(pb::HostSort {
                    name: "Unknown".into(),
                    args: vec![],
                })),
                "Rust sort has no supported value codec",
            ),
            (
                Some(pb::sort::Kind::Eq("Nominal".into())),
                "unsupported generated Rust sort pattern",
            ),
        ] {
            let mut malformed = original.clone();
            if kind.is_some() {
                malformed.sorts.push(pb::Sort {
                    kind,
                    ..Default::default()
                });
            }
            let Some(pb::declaration::Kind::HostPrimitive(p)) =
                &mut malformed.declarations[range].kind
            else {
                panic!()
            };
            let Some(pb::host_primitive::Typing::Signature(signature)) = &mut p.typing else {
                panic!()
            };
            signature.output = Some(root);
            assert_eq!(generate(&malformed).unwrap_err(), error);
        }
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
