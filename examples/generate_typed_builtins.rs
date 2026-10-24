//! Generate the Rust scalar and container surfaces from the actual native catalog.
//! Run without `--features typed` to bootstrap the generated source/resource;
//! use `--check` to detect either API or catalog drift. Nothing runs at import.
use egglog_experimental::PortableTypeInfo;
use egglog_experimental::proto as pb;
use prost::Message;
#[path = "../src/typed/builtins/presentation.rs"]
mod presentation;
use presentation::RustPresentation;
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
    let presentation = RustPresentation::builtin().map_err(std::io::Error::other)?;
    let (source, deferred, definitions) =
        generate(&catalog.definitions, &presentation).map_err(std::io::Error::other)?;
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
        ("catalog.pb", definitions.encode_to_vec()),
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
        catalog.definitions.primitives.len() + catalog.definitions.primitive_sorts.len()
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

fn generate(
    program: &pb::BuiltinCatalog,
    presentation: &RustPresentation,
) -> Result<(String, Vec<String>, pb::BuiltinCatalog), String> {
    let native_catalog = program;
    let native_sort_count = program.sorts.len();
    let (joined, presentation) = presentation.join(program)?;
    let program = &joined;
    let presentation = &presentation;
    let mut source = String::from(
        "// @generated by examples/generate_typed_builtins.rs. Do not edit.\n// The adjacent catalog.pb owns every semantic field; indices are locations only.\n",
    );
    let mut deferred = vec![];
    let mut types = BTreeMap::new(); // Derived presentation names, not signatures.
    let mut public_names = HashSet::new();
    let type_names: HashSet<&str> = presentation
        .families
        .values()
        .filter_map(|view| view.path.last().map(String::as_str))
        .collect();
    let occupied: HashSet<&str> = type_names
        .iter()
        .copied()
        .chain(
            presentation
                .callables
                .values()
                .flatten()
                .flat_map(|view| &view.params)
                .map(|p| p.name.as_str()),
        )
        .collect();
    let value_local = local_name("value", &occupied);
    let record_local = local_name("record", &occupied);
    let node_local = local_name("node", &occupied);
    let error_local = local_name("error", &occupied);
    let mut identities = HashSet::new();
    for (declaration_index, family) in program.primitive_sorts.iter().enumerate() {
        if family.name.is_empty() || !identities.insert((false, &family.name)) {
            return Err(format!("empty or duplicate catalog name {:?}", family.name));
        }
        let Some(binding) = presentation.families.get(&family.name) else {
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
            emit_container_type(
                program,
                presentation,
                declaration_index,
                &mut source,
                &occupied,
            )?;
            continue;
        }
        // These are schema-defined value codecs, not a primitive signature or
        // a family-to-wrapper-name table. The Rust name comes from the local presentation map.
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
        let concrete = program.sorts.iter().take(native_sort_count).position(|s| {
            matches!(&s.kind,
            Some(pb::sort::Kind::Application(f)) if f.name == family.name && f.args.is_empty())
        });
        for (i, sort) in program.sorts.iter().enumerate() {
            if matches!(&sort.kind, Some(pb::sort::Kind::Application(f)) if f.name == family.name && f.args.is_empty())
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
                "PrimitiveSort",
                declaration_index,
                format!(
                    "crate::typed::SortRef::family(&{record_local}, ::std::vec![]).expect(\"generated scalar family arity\")"
                ),
            )
        };
        let mut doc = format!(
            "A protobuf-owned symbolic {} value. Structural equality preserves exact literal payloads.\n\n{}",
            family.name,
            family.doc.as_deref().unwrap_or_default()
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
        let {node_local} = &{record_local}.owner.as_ref().unwrap().program().expect("owned literal Program").nodes[{record_local}.index as ::core::primitive::usize];
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
    for (index, primitive) in program.primitives.iter().enumerate() {
        if primitive.name.is_empty() || !identities.insert((true, &primitive.name)) {
            return Err(format!(
                "empty or duplicate catalog name {:?}",
                primitive.name
            ));
        }
        let Some(rust) = presentation.callables.get(&primitive.name) else {
            deferred.push(primitive.name.clone());
            continue;
        };
        let signature = primitive
            .signature
            .as_ref()
            .ok_or_else(|| format!("missing selected Rust signature: {}", primitive.name))?;
        if signature.varargs.len() > 1 {
            return Err(format!(
                "unsupported selected Rust tail width {} for {}",
                signature.varargs.len(),
                primitive.name
            ));
        }
        if signature.type_param_count != 0 {
            emit_generic_views(
                program,
                presentation,
                index,
                &mut source,
                &mut implementations,
                &mut public_names,
                &occupied,
            )?;
            continue;
        }
        let output = rust_type(
            program,
            presentation,
            signature.output.ok_or("missing output")?,
            &[],
        )?;
        if rust.is_empty() {
            return Err(format!("empty Rust presentation for {}", primitive.name));
        }
        for view in rust {
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
                let owner = view
                    .owner_sort
                    .as_ref()
                    .map(|sort| types.get(&sort.root).ok_or("unsupported Rust member owner"))
                    .transpose()?;
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
        {record_local}.arena = crate::typed::storage::Arena::Primitive;
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
            let Some(owner) = view.owner_sort.as_ref() else {
                return Err("scalar operator needs a sort owner".into());
            };
            let owner = types
                .get(&owner.root)
                .ok_or("unsupported Rust owner sort")?;
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
        {record_local}.arena = crate::typed::storage::Arena::Primitive;
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
                        .as_ref()
                        .ok_or("missing trait argument sort")?
                        .root,
                ) != types.get(&inputs[rhs_index].sort)
            {
                return Err(
                    "Rust receiver/parameter/trait mapping disagrees with signature".into(),
                );
            }
            let rhs_type = types
                .get(&inputs[rhs_index].sort)
                .ok_or("unsupported RHS sort")?;
            // Presentation names remain in the local map, not binding
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
        {record_local}.arena = crate::typed::storage::Arena::Primitive;
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
    Ok((source, deferred, native_catalog.clone()))
}

// Translate the actual sort arena into Rust types. This derives presentation
// only: no family/callable signatures are restated in an emitter registry.
fn rust_type(
    program: &pb::BuiltinCatalog,
    presentation: &RustPresentation,
    root: u32,
    parameters: &[String],
) -> Result<String, String> {
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
            if let pb::sort::Kind::Application(f) = kind {
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
            pb::sort::Kind::Application(f) => {
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
                    .primitive_sorts
                    .iter()
                    .find(|p| p.name == f.name)
                    .ok_or("missing Rust family definition")?;
                let binding = presentation
                    .families
                    .get(&definition.name)
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
// parameter positions determine the Rust mapping.
fn generic_parameters(presentation: &RustPresentation, count: usize) -> Vec<String> {
    let mut occupied: HashSet<String> = presentation
        .families
        .values()
        .filter_map(|view| view.path.last().cloned())
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
    program: &pb::BuiltinCatalog,
    presentation: &RustPresentation,
    index: usize,
    source: &mut String,
    occupied: &HashSet<&str>,
) -> Result<(), String> {
    let family = &program.primitive_sorts[index];
    let binding = presentation
        .families
        .get(&family.name)
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
    let parameters = generic_parameters(presentation, arity);
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
        {record}.arena = crate::typed::storage::Arena::PrimitiveSort;
        {record}.index = {index};
        crate::typed::SortRef::family(&{record}, ::std::vec![{sorts}]).expect("generated family arity")
    }}
    fn expression(&self) -> &crate::typed::expr::Expr {{ &self.0 }}
    fn from_expression({value}: crate::typed::expr::Expr) -> Self {{ Self({value}, ::core::marker::PhantomData) }}
}}
"#).unwrap();
    if family.name == "Map" {
        emit_map_codec(program, presentation, name, &parameters, source, occupied)?;
    } else if family.name == "Maybe" {
        let mut constructors = vec![];
        let owner = format!("self::{name}<{types}>");
        for (key, arity) in [("none", 0), ("some", 1)] {
            let identity = format!("egglog.experimental.maybe.{key}");
            let (index, signature) = program
                .primitives
                .iter()
                .enumerate()
                .find_map(|(i, p)| {
                    if p.name != identity {
                        return None;
                    }
                    let Some(s) = &p.signature else {
                        return None;
                    };
                    Some((i, s))
                })
                .ok_or("missing catalog Maybe constructor")?;
            if signature.type_param_count as usize != 1
                || signature.inputs.len() != arity
                || !signature.varargs.is_empty()
                || rust_type(
                    program,
                    presentation,
                    signature.output.ok_or("missing Maybe result")?,
                    &parameters,
                )? != owner
                || signature.inputs.iter().any(|a| {
                    rust_type(program, presentation, a.sort, &parameters).as_ref()
                        != Ok(&parameters[0])
                })
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
        {none}.arena = crate::typed::storage::Arena::Primitive;
        {none}.index = {none_index};
        let mut {some} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {some}.arena = crate::typed::storage::Arena::Primitive;
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
            .primitives
            .iter()
            .enumerate()
            .find_map(|(index, p)| {
                if p.name != "egglog.core.pair.make" {
                    return None;
                }
                let Some(s) = &p.signature else {
                    return None;
                };
                Some((index, s))
            })
            .ok_or("missing catalog Pair constructor")?;
        let owner = format!("self::{name}<{types}>");
        if signature.type_param_count as usize != arity
            || signature.inputs.len() != arity
            || !signature.varargs.is_empty()
            || rust_type(
                program,
                presentation,
                signature.output.ok_or("missing Pair output")?,
                &parameters,
            )? != owner
            || signature.inputs.iter().zip(&parameters).any(|(arg, ty)| {
                rust_type(program, presentation, arg.sort, &parameters).as_ref() != Ok(ty)
            })
        {
            return Err("catalog Pair constructor does not match the two-child codec".into());
        }
        let left = local_name("left", occupied);
        let right = local_name("right", occupied);
        let l = &parameters[0];
        let r = &parameters[1];
        let input_parameters = generic_parameters(presentation, 4);
        let a = &input_parameters[2];
        let b = &input_parameters[3];
        writeln!(source, r#"
impl<{generics}> {owner} {{
    /// Inspect direct ordered fields without evaluating symbolic children.
    pub fn fields(&self) -> ::core::result::Result<({types}), crate::typed::TypedError> {{
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Primitive;
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
        {record}.arena = crate::typed::storage::Arena::Primitive;
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
    program: &pb::BuiltinCatalog,
    presentation: &RustPresentation,
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
            .primitives
            .iter()
            .enumerate()
            .find_map(|(i, p)| {
                let Some(s) = &p.signature else {
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
        presentation,
        pair_make.output.ok_or("missing Pair output")?,
        parameters,
    )?;
    let Some(pb::sort::Kind::Application(pair_family)) = program
        .sorts
        .get(pair_make.output.unwrap() as usize)
        .and_then(|s| s.kind.as_ref())
    else {
        return Err("Map codec requires a Pair family result".into());
    };
    if pair_family.name != "Pair"
        || pair_family.args.len() != 2
        || pair_make.type_param_count as usize != 2
        || pair_make.inputs.len() != 2
        || !pair_make.varargs.is_empty()
        || pair_make.inputs.iter().zip(parameters).any(|(arg, ty)| {
            rust_type(program, presentation, arg.sort, parameters).as_ref() != Ok(ty)
        })
        || pair_family
            .args
            .iter()
            .zip(parameters)
            .any(|(arg, ty)| rust_type(program, presentation, *arg, parameters).as_ref() != Ok(ty))
    {
        return Err("catalog Pair constructor does not match Map's tuple codec".into());
    }
    let vec_type = rust_type(
        program,
        presentation,
        vec_of.output.ok_or("missing Vec output")?,
        std::slice::from_ref(&pair_type),
    )?;
    let Some(pb::sort::Kind::Application(vec_family)) = program
        .sorts
        .get(vec_of.output.unwrap() as usize)
        .and_then(|s| s.kind.as_ref())
    else {
        return Err("Map codec requires a Vec family result".into());
    };
    if vec_family.name != "Vec"
        || vec_family.args.len() != 1
        || vec_of.type_param_count as usize != 1
        || !vec_of.inputs.is_empty()
        || vec_of.varargs.len() != 1
        || rust_type(
            program,
            presentation,
            vec_family.args[0],
            std::slice::from_ref(&pair_type),
        )? != pair_type
        || rust_type(
            program,
            presentation,
            vec_of.varargs[0].sort,
            std::slice::from_ref(&pair_type),
        )? != pair_type
        || vec_empty.type_param_count as usize != 1
        || !vec_empty.inputs.is_empty()
        || !vec_empty.varargs.is_empty()
        || rust_type(
            program,
            presentation,
            vec_empty.output.ok_or("missing Vec empty output")?,
            std::slice::from_ref(&pair_type),
        )? != vec_type
        || empty.type_param_count as usize != 2
        || !empty.inputs.is_empty()
        || !empty.varargs.is_empty()
        || rust_type(
            program,
            presentation,
            empty.output.ok_or("missing Map empty output")?,
            parameters,
        )? != owner
        || of.type_param_count as usize != 2
        || of.inputs.len() != 1
        || !of.varargs.is_empty()
        || rust_type(
            program,
            presentation,
            of.output.ok_or("missing Map output")?,
            parameters,
        )? != owner
        || rust_type(program, presentation, of.inputs[0].sort, parameters)? != vec_type
    {
        return Err("catalog Map constructor does not match the Vec-of-Pair codec".into());
    }
    let generics = parameters
        .iter()
        .map(|t| format!("{t}: crate::typed::EgglogValue"))
        .collect::<Vec<_>>()
        .join(", ");
    let inputs = generic_parameters(presentation, 5);
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
        {record}.arena = crate::typed::storage::Arena::Primitive;
        {record}.index = {vec_of_index};
        let {value} = crate::typed::expr::Expr::call_with_result(&crate::typed::decl::Callable({record}), {items}, <{vec_type} as crate::typed::EgglogValue>::sort_ref()).expect("generated Map Vec packing disagrees with its descriptor");
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Primitive;
        {record}.index = {of_index};
        <Self as crate::typed::EgglogValue>::from_expression(crate::typed::expr::Expr::call_with_result(&crate::typed::decl::Callable({record}), ::std::vec![{value}], <Self as crate::typed::EgglogValue>::sort_ref()).expect("generated Map packing disagrees with its descriptor"))
    }}
    /// Inspect direct entries without evaluating computations or normalizing keys.
    pub fn entries(&self) -> ::core::result::Result<::std::vec::Vec<({types})>, crate::typed::TypedError> {{
        let {callables} = [{indices}].map(|{index}| {{
            let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
            {record}.arena = crate::typed::storage::Arena::Primitive;
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
    program: &pb::BuiltinCatalog,
    presentation: &RustPresentation,
    index: usize,
    source: &mut String,
    implementations: &mut HashSet<(String, String, Vec<String>)>,
    public_names: &mut HashSet<String>,
    occupied: &HashSet<&str>,
) -> Result<(), String> {
    let primitive = &program.primitives[index];
    let Some(signature) = &primitive.signature else {
        return Err("unsupported generic typing".into());
    };
    let rust = presentation
        .callables
        .get(&primitive.name)
        .ok_or("missing generic Rust views")?;
    if rust.is_empty() {
        return Err("empty generic Rust views".into());
    }
    // Check actual referenced data before allocating generated identifiers. A
    // malformed count must not require memory proportional to its scalar value.
    let mut pending = signature
        .inputs
        .iter()
        .chain(&signature.varargs)
        .map(|arg| arg.sort)
        .chain(signature.output)
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    let mut referenced = HashSet::new();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        match program
            .sorts
            .get(index as usize)
            .and_then(|sort| sort.kind.as_ref())
            .ok_or("invalid generic sort reference")?
        {
            pb::sort::Kind::Var(index) if *index < signature.type_param_count => {
                referenced.insert(*index);
            }
            pb::sort::Kind::Var(_) => return Err("unbound generic parameter".into()),
            pb::sort::Kind::Application(family) => pending.extend(&family.args),
            pb::sort::Kind::Func(function) => {
                pending.extend(&function.params);
                pending.push(function.result);
            }
            _ => (),
        }
    }
    if referenced.len() != signature.type_param_count as usize {
        return Err("undetermined generic parameter".into());
    }
    let parameters = generic_parameters(presentation, referenced.len());
    let value = local_name("value", occupied);
    let record = local_name("record", occupied);
    let args = local_name("args", occupied);
    for view in rust {
        if view.tail_repetitions.is_some() {
            return Err("specialized generic Rust views are not supported yet".into());
        }
        let mut anchors = vec![None; parameters.len()];
        let mut concrete_inputs = false;
        let mut owner_parameter_count = 0;
        let (owner, method, types, bound) = if view.owner_sort.is_none() {
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
                        Some(pb::sort::Kind::Application(f)) => pending.extend(&f.args),
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
            let Some(owner) = view.owner_sort.as_ref() else {
                return Err("generic Rust view requires a family owner".into());
            };
            let Some(pb::sort::Kind::Application(family)) = program
                .sorts
                .get(owner.root as usize)
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
            let owner = rust_type(program, presentation, owner.root, &parameters)?;
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
            .map(|t| format!("{t}: {bound}"))
            .collect::<Vec<_>>();
        let output = rust_type(
            program,
            presentation,
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
            if Some(rust_type(program, presentation, input.sort, &types)?) != owner {
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
                    presentation,
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
                    presentation,
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
    pub fn {method}{method_generics}({params}) -> {output} {{
        let {mutability}{args} = ::std::vec![{inputs}];
        {tail_code}
        let mut {record} = ::core::clone::Clone::clone(crate::typed::storage::builtin_catalog());
        {record}.arena = crate::typed::storage::Arena::Primitive;
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
#[path = "../src/typed/builtins/presentation_tests.rs"]
mod tests;
