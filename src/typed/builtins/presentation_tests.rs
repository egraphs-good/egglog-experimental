use super::*;
use presentation::{Parameter, SortRef, TraitView};
use std::sync::Arc;

#[test]
fn local_mapping_rejects_orphan_primitive_sort_and_callable_keys() {
    let (catalog, mapping) = native_fixture();
    let mut orphan = mapping.clone();
    orphan
        .families
        .insert("orphan.sort".into(), mapping.families["i64"].clone());
    assert!(
        orphan
            .join(&catalog)
            .unwrap_err()
            .contains("orphan Rust family mapping: orphan.sort")
    );
    let mut orphan = mapping.clone();
    orphan.callables.insert(
        "orphan.callable".into(),
        mapping.callables["egglog.core.i64.abs"].clone(),
    );
    assert!(
        orphan
            .join(&catalog)
            .unwrap_err()
            .contains("orphan Rust callable mapping: orphan.callable")
    );
}

// Every fixture uses actual native signatures and checks complete export.
fn native_fixture() -> (pb::BuiltinCatalog, RustPresentation) {
    let catalog = egglog_experimental::new_experimental_egraph()
        .type_info()
        .portable_builtin_catalog()
        .unwrap();
    assert!(catalog.undescribed_primitives.is_empty());
    assert!(catalog.undescribed_families.is_empty());
    assert!(catalog.undescribed_family_primitives.is_empty());
    assert!(catalog.undescribed_sorts.is_empty());
    (catalog.definitions, RustPresentation::builtin().unwrap())
}

// Generation may add a frontend-owned type closure, but cannot mutate or
// rewrite native definitions or their existing graph locations.
fn checked_source(program: &pb::BuiltinCatalog, mapping: &RustPresentation) -> String {
    let before = program.encode_to_vec();
    let (source, deferred, joined) = generate(program, mapping).unwrap();
    assert!(deferred.is_empty(), "{deferred:?}");
    assert_eq!(program.encode_to_vec(), before);
    assert_eq!(joined.primitives, program.primitives);
    assert_eq!(joined.primitive_sorts, program.primitive_sorts);
    assert_eq!(joined.sorts, program.sorts);
    source
}

#[test]
fn complete_native_catalog_uses_existing_generic_and_function_views() {
    let (program, mapping) = native_fixture();
    let source = checked_source(&program, &mapping);
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
        "pub fn subst<__EgglogType0: crate::typed::EgglogValue, __EgglogType1: crate::typed::EgglogValue>(__egglog_arg_0: __EgglogType0, __egglog_arg_1: self::Map<__EgglogType1, __EgglogType1>) -> __EgglogType0",
    ] {
        assert!(
            source.contains(method),
            "missing generated method: {method}"
        );
    }
}

#[test]
fn generic_free_functions_follow_binders_slots_names_and_results() {
    let (program, mapping) = native_fixture();
    let baseline = checked_source(&program, &mapping);
    assert!(baseline.contains("pub fn ne<__EgglogType0: crate::typed::expr::ValueInput>(__egglog_arg_0: __EgglogType0, __egglog_arg_1: impl ::core::convert::Into<<__EgglogType0 as crate::typed::expr::ValueInput>::Owned>) -> self::Unit"));
    for reverse in [false, true] {
        let mut changed = program.clone();
        let mut local = mapping.clone();
        let index = changed
            .primitives
            .iter()
            .position(|p| p.name == "egglog.core.ne")
            .unwrap();
        let p = &mut changed.primitives[index];
        p.name = "test.generic.renamed".into();
        let mut views = local.callables.remove("egglog.core.ne").unwrap();
        views[0].path[3] = "renamed_generic".into();
        views[0].params.reverse();
        views[0].params[0].name = "__egglog_record".into();
        local.callables.insert(p.name.clone(), views);
        if reverse {
            changed.primitives.reverse();
            changed.primitive_sorts.reverse();
        }
        let source = checked_source(&changed, &local);
        let body = source
            .split_once("pub fn renamed_generic<")
            .unwrap()
            .1
            .split_once("\n    }\n")
            .unwrap()
            .0;
        assert!(body.contains("crate::typed::expr::ValueInput"));
        assert!(
            body.find("Into::into(__egglog_arg_1)").unwrap()
                < body.find("Borrow::borrow(&__egglog_arg_0)").unwrap()
        );
        let location = if reverse {
            changed.primitives.len() - 1 - index
        } else {
            index
        };
        assert!(body.contains(&format!(".index = {location};")));
        assert!(!source.contains("test.generic.renamed"));
    }
    let mut absent = mapping.clone();
    absent.callables.remove("egglog.core.ne");
    let (source, deferred, _) = generate(&program, &absent).unwrap();
    assert!(deferred.contains(&"egglog.core.ne".into()));
    assert!(!source.contains("pub fn ne<"));
}

#[test]
fn generic_free_functions_reject_unsupported_or_ambiguous_views() {
    let (program, mapping) = native_fixture();
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
        (10, "undetermined generic parameter"),
        (11, "unsupported generic Rust free function view"),
        (12, "Rust free function name collision"),
        (13, "unsupported Rust identifier"),
    ] {
        let mut changed = program.clone();
        let mut local = mapping.clone();
        let views = local.callables.get_mut("egglog.core.ne").unwrap();
        let view = &mut views[0];
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
            8 => view.trait_impl = Some(TraitView::default()),
            9 => view.tail_repetitions = Some(0),
            10 | 11 => {
                let p = changed
                    .primitives
                    .iter_mut()
                    .find(|p| p.name == "egglog.core.ne")
                    .unwrap();
                let Some(s) = &mut p.signature else { panic!() };
                if case == 10 {
                    s.type_param_count += 1;
                } else {
                    s.varargs.push(s.inputs[0]);
                }
            }
            12 => {
                let duplicate = view.clone();
                views.push(duplicate);
            }
            13 => view.path[3] = "not-a-name".into(),
            _ => unreachable!(),
        }
        let error = generate(&changed, &local).unwrap_err();
        assert!(error.starts_with(expected), "case {case}: {error}");
    }
    let mut local = mapping.clone();
    local.callables.insert(
        "egglog.core.fn.apply".into(),
        local.callables["egglog.core.ne"].clone(),
    );
    assert_eq!(
        generate(&program, &local).unwrap_err(),
        "orphan Rust callable mapping: egglog.core.fn.apply"
    );
}

#[test]
fn bignum_operator_traits_follow_actual_input_and_output_sorts() {
    let (program, mapping) = native_fixture();
    let source = checked_source(&program, &mapping);
    for lhs in ["", "&"] {
        assert!(source.contains(&format!("impl ::core::ops::Neg for {lhs}self::BigRat")));
        for rhs in ["", "&"] {
            for name in ["Shl", "Shr"] {
                assert!(source.contains(&format!(
                    "impl ::core::ops::{name}<{rhs}self::I64> for {lhs}self::BigInt"
                )));
                assert!(!source.contains(&format!(
                    "impl ::core::ops::{name}<{rhs}self::BigInt> for {lhs}self::BigInt"
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
        let mut local = mapping.clone();
        local.callables.get_mut(provider).unwrap()[0]
            .receiver
            .as_mut()
            .unwrap()
            .core_input = Some(1);
        assert!(
            generate(&program, &local).is_err(),
            "invalid receiver for {provider}"
        );
    }
}

#[test]
fn exact_number_codecs_leave_constructor_views_and_records_authoritative() {
    let (program, mapping) = native_fixture();
    let source = checked_source(&program, &mapping);
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
        for borrow in ["", "&"] {
            assert!(source.contains(&format!(
                "impl ::core::convert::{conversion}<{borrow}{host}> for self::{family}"
            )));
        }
        if family != "BigInt" {
            assert!(!source.contains(&format!(
                "impl ::core::convert::From<{host}> for self::{family}"
            )));
        }
    }
    for provider in [
        "egglog.core.bigint.from_i64",
        "egglog.core.bigint.from_string",
        "egglog.core.bigrat.make",
        "egglog.experimental.rational.make",
    ] {
        let mut local = mapping.clone();
        local.callables.get_mut(provider).unwrap()[0].path = vec!["renamed_constructor".into()];
        assert!(checked_source(&program, &local).contains("pub fn renamed_constructor("));
    }
    let mut local = mapping.clone();
    for family in ["BigInt", "BigRat", "Rational"] {
        local.families.get_mut(family).unwrap().path[3].push_str("Value");
    }
    let source = checked_source(&program, &local);
    assert!(source.contains("From<::num::BigInt> for self::BigIntValue"));
    assert!(source.contains("TryFrom<::num::BigRational> for self::BigRatValue"));
    assert!(source.contains("TryFrom<::num::rational::Rational64> for self::RationalValue"));
}

#[test]
fn map_data_codec_and_operations_follow_their_own_typed_records() {
    let (program, mapping) = native_fixture();
    let baseline = checked_source(&program, &mapping);
    assert!(baseline.contains("pub fn entries(&self)"));
    assert!(baseline.contains("pub fn of<"));
    let mut local = mapping.clone();
    local.families.get_mut("Map").unwrap().path[3] = "RenamedMap".into();
    local.callables.get_mut("egglog.core.map.get").unwrap()[0].path[0] = "lookup".into();
    let source = checked_source(&program, &local);
    assert!(source.contains("pub struct RenamedMap"));
    assert!(source.contains("pub fn lookup("));
    for case in [0, 2, 3, 4] {
        let mut changed = program.clone();
        let p = changed
            .primitives
            .iter_mut()
            .find(|p| p.name == "egglog.core.map.of")
            .unwrap();
        let Some(s) = &mut p.signature else { panic!() };
        match case {
            0 => {
                s.type_param_count -= 1;
            }
            2 => s.inputs.clear(),
            3 => s.output = Some(s.inputs[0]),
            _ => s.varargs.push(s.inputs[0]),
        }
        if case == 3 {
            // from_pairs is a catalog operation; its declared result determines
            // the public return type. The separate Map::of data codec does not
            // depend on that operation or assume its result is a Map.
            let source = checked_source(&changed, &mapping);
            let operation = source
                .split_once("pub fn from_pairs(")
                .unwrap()
                .1
                .split_once("\n    }\n")
                .unwrap()
                .0;
            assert!(operation.contains("-> self::Vec<self::Pair<"));
            assert!(operation.contains("Expr::call_with_result("));
            let data = source
                .split_once("pub fn of<")
                .unwrap()
                .1
                .split_once("\n    }\n")
                .unwrap()
                .0;
            assert!(data.contains("-> Self"));
            assert!(data.contains("Expr::container("));
        } else {
            assert!(generate(&changed, &mapping).is_err(), "Map negative {case}");
        }
    }
}

#[test]
fn maybe_codec_follows_catalog_identity_and_checks_optional_child_scheme() {
    let (program, mapping) = native_fixture();
    let baseline = checked_source(&program, &mapping);
    for method in ["none()", "some(", "unwrap(&self)", "unwrap_or(&self,"] {
        assert!(baseline.contains(&format!("pub fn {method}")));
    }
    let mut local = mapping.clone();
    local.families.get_mut("Maybe").unwrap().path[3] = "__EgglogType0".into();
    for (key, name) in [
        ("egglog.experimental.maybe.none", "absent"),
        ("egglog.experimental.maybe.some", "present"),
    ] {
        local.callables.get_mut(key).unwrap()[0].path[0] = name.into();
    }
    let source = checked_source(&program, &local);
    assert!(source.contains("pub fn absent()"));
    assert!(source.contains("pub fn present("));
    assert!(source.contains("__EgglogType0_"));
    for case in 0..4 {
        let mut changed = program.clone();
        let p = changed
            .primitives
            .iter_mut()
            .find(|p| p.name == "egglog.experimental.maybe.some")
            .unwrap();
        let Some(s) = &mut p.signature else { panic!() };
        match case {
            0 => s.inputs.clear(),
            1 => s.output = Some(s.inputs[0]),
            2 => s.type_param_count += 1,
            _ => s.varargs.push(s.inputs[0]),
        }
        assert!(
            generate(&changed, &mapping).is_err(),
            "Maybe negative {case}"
        );
    }
}

#[test]
fn pair_codec_follows_catalog_identity_paths_and_two_binders() {
    let (program, mapping) = native_fixture();
    let source = checked_source(&program, &mapping);
    assert!(source.contains("pub fn fields(&self)"));
    let mut local = mapping.clone();
    local.families.get_mut("Pair").unwrap().path[3] = "__EgglogType0".into();
    for (key, name) in [("make", "assemble"), ("first", "left"), ("second", "right")] {
        local
            .callables
            .get_mut(&format!("egglog.core.pair.{key}"))
            .unwrap()[0]
            .path[0] = name.into();
    }
    let source = checked_source(&program, &local);
    for method in ["assemble(", "left(&self)", "right(&self)", "fields(&self)"] {
        assert!(source.contains(&format!("pub fn {method}")));
    }
    for case in 0..4 {
        let mut changed = program.clone();
        let p = changed
            .primitives
            .iter_mut()
            .find(|p| p.name == "egglog.core.pair.make")
            .unwrap();
        let Some(s) = &mut p.signature else { panic!() };
        match case {
            0 => {
                s.inputs.pop();
            }
            1 => s.output = Some(s.inputs[0]),
            2 => {
                s.type_param_count -= 1;
            }
            _ => s.varargs.push(s.inputs[0]),
        }
        assert!(
            generate(&changed, &mapping).is_err(),
            "Pair negative {case}"
        );
    }
}

#[test]
fn scalar_tail_views_derive_slots_and_trait_identity_from_actual_records() {
    let (program, mut mapping) = native_fixture();
    for (key, name) in [
        ("egglog.core.bool.and", "and_all"),
        ("egglog.core.bool.or", "or_all"),
    ] {
        let views = mapping.callables.get_mut(key).unwrap();
        let mut method = views[0].clone();
        method.path = vec![name.into()];
        method.trait_impl = None;
        views.push(method);
    }
    let baseline = checked_source(&program, &mapping);
    assert!(baseline.contains("pub fn join("));
    assert!(baseline.contains("pub fn and_all("));
    assert!(baseline.contains("pub fn or_all("));
    for key in ["egglog.core.string.concat", "egglog.core.bool.or"] {
        for case in 0..7 {
            let mut local = mapping.clone();
            let view = local.callables.get_mut(key).unwrap().last_mut().unwrap();
            match case {
                0 => view.params[0].core_input = Some(0),
                1 => view.params.clear(),
                2 => view.params[0].core_input = None,
                3 => view.receiver = None,
                4 => view.owner_sort = None,
                5 => view.tail_repetitions = Some(u32::MAX),
                _ => view.tail_repetitions = Some(0),
            }
            assert!(generate(&program, &local).is_err(), "{key}/{case}");
        }
    }
    let mut local = mapping.clone();
    let view = local
        .callables
        .get_mut("egglog.core.bool.or")
        .unwrap()
        .last_mut()
        .unwrap();
    view.tail_repetitions = None;
    view.receiver.as_mut().unwrap().borrowed = true;
    assert!(
        checked_source(&program, &local)
            .contains("pub fn or_all(&self, __egglog_arg_0: impl ::core::iter::IntoIterator")
    );
}

#[test]
fn optional_documentation_renders_without_rewriting_records() {
    let (program, mapping) = native_fixture();
    for doc in [None, Some(""), Some("π and \\\"quoted\\\" docs")] {
        let mut changed = program.clone();
        for declaration in &mut changed.primitives {
            declaration.doc = doc.map(str::to_owned);
        }
        for primitive_sort in &mut changed.primitive_sorts {
            primitive_sort.doc = doc.map(str::to_owned);
        }
        let source = checked_source(&changed, &mapping);
        if let Some(doc) = doc {
            if !doc.is_empty() {
                assert!(source.contains("π and"));
            }
        }
    }
}

#[test]
fn grouped_tail_views_are_explicitly_rejected_but_records_are_retained() {
    let (program, mapping) = native_fixture();
    let key = "egglog.core.ne";
    let mut changed = program.clone();
    let p = changed
        .primitives
        .iter_mut()
        .find(|p| p.name == key)
        .unwrap();
    let Some(s) = &mut p.signature else { panic!() };
    if s.varargs.is_empty() {
        s.varargs = s.inputs.clone();
        s.inputs.clear();
    }
    s.varargs.push(s.varargs[0]);
    let before = changed.encode_to_vec();
    assert!(generate(&changed, &mapping).is_err());
    assert_eq!(changed.encode_to_vec(), before);
    let mut local = mapping.clone();
    local.callables.remove(key);
    let (source, deferred, _) = generate(&changed, &local).unwrap();
    assert!(deferred.contains(&key.to_string()));
    assert!(!source.is_empty());
    assert_eq!(changed.encode_to_vec(), before);
}

#[test]
fn ordinary_metadata_names_cannot_capture_generated_support() {
    let (program, mapping) = native_fixture();
    for (integer, float, param) in [
        ("i64", "f64", "catalog"),
        ("From", "TryFrom", "Callable"),
        ("Result", "Some", "__egglog_record"),
        ("Expr", "SortRef", "record"),
        ("Clone", "Into", "value"),
        ("value", "__egglog_value", "__egglog_record_"),
        ("catalog", "Callable", "catalog"),
    ] {
        let mut local = mapping.clone();
        local.families.get_mut("i64").unwrap().path[3] = integer.into();
        local.families.get_mut("f64").unwrap().path[3] = float.into();
        for view in local
            .callables
            .values_mut()
            .flatten()
            .filter(|v| v.trait_impl.is_some())
        {
            for p in &mut view.params {
                p.name = param.into();
            }
        }
        let source = checked_source(&program, &local);
        for marker in [
            "::core::primitive::i64",
            "::core::primitive::f64",
            "::core::convert::From<",
            "::core::convert::TryFrom<",
            "::core::result::Result<",
            "::core::option::Option::Some(",
            "crate::typed::decl::Callable(",
        ] {
            assert!(source.contains(marker));
        }
        assert!(!source.contains("= catalog()"));
        assert!(!source.contains("(Expr)"));
    }
}

#[test]
fn i64_i32_inputs_follow_catalog_binding() {
    let (program, mapping) = native_fixture();
    for name in ["I64", "RenamedI64"] {
        let mut local = mapping.clone();
        local.families.get_mut("i64").unwrap().path[3] = name.into();
        let source = checked_source(&program, &local);
        for input in ["::core::primitive::i32", "&::core::primitive::i32"] {
            assert!(source.contains(&format!(
                "impl ::core::convert::From<{input}> for self::{name}"
            )));
            assert!(!source.contains(&format!(
                "impl ::core::convert::From<{input}> for self::F64"
            )));
        }
        assert_eq!(source.matches("From<::core::primitive::i32>").count(), 1);
        assert_eq!(source.matches("From<&::core::primitive::i32>").count(), 1);
    }
}

#[test]
fn operand_metadata_names_never_become_rust_binding_patterns() {
    let (program, mapping) = native_fixture();
    for parameter in ["Some", "None", "Ok", "Err", "__egglog_rhs"] {
        let mut local = mapping.clone();
        for view in local
            .callables
            .values_mut()
            .flatten()
            .filter(|v| v.trait_impl.is_some())
        {
            for p in &mut view.params {
                p.name = parameter.into();
            }
        }
        let source = checked_source(&program, &local);
        assert!(!source.contains(&format!("fn add(self, {parameter}:")));
        let expected = if parameter == "__egglog_rhs" {
            "__egglog_rhs_"
        } else {
            "__egglog_rhs"
        };
        assert_eq!(
            source.matches(&format!("fn add(self, {expected}:")).count(),
            local
                .callables
                .values()
                .flatten()
                .filter(|v| v.path == ["add"])
                .count()
                * 4
        );
    }
}

// Operations retain their selected declaration indices; data constructors pack
// child fields directly. Neither route depends on public presentation spelling.
fn assert_locations(program: &pb::BuiltinCatalog, mapping: &RustPresentation, source: &str) {
    let (program, mapping) = mapping.join(program).unwrap();
    for (index, p) in program.primitives.iter().enumerate() {
        let Some(views) = mapping.callables.get(&p.name) else {
            continue;
        };
        for view in views.iter().filter(|v| v.trait_impl.is_none()) {
            let name = view.path.last().unwrap();
            let marker = format!("pub fn {name}");
            let expected = if matches!(
                p.name.as_str(),
                "egglog.core.vec.of"
                    | "egglog.core.vec.empty"
                    | "egglog.core.set.of"
                    | "egglog.core.set.empty"
                    | "egglog.core.multiset.of"
                    | "egglog.core.pair.make"
                    | "egglog.core.map.empty"
                    | "egglog.experimental.maybe.none"
                    | "egglog.experimental.maybe.some"
            ) {
                "Expr::container(".to_owned()
            } else {
                format!(".index = {index};")
            };
            assert!(
                source
                    .split(&marker)
                    .skip(1)
                    .any(|part| { part.split_once("\n    }\n").unwrap().0.contains(&expected) }),
                "missing {name} at {index}"
            );
        }
    }
    for (index, sort) in program.sorts.iter().enumerate() {
        let Some(pb::sort::Kind::Primitive(f)) = &sort.kind else {
            continue;
        };
        if !f.args.is_empty()
            || !matches!(f.name.as_str(), "i64" | "f64" | "String" | "bool" | "Unit")
        {
            continue;
        }
        let name = &mapping.families[&f.name].path[3];
        let body = source
            .split_once(&format!("EgglogValue for self::{name} {{"))
            .unwrap()
            .1
            .split_once("fn expression")
            .unwrap()
            .0;
        assert!(
            body.contains(&format!(".index = {index};")),
            "wrong sort location for {name}"
        );
    }
}

#[test]
fn closed_i64_operator_views_preserve_slots_and_all_ownership_forms() {
    let (program, mapping) = native_fixture();
    let baseline = checked_source(&program, &mapping);
    for (key, method) in [
        ("add", "add"),
        ("sub", "sub"),
        ("mul", "mul"),
        ("div", "div"),
        ("rem", "rem"),
        ("shl", "shl"),
        ("shr", "shr"),
    ] {
        let provider = format!("egglog.core.i64.{key}");
        let mut local = mapping.clone();
        let view = &mut local.callables.get_mut(&provider).unwrap()[0];
        view.receiver.as_mut().unwrap().core_input = Some(1);
        view.params[0].core_input = Some(0);
        view.params[0].name = "__egglog_rhs".into();
        let source = checked_source(&program, &local);
        assert!(source.contains("::std::vec![::core::clone::Clone::clone(&__egglog_rhs_.0), ::core::clone::Clone::clone(&self.0)]"));
        for lhs in ["", "&"] {
            for rhs in ["", "&"] {
                let trait_name = match method {
                    "add" => "Add",
                    "sub" => "Sub",
                    "mul" => "Mul",
                    "div" => "Div",
                    "rem" => "Rem",
                    "shl" => "Shl",
                    _ => "Shr",
                };
                assert!(source.contains(&format!(
                    "impl ::core::ops::{trait_name}<{rhs}self::I64> for {lhs}self::I64"
                )));
            }
        }
    }
    assert_locations(&program, &mapping, &baseline);
}

#[test]
fn native_records_determine_paths_locations_and_argument_order() {
    let (program, mapping) = native_fixture();
    let mut changed = program.clone();
    let mut local = mapping.clone();
    let index = changed
        .primitives
        .iter()
        .position(|p| p.name == "egglog.core.i64.add")
        .unwrap();
    let p = &mut changed.primitives[index];
    p.name = "test.renamed.scalar.add".into();
    let mut views = local.callables.remove("egglog.core.i64.add").unwrap();
    views[0].receiver.as_mut().unwrap().core_input = Some(1);
    views[0].params[0].core_input = Some(0);
    local.callables.insert(p.name.clone(), views);
    let source = checked_source(&changed, &local);
    assert_locations(&changed, &local, &source);
    changed.primitives.reverse();
    changed.primitive_sorts.reverse();
    local.families.get_mut("i64").unwrap().path[3] = "RenamedI64".into();
    let reversed = checked_source(&changed, &local);
    assert_locations(&changed, &local, &reversed);
    assert!(reversed.contains("pub struct RenamedI64"));
    let last = changed.sorts.len() as u32 - 1;
    changed.sorts.reverse();
    for sort in &mut changed.sorts {
        match &mut sort.kind {
            Some(pb::sort::Kind::Primitive(f)) => {
                for i in &mut f.args {
                    *i = last - *i
                }
            }
            Some(pb::sort::Kind::Func(f)) => {
                for i in &mut f.params {
                    *i = last - *i
                }
                f.result = last - f.result
            }
            _ => {}
        }
    }
    for primitive in &mut changed.primitives {
        if let Some(s) = &mut primitive.signature {
            for a in s.inputs.iter_mut().chain(&mut s.varargs) {
                *a = last - *a
            }
            let output = s.output.as_mut().unwrap();
            *output = last - *output;
        }
    }
    // No local presentation relocation: its graph owner remains independent.
    let relocated = checked_source(&changed, &local);
    assert_locations(&changed, &local, &relocated);
    assert_ne!(relocated, reversed);
}

#[test]
fn malformed_mapping_and_generated_borrow_collisions_are_errors() {
    let (program, mapping) = native_fixture();
    for slot in [0, 2] {
        let mut local = mapping.clone();
        local.callables.get_mut("egglog.core.i64.add").unwrap()[0].params[0].core_input =
            Some(slot);
        assert!(generate(&program, &local).is_err());
    }
    let mut local = mapping.clone();
    let views = local.callables.get_mut("egglog.core.i64.add").unwrap();
    views.push(views[0].clone());
    assert!(generate(&program, &local).is_err());
    let mut local = mapping.clone();
    local.families.get_mut("f64").unwrap().path[3] = "I64".into();
    assert!(
        generate(&program, &local)
            .unwrap_err()
            .contains("collision")
    );
}

#[test]
fn associated_owner_is_owned_and_independent_of_result_sort() {
    let (program, mut mapping) = native_fixture();
    let owner = mapping.callables["egglog.core.f64.abs"][0]
        .owner_sort
        .clone();
    let view = &mut mapping.callables.get_mut("egglog.core.i64.abs").unwrap()[0];
    view.owner_sort = owner;
    view.receiver = None;
    view.path = vec!["associated".into()];
    view.params = vec![Parameter {
        core_input: Some(0),
        name: "value".into(),
        borrowed: false,
    }];
    let source = checked_source(&program, &mapping);
    let body = source
        .split_once("pub fn associated(")
        .unwrap()
        .1
        .split_once("\n    }\n")
        .unwrap()
        .0;
    assert!(body.contains("Into<self::I64>"));
    assert!(body.contains("-> self::I64"));
    let owner = source
        .split_once("pub fn associated(")
        .unwrap()
        .0
        .rsplit_once("impl self::F64 {")
        .unwrap()
        .1;
    assert!(!owner.contains("\n}"));
}

#[test]
fn local_type_fragments_import_missing_closures_and_reject_invalid_graphs() {
    let (program, mut mapping) = native_fixture();
    let graph = Arc::new(pb::BuiltinCatalog {
        sorts: vec![
            pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                    name: "i64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                    name: "f64".into(),
                    args: vec![],
                })),
                ..Default::default()
            },
            pb::Sort {
                kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                    name: "Pair".into(),
                    args: vec![0, 1],
                })),
                ..Default::default()
            },
        ],
        ..Default::default()
    });
    mapping.callables.get_mut("egglog.core.i64.abs").unwrap()[0].owner_sort = Some(SortRef {
        graph: graph.clone(),
        root: 2,
    });
    drop(graph);
    let (joined, local) = mapping.join(&program).unwrap();
    assert_eq!(joined.primitives, program.primitives);
    assert_eq!(joined.sorts.len(), program.sorts.len() + 1);
    let owner = local.callables["egglog.core.i64.abs"][0]
        .owner_sort
        .clone()
        .unwrap();
    drop(joined);
    drop(local);
    assert!(
        matches!(&owner.graph.sorts[owner.root as usize].kind, Some(pb::sort::Kind::Primitive(f)) if f.name == "Pair" && f.args.len() == 2)
    );
    mapping.callables.get_mut("egglog.core.i64.abs").unwrap()[0]
        .owner_sort
        .as_mut()
        .unwrap()
        .root = u32::MAX;
    assert!(
        mapping
            .join(&program)
            .unwrap_err()
            .contains("out of bounds")
    );
    let cyclic = Arc::new(pb::BuiltinCatalog {
        sorts: vec![pb::Sort {
            kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                name: "Vec".into(),
                args: vec![0],
            })),
            ..Default::default()
        }],
        ..Default::default()
    });
    mapping.callables.get_mut("egglog.core.i64.abs").unwrap()[0].owner_sort = Some(SortRef {
        graph: cyclic,
        root: 0,
    });
    assert!(mapping.join(&program).unwrap_err().contains("cyclic"));
}

#[test]
fn native_set_catalog_drives_every_method_and_rejects_invalid_views() {
    let (program, mapping) = native_fixture();
    let source = checked_source(&program, &mapping);
    for method in [
        "empty(",
        "of(",
        "contains(",
        "insert(",
        "remove(",
        "union(",
        "intersect(",
        "diff(",
        "length(",
        "get(",
    ] {
        assert!(source.contains(&format!("pub fn {method}")), "{method}");
    }
    let mut local = mapping.clone();
    local.families.get_mut("Set").unwrap().path[3] = "RenamedSet".into();
    local.callables.get_mut("egglog.core.set.get").unwrap()[0].path[0] = "pick".into();
    let source = checked_source(&program, &local);
    assert!(source.contains("pub struct RenamedSet"));
    assert!(source.contains("pub fn pick("));
    for case in 0..7 {
        let mut local = mapping.clone();
        let view = &mut local.callables.get_mut("egglog.core.set.get").unwrap()[0];
        match case {
            0 => view.params[0].core_input = Some(0),
            1 => view.params.clear(),
            2 => view.receiver = None,
            3 => view.receiver.as_mut().unwrap().core_input = Some(1),
            4 => view.path.push("qualified".into()),
            5 => view.borrowed_self = true,
            _ => view.owner_sort = None,
        }
        assert!(generate(&program, &local).is_err(), "Set negative {case}");
    }
}

#[test]
fn native_vec_views_drive_generic_members_and_relocated_declarations() {
    let (program, mapping) = native_fixture();
    for reverse in [false, true] {
        let mut changed = program.clone();
        if reverse {
            changed.primitives.reverse();
            changed.primitive_sorts.reverse();
        }
        let source = checked_source(&changed, &mapping);
        assert_locations(&changed, &mapping, &source);
    }
    let mut local = mapping.clone();
    local.callables.get_mut("egglog.core.vec.get").unwrap()[0].path[0] = "pick".into();
    assert!(checked_source(&program, &local).contains("pub fn pick("));
    local.callables.get_mut("egglog.core.vec.get").unwrap()[0]
        .receiver
        .as_mut()
        .unwrap()
        .core_input = Some(1);
    assert!(generate(&program, &local).is_err());
    let mut changed = program.clone();
    let integer=changed.sorts.iter().position(|s|matches!(&s.kind,Some(pb::sort::Kind::Primitive(f))if f.name=="i64"&&f.args.is_empty())).unwrap()as u32;
    let p = changed
        .primitives
        .iter_mut()
        .find(|p| p.name == "egglog.core.vec.get")
        .unwrap();
    let Some(s) = &mut p.signature else { panic!() };
    s.output = Some(integer);
    assert!(checked_source(&changed, &mapping).contains("-> self::I64"));
    let graph = Arc::new(pb::BuiltinCatalog {
        sorts: vec![pb::Sort {
            kind: Some(pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
                name: "i64".into(),
                args: vec![],
            })),
            ..Default::default()
        }],
        ..Default::default()
    });
    let mut local = mapping.clone();
    let owner = local.callables.get_mut("egglog.core.i64.add").unwrap()[0]
        .owner_sort
        .as_mut()
        .unwrap();
    *owner = SortRef {
        graph: graph.clone(),
        root: 0,
    };
    drop(graph);
    assert_eq!(
        checked_source(&program, &local),
        checked_source(&program, &mapping)
    );
}

#[test]
fn generic_count_must_be_determined_by_actual_referenced_sorts() {
    let (mut catalog, mapping) = native_fixture();
    catalog
        .primitives
        .iter_mut()
        .find(|p| p.name == "egglog.core.ne")
        .unwrap()
        .signature
        .as_mut()
        .unwrap()
        .type_param_count = u32::MAX;
    assert!(
        generate(&catalog, &mapping)
            .unwrap_err()
            .contains("undetermined generic parameter")
    );
}
