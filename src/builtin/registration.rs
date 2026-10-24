//! Portable metadata is checked against native registrations before publication.

use super::*;

#[derive(Clone, Default)]
pub(super) struct PortableMetadata {
    pub(super) primitives: HashMap<String, (Arc<BuiltinDescription>, pb::Program)>,
    pub(super) families: HashMap<String, (Arc<FamilyDescription>, pb::HostSortFamily)>,
}

/// Project family presentation belonging to this exact native registry owner.
pub fn family_metadata(
    types: &TypeInfo,
    family: &FamilyDescription,
) -> Result<pb::HostSortFamily, String> {
    let owner = types.registered_builtin_family(&family.name)?;
    if owner.as_ref() != family {
        return Err("native family description mismatch".into());
    }
    if let Some((_, family)) = types
        .extension_state::<PortableMetadata>()
        .and_then(|metadata| metadata.families.get(&family.name))
        .filter(|(registered, _)| Arc::ptr_eq(registered, &owner))
    {
        return Ok(family.clone());
    }
    let bindings = LANGUAGE_METADATA
        .declarations
        .iter()
        .find_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::HostSortFamily(known)) if known.name == family.name => {
                known.bindings.clone()
            }
            _ => None,
        });
    Ok(pb::HostSortFamily {
        name: family.name.clone(),
        arity: u32::try_from(family.arity).map_err(|_| "family arity exceeds wire limits")?,
        bindings,
    })
}

fn family_context(types: &TypeInfo) -> Result<pb::Program, String> {
    let mut program = pb::Program {
        ..Default::default()
    };
    for family in types.builtin_catalog()?.families {
        program.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::HostSortFamily(family_metadata(
                types, &family,
            )?)),
            ..Default::default()
        });
    }
    Ok(program)
}

/// Metadata-only registration operations on a native type environment.
pub trait PortableRegistration {
    /// Build and validate a root's closed default context without native writes.
    fn prepare_builtin_context(
        &self,
        key: &str,
        alias: &str,
        generated: pb::Program,
        supply: impl FnOnce(&TypeInfo, &str, &mut pb::Program) -> Result<(), String>,
    ) -> Result<pb::Program, String>;

    /// Add presentation at the native family's own registration site.
    fn register_portable_family(&mut self, family: pb::HostSortFamily) -> Result<(), String>;
}

fn check_context(
    types: &TypeInfo,
    key: &str,
    alias: &str,
    context: &pb::Program,
) -> Result<(), String> {
    let native = types.builtin_catalog()?;
    if key == alias
        || alias.is_empty()
        || types.is_primitive(key)
        || types.get_func_type(key).is_some()
        || types.is_primitive(alias)
        || types.get_func_type(alias).is_some()
    {
        return Err(format!(
            "builtin context registration collision: {key}/{alias}"
        ));
    }
    let (_, primitive) = definition_root(context, key)?;
    normalized_signature(context, primitive, &mut vec![])?;
    definitions::check_builtin_context_families(context, &family_context(types)?)?;
    for declaration in &context.declarations {
        if let Some(pb::declaration::Kind::HostSortFamily(family)) = &declaration.kind
            && (!context.sorts.iter().any(|sort| {
                matches!(&sort.kind,
                Some(pb::sort::Kind::Family(sort)) if sort.name == family.name)
            }) || !native
                .families
                .iter()
                .any(|known| known.name == family.name && known.arity == family.arity as usize))
        {
            return Err(format!(
                "unregistered or unused builtin context family {}",
                family.name
            ));
        }
    }
    for sort in &context.sorts {
        if let Some(pb::sort::Kind::Family(sort)) = &sort.kind
            && !native
                .families
                .iter()
                .any(|family| family.name == sort.name && family.arity == sort.args.len())
        {
            return Err(format!(
                "unregistered builtin context family sort {}",
                sort.name
            ));
        }
    }
    definitions::check_builtin_context(context, key, |helper| {
        let description = types
            .builtin_description(helper)
            .map_err(|_| format!("unregistered builtin context helper {helper}"))?;
        let implementations = types
            .get_prims(helper)
            .filter(|implementations| !implementations.is_empty())
            .ok_or_else(|| {
                format!("builtin context helper {helper} has no registered implementation")
            })?;
        for implementation in implementations {
            let registered = implementation
                .primitive
                .builtin_description()
                .ok_or("registered helper has no native description")?;
            if registered != description
                || !implementation
                    .context_ids
                    .iter()
                    .any(|(_, id)| id.is_some())
                || implementation
                    .primitive
                    .builtin_instance()
                    .is_some_and(|instance| {
                        instance.description.key != helper
                            || !std::ptr::eq(description, instance.description.as_ref())
                    })
            {
                return Err(format!(
                    "builtin context helper {helper} lacks native ownership"
                ));
            }
        }
        let mut program = pb::Program::default();
        types.export_builtin_definition(helper, &mut program)?;
        Ok(program)
    })
}

impl PortableRegistration for TypeInfo {
    fn prepare_builtin_context(
        &self,
        key: &str,
        alias: &str,
        generated: pb::Program,
        supply: impl FnOnce(&TypeInfo, &str, &mut pb::Program) -> Result<(), String>,
    ) -> Result<pb::Program, String> {
        if definition_key(&generated)? != key {
            return Err("generated builtin root identity mismatch".into());
        }
        let mut family_keys = HashSet::new();
        for declaration in &generated.declarations {
            if let Some(pb::declaration::Kind::HostSortFamily(family)) = &declaration.kind
                && !family_keys.insert(family.name.as_str())
            {
                return Err(format!(
                    "duplicate generated builtin family {}",
                    family.name
                ));
            }
        }
        let mut sorts = vec![];
        let (_, primitive) = definition_root(&generated, key)?;
        let signature = normalized_signature(&generated, primitive, &mut sorts)?;
        let mut families = family_context(self)?;
        families.declarations.retain(|declaration| matches!(&declaration.kind,
            Some(pb::declaration::Kind::HostSortFamily(family)) if generated.sorts.iter().any(|sort|
                matches!(&sort.kind, Some(pb::sort::Kind::Family(sort)) if sort.name == family.name))));
        let mut supplied = pb::Program::default();
        definitions::reconcile_declarations(&families, &mut supplied)?;
        definitions::reconcile_declarations(&generated, &mut supplied)?;
        supply(self, key, &mut supplied)?;
        if !supplied.commands.is_empty() || !supplied.rules.is_empty() {
            return Err("invalid builtin context header".into());
        }
        let (_, primitive) = definition_root(&supplied, key)?;
        if normalized_signature(&supplied, primitive, &mut sorts)? != signature {
            return Err("builtin context changed the generated native signature".into());
        }
        check_context(self, key, alias, &supplied)?;
        definitions::reconcile_declarations(&generated, &mut supplied)?;
        let mut context = pb::Program::default();
        definitions::reconcile_declarations(&supplied, &mut context)?;
        check_context(self, key, alias, &context)?;
        Ok(context)
    }

    fn register_portable_family(&mut self, family: pb::HostSortFamily) -> Result<(), String> {
        let native = FamilyDescription {
            name: family.name.clone(),
            arity: family.arity as usize,
        };
        let mut staged = self.clone();
        staged.register_builtin_family(native.clone())?;
        let owner = staged.registered_builtin_family(&family.name)?;
        let mut canonical = pb::Program {
            declarations: vec![pb::Declaration {
                kind: Some(pb::declaration::Kind::HostSortFamily(family_metadata(
                    &staged, &native,
                )?)),
                ..Default::default()
            }],
            ..Default::default()
        };
        definitions::reconcile_declarations(
            &pb::Program {
                declarations: vec![pb::Declaration {
                    kind: Some(pb::declaration::Kind::HostSortFamily(family)),
                    ..Default::default()
                }],
                ..Default::default()
            },
            &mut canonical,
        )?;
        let Some(pb::declaration::Kind::HostSortFamily(family)) =
            canonical.declarations.remove(0).kind
        else {
            unreachable!()
        };
        staged
            .extension_state_or_default::<PortableMetadata>()
            .families
            .insert(family.name.clone(), (owner, family));
        *self = staged;
        Ok(())
    }
}

fn remember(types: &mut TypeInfo, key: &str, program: pb::Program) -> Result<(), String> {
    let owner = types
        .builtin_catalog()?
        .descriptions
        .into_iter()
        .find(|description| description.key == key)
        .ok_or_else(|| format!("missing registered native description {key}"))?;
    types
        .extension_state_or_default::<PortableMetadata>()
        .primitives
        .insert(key.into(), (owner, program));
    Ok(())
}

/// Validate portable context evidence before publishing a manual primitive.
pub fn add_pure_with_definition<T: PurePrim + Clone>(
    graph: &mut EGraph,
    primitive: T,
    key: &str,
    definition: &pb::Program,
    validator: Option<PrimitiveValidator>,
) -> Result<(), String> {
    let description = primitive
        .builtin_description()
        .ok_or("manual portable registration requires a native description")?;
    if description.key != key {
        return Err("manual builtin root identity mismatch".into());
    }
    let generated = project_description(description)?;
    let context = graph.authoring_type_info().prepare_builtin_context(
        key,
        primitive.name(),
        generated,
        |_, _, draft| {
            *draft = definition.clone();
            Ok(())
        },
    )?;
    let mut staged = graph.clone();
    staged.add_pure_primitive(primitive, validator);
    staged.authoring_type_info().builtin_catalog()?;
    remember(staged.type_info(), key, context)?;
    *graph = staged;
    Ok(())
}

/// Complete a macro's staged native registration after checking its metadata.
/// The scheme comes exclusively from the native macro's registered description.
#[doc(hidden)]
pub fn finish_registration(
    graph: &mut EGraph,
    mut staged: EGraph,
    key: &str,
    alias: &str,
    supply: impl FnOnce(&TypeInfo, &str, &mut pb::Program) -> Result<(), String>,
) -> Result<(), String> {
    let generated = project_description(staged.authoring_type_info().builtin_description(key)?)?;
    let context = graph
        .authoring_type_info()
        .prepare_builtin_context(key, alias, generated, supply)?;
    remember(staged.type_info(), key, context)?;
    *graph = staged;
    Ok(())
}

/// Apply language views while retaining the native source aliases and scheme.
#[doc(hidden)]
pub fn finish_bindings_registration(
    graph: &mut EGraph,
    staged: EGraph,
    key: &str,
    alias: &str,
    bindings: impl FnOnce(&pb::GenericSignature) -> pb::CallableBindings,
) -> Result<(), String> {
    finish_registration(graph, staged, key, alias, |_, key, draft| {
        let mut supplied = draft.clone();
        let declaration = supplied
            .declarations
            .iter_mut()
            .find(|declaration| {
                matches!(&declaration.kind,
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == key)
            })
            .ok_or("missing generated builtin root")?;
        let Some(pb::declaration::Kind::HostPrimitive(primitive)) = &declaration.kind else {
            unreachable!()
        };
        let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
            return Err("bindings require a signature builtin".into());
        };
        declaration.bindings = Some(bindings(signature));
        definitions::reconcile_declarations(&supplied, draft).map(|_| ())
    })
}

/// Shared staging for the three native primitive macro forms.
#[doc(hidden)]
#[macro_export]
macro_rules! __portable_native_registration {
    (@bindings $native:ident, $graph:expr, $alias:literal, $key:literal, $bindings:expr; $($implementation:tt)*) => {{
        let __portable_graph: &mut ::egglog::EGraph = $graph;
        let mut __portable_staged = __portable_graph.clone();
        ::egglog::$native!(&mut __portable_staged, $alias [id = $key] = $($implementation)*);
        $crate::builtin::registration::finish_bindings_registration(
            __portable_graph, __portable_staged, $key, $alias, $bindings,
        ).expect("invalid builtin presentation");
    }};
    (@context $native:ident, $graph:expr, $alias:literal, $key:literal, $context:expr; $($implementation:tt)*) => {{
        let __portable_graph: &mut ::egglog::EGraph = $graph;
        let mut __portable_staged = __portable_graph.clone();
        ::egglog::$native!(&mut __portable_staged, $alias [id = $key] = $($implementation)*);
        $crate::builtin::registration::finish_registration(
            __portable_graph, __portable_staged, $key, $alias, $context,
        ).expect("invalid builtin default context");
    }};
}

/// Register a native primitive with optional Experimental-owned presentation.
#[macro_export]
macro_rules! add_primitive {
    ($graph:expr, $alias:literal [id = $key:literal, bindings = $bindings:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@bindings add_primitive, $graph, $alias, $key, $bindings; $($implementation)*)
    };
    ($graph:expr, $alias:literal [id = $key:literal, context = $context:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@context add_primitive, $graph, $alias, $key, $context; $($implementation)*)
    };
    ($($native:tt)*) => { ::egglog::add_primitive!($($native)*) };
}

/// Register a primitive and validator with optional portable presentation.
#[macro_export]
macro_rules! add_primitive_with_validator {
    ($graph:expr, $alias:literal [id = $key:literal, bindings = $bindings:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@bindings add_primitive_with_validator, $graph, $alias, $key, $bindings; $($implementation)*)
    };
    ($graph:expr, $alias:literal [id = $key:literal, context = $context:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@context add_primitive_with_validator, $graph, $alias, $key, $context; $($implementation)*)
    };
    ($($native:tt)*) => { ::egglog::add_primitive_with_validator!($($native)*) };
}

/// Register literal operations and automatic validators with portable metadata.
#[macro_export]
macro_rules! add_literal_prim {
    ($graph:expr, $alias:literal [id = $key:literal, bindings = $bindings:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@bindings add_literal_prim, $graph, $alias, $key, $bindings; $($implementation)*)
    };
    ($graph:expr, $alias:literal [id = $key:literal, context = $context:expr] = $($implementation:tt)*) => {
        $crate::__portable_native_registration!(@context add_literal_prim, $graph, $alias, $key, $context; $($implementation)*)
    };
    ($($native:tt)*) => { ::egglog::add_literal_prim!($($native)*) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use egglog::ast::Span;

    #[test]
    fn primitive_metadata_isolated_across_clone_and_scope_with_shared_native_owner() {
        const KEY: &str = "test.metadata_snapshot.root";
        let mut original = EGraph::default();
        egglog::add_primitive!(
            &mut original,
            "metadata-snapshot-root"[id = "test.metadata_snapshot.root"] = || -> i64 { 1 }
        );
        let owner = original
            .authoring_type_info()
            .builtin_catalog()
            .unwrap()
            .descriptions
            .into_iter()
            .find(|description| description.key == KEY)
            .unwrap();
        let mut python = project_description(&owner).unwrap();
        let root = python
            .declarations
            .iter_mut()
            .find(|declaration| {
                matches!(&declaration.kind,
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == KEY)
            })
            .unwrap();
        root.bindings.as_mut().unwrap().python = Some(pb::PythonBindings {
            views: vec![pb::PythonCallable {
                kind: pb::PythonCallKind::Function.into(),
                path: vec!["snapshot_root".into()],
                ..Default::default()
            }],
        });
        let mut cloned = original.clone();
        remember(cloned.type_info(), KEY, python.clone()).unwrap();

        let mut both = python;
        let root = both
            .declarations
            .iter_mut()
            .find(|declaration| {
                matches!(&declaration.kind,
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == KEY)
            })
            .unwrap();
        root.bindings.as_mut().unwrap().rust = Some(pb::RustBindings {
            views: vec![pb::RustCallable {
                path: vec!["snapshot_root".into()],
                ..Default::default()
            }],
        });
        let mut newer = cloned.clone();
        remember(newer.type_info(), KEY, both.clone()).unwrap();
        cloned.push();
        remember(cloned.type_info(), KEY, both).unwrap();
        cloned.pop().unwrap();

        for (graph, expected) in [
            (&original, (false, false)),
            (&cloned, (true, false)),
            (&newer, (true, true)),
        ] {
            let native = graph
                .authoring_type_info()
                .builtin_catalog()
                .unwrap()
                .descriptions
                .into_iter()
                .find(|description| description.key == KEY)
                .unwrap();
            assert!(Arc::ptr_eq(&owner, &native));
            let catalog = graph
                .authoring_type_info()
                .portable_builtin_catalog()
                .unwrap();
            let root = catalog
                .definitions
                .declarations
                .iter()
                .find(|declaration| {
                    matches!(&declaration.kind,
                Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == KEY)
                })
                .unwrap();
            let bindings = root.bindings.as_ref().unwrap();
            assert_eq!(
                (bindings.python.is_some(), bindings.rust.is_some()),
                expected
            );
        }
    }

    #[derive(Debug)]
    struct SnapshotScalar;

    impl egglog::prelude::BaseSort for SnapshotScalar {
        type Base = i64;

        fn name(&self) -> &str {
            "MetadataSnapshotScalar"
        }

        fn reconstruct_termdag(
            &self,
            _: &egglog::sort::BaseValues,
            _: Value,
            _: &mut TermDag,
        ) -> TermId {
            panic!("metadata projection must not reconstruct native values")
        }
    }

    #[test]
    fn family_metadata_isolated_across_clone_and_scope_with_shared_native_owner() {
        const NAME: &str = "MetadataSnapshotScalar";
        let mut original = EGraph::default();
        egglog::prelude::add_base_sort(&mut original, SnapshotScalar, Span::Panic).unwrap();
        original
            .type_info()
            .register_builtin_family(FamilyDescription {
                name: NAME.into(),
                arity: 0,
            })
            .unwrap();
        let owner = original
            .authoring_type_info()
            .registered_builtin_family(NAME)
            .unwrap();
        let python = pb::HostSortFamily {
            name: NAME.into(),
            arity: 0,
            bindings: Some(pb::SortBindings {
                python: Some(pb::TypeBinding {
                    path: vec!["SnapshotScalar".into()],
                    type_params: vec![],
                }),
                ..Default::default()
            }),
        };
        let rust = pb::HostSortFamily {
            name: NAME.into(),
            arity: 0,
            bindings: Some(pb::SortBindings {
                rust: Some(pb::TypeBinding {
                    path: vec!["SnapshotScalar".into()],
                    type_params: vec![],
                }),
                ..Default::default()
            }),
        };
        let mut cloned = original.clone();
        cloned.type_info().register_portable_family(python).unwrap();
        let mut newer = cloned.clone();
        newer
            .type_info()
            .register_portable_family(rust.clone())
            .unwrap();
        cloned.push();
        cloned.type_info().register_portable_family(rust).unwrap();
        cloned.pop().unwrap();

        for (graph, expected) in [
            (&original, (false, false)),
            (&cloned, (true, false)),
            (&newer, (true, true)),
        ] {
            let native = graph
                .authoring_type_info()
                .registered_builtin_family(NAME)
                .unwrap();
            assert!(Arc::ptr_eq(&owner, &native));
            let catalog = graph
                .authoring_type_info()
                .portable_builtin_catalog()
                .unwrap();
            let family = catalog
                .definitions
                .declarations
                .iter()
                .find_map(|declaration| match &declaration.kind {
                    Some(pb::declaration::Kind::HostSortFamily(family)) if family.name == NAME => {
                        Some(family)
                    }
                    _ => None,
                })
                .unwrap();
            assert_eq!(
                (
                    family
                        .bindings
                        .as_ref()
                        .is_some_and(|bindings| bindings.python.is_some()),
                    family
                        .bindings
                        .as_ref()
                        .is_some_and(|bindings| bindings.rust.is_some())
                ),
                expected
            );
        }
    }
}
