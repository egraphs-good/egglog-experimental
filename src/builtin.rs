//! Protobuf projection and declaration reconciliation owned by Experimental.

type HashMap<K, V> = std::collections::HashMap<K, V>;
type HashSet<T> = std::collections::HashSet<T>;
use crate::proto as pb;
pub use egglog::builtin::{
    Argument, BuiltinDescription, BuiltinInstance, BuiltinTyping, FamilyDescription, Signature,
    SortPattern, TypeParameter,
};
use egglog::prelude::Span;
use egglog::*;
pub mod definitions;
/// Resolve the concrete scalar endpoints of a portable signature.
pub fn signature_sorts(
    program: &pb::BuiltinCatalog,
    primitive: &pb::Primitive,
) -> Result<Vec<String>, String> {
    let signature = primitive
        .signature
        .as_ref()
        .ok_or("missing builtin signature")?;
    if primitive.name.is_empty() || signature.type_param_count != 0 {
        return Err("builtin typing currently requires a named closed signature".into());
    }
    signature.inputs.iter().chain(&signature.varargs).map(|arg| arg.sort).chain(std::iter::once(signature.output.ok_or("missing builtin result sort")?)).map(|index| {
        let sort = program.sorts.get(index as usize).ok_or("builtin signature sort index out of bounds")?;
        match &sort.kind {
            Some(pb::sort::Kind::Primitive(family)) if family.args.is_empty() && !family.name.is_empty() => Ok(family.name.clone()),
            _ => Err("builtin signature requires a symbolic-family compiler beyond this scalar slice".into()),
        }
    }).collect()
}
pub mod registration;
pub use registration::add_pure_with_definition;

/// Portable declarations plus explicit native provider inventory gaps.
pub struct PortableCatalog {
    /// Portable signatures and authored computations projected from native owners.
    pub definitions: pb::BuiltinCatalog,
    /// Actual callable registrations without a portable projection.
    pub undescribed_primitives: Vec<String>,
    /// Actual family factories without a native description.
    pub undescribed_families: Vec<String>,
    /// Reserved native family operations without a description.
    pub undescribed_family_primitives: Vec<String>,
    /// Actual non-equality sorts without structural family provenance.
    pub undescribed_sorts: Vec<String>,
}

/// Capture only the configured native environment, rejecting missing machine
/// descriptions rather than publishing an incomplete ambient contract.
pub(crate) fn configured_catalog(
    graph: &EGraph,
) -> Result<std::sync::Arc<pb::BuiltinCatalog>, String> {
    let catalog = graph.authoring_type_info().portable_builtin_catalog()?;
    let gaps = catalog
        .undescribed_primitives
        .into_iter()
        .chain(catalog.undescribed_families)
        .chain(catalog.undescribed_family_primitives)
        .chain(catalog.undescribed_sorts)
        .collect::<Vec<_>>();
    if !gaps.is_empty() {
        return Err(format!(
            "builtin catalog has undescribed native registrations: {}",
            gaps.join(", ")
        ));
    }
    Ok(std::sync::Arc::new(catalog.definitions))
}

fn export_pattern(pattern: &SortPattern, sorts: &mut Vec<pb::Sort>) -> Result<u32, String> {
    let kind = match pattern {
        SortPattern::Param(index) => {
            pb::sort::Kind::Var(u32::try_from(*index).map_err(|_| "too many parameters")?)
        }
        SortPattern::Eq(name) => pb::sort::Kind::Eq(name.clone()),
        SortPattern::Family { name, args } => pb::sort::Kind::Primitive(pb::PrimitiveSortRef {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| export_pattern(arg, sorts))
                .collect::<Result<_, _>>()?,
        }),
        SortPattern::Function { inputs, output } => pb::sort::Kind::Func(pb::FuncSort {
            params: inputs
                .iter()
                .map(|input| export_pattern(input, sorts))
                .collect::<Result<_, _>>()?,
            result: export_pattern(output, sorts)?,
        }),
    };
    if let Some(index) = sorts
        .iter()
        .position(|sort| sort.kind.as_ref() == Some(&kind))
    {
        return Ok(index as u32);
    }
    let index = u32::try_from(sorts.len()).map_err(|_| "too many signature sorts")?;
    sorts.push(pb::Sort {
        kind: Some(kind),
        ..Default::default()
    });
    Ok(index)
}

fn native_pattern(sorts: &[pb::Sort], index: u32, depth: usize) -> Result<SortPattern, String> {
    if depth >= 256 {
        return Err("cyclic or too-deep signature pattern".into());
    }
    Ok(
        match sorts
            .get(index as usize)
            .and_then(|sort| sort.kind.as_ref())
            .ok_or("missing signature sort")?
        {
            pb::sort::Kind::Var(index) => SortPattern::Param(*index as usize),
            pb::sort::Kind::Eq(name) => SortPattern::Eq(name.clone()),
            pb::sort::Kind::Primitive(family) => SortPattern::Family {
                name: family.name.clone(),
                args: family
                    .args
                    .iter()
                    .map(|i| native_pattern(sorts, *i, depth + 1))
                    .collect::<Result<_, _>>()?,
            },
            pb::sort::Kind::Func(function) => SortPattern::Function {
                inputs: function
                    .params
                    .iter()
                    .map(|i| native_pattern(sorts, *i, depth + 1))
                    .collect::<Result<_, _>>()?,
                output: Box::new(native_pattern(sorts, function.result, depth + 1)?),
            },
        },
    )
}

fn wire_description(
    program: &pb::BuiltinCatalog,
    primitive: &pb::Primitive,
) -> Result<BuiltinDescription, String> {
    let signature = primitive
        .signature
        .as_ref()
        .ok_or("missing builtin signature")?;
    let mut normalized_sorts = vec![];
    normalized_signature(program, primitive, &mut normalized_sorts)?;
    let referenced: HashSet<_> = normalized_sorts
        .iter()
        .filter_map(|sort| match sort.kind {
            Some(pb::sort::Kind::Var(index)) => Some(index),
            _ => None,
        })
        .collect();
    if referenced.len() != signature.type_param_count as usize {
        return Err("undetermined builtin type parameter".into());
    }
    let arguments = |args: &[pb::Arg]| {
        args.iter()
            .map(|arg| {
                Ok(Argument {
                    name: arg.name.clone(),
                    sort: native_pattern(&program.sorts, arg.sort, 0)?,
                })
            })
            .collect::<Result<Vec<_>, String>>()
    };
    let typing = BuiltinTyping::Signature(Signature {
        params: referenced
            .iter()
            .map(|_| TypeParameter {
                name: String::new(),
                equality: false,
            })
            .collect(),
        fixed: arguments(&signature.inputs)?,
        tail: arguments(&signature.varargs)?,
        output: native_pattern(
            &program.sorts,
            signature.output.ok_or("missing builtin result")?,
            0,
        )?,
    });
    // Aliases are presentation; the native checker compares the semantic scheme.
    Ok(BuiltinDescription {
        key: primitive.name.clone(),
        aliases: vec![format!("__wire_{}", primitive.name)],
        typing,
    })
}

/// Decode a fixture/provider description into the native semantic model.
/// Validation and installation remain explicit; helper records are not roots.
pub fn native_definition(program: &pb::BuiltinCatalog) -> Result<BuiltinDescription, String> {
    let key = definition_key(program)?;
    let primitive = definition_root(program, key)?;
    wire_description(program, primitive)
}

/// Project the native macro's closed signature, without reauthoring its types.
pub fn closed_signature(
    key: &str,
    alias: &str,
    inputs: &[(&str, ArcSort)],
    tail: &[(&str, ArcSort)],
    output: ArcSort,
) -> Result<pb::BuiltinCatalog, String> {
    project_description(&egglog::builtin::closed_signature(
        key, alias, inputs, tail, output,
    )?)
}

/// Project homogeneous native typing using the same registered type scheme.
pub fn homogeneous_signature(
    key: &str,
    alias: &str,
    inputs: &[&str],
    output: ArcSort,
) -> Result<pb::BuiltinCatalog, String> {
    project_description(&egglog::builtin::homogeneous_signature(
        key, alias, inputs, output,
    )?)
}

/// Native inference for one wire fixture's own canonical registration root.
pub fn type_constraints(
    definition: &pb::BuiltinCatalog,
    span: &Span,
) -> Box<dyn constraint::TypeConstraint> {
    let native = native_definition(definition).expect("valid native fixture description");
    egglog::builtin::rooted_type_constraints(&native.key, &native, span)
}

/// Project the native semantic scheme without frontend presentation.
pub fn project_description(description: &BuiltinDescription) -> Result<pb::BuiltinCatalog, String> {
    let mut catalog = pb::BuiltinCatalog::default();
    let primitive = project_primitive(description, &mut catalog.sorts)?;
    catalog.primitive_sorts = catalog
        .sorts
        .iter()
        .filter_map(|sort| match &sort.kind {
            Some(pb::sort::Kind::Primitive(primitive)) => {
                Some((primitive.name.clone(), primitive.args.len() as u32))
            }
            _ => None,
        })
        .collect::<std::collections::BTreeMap<_, _>>()
        .into_iter()
        .map(|(name, arity)| pb::PrimitiveSort {
            name,
            arity,
            ..Default::default()
        })
        .collect();
    catalog.primitives.push(primitive);
    Ok(catalog)
}

fn project_primitive(
    description: &BuiltinDescription,
    sorts: &mut Vec<pb::Sort>,
) -> Result<pb::Primitive, String> {
    description.validate()?;
    let BuiltinTyping::Signature(signature) = &description.typing else {
        return Err(
            "function construction/application is intrinsic, not a public primitive".into(),
        );
    };
    let mut arguments = |args: &[Argument]| {
        args.iter()
            .map(|arg| {
                Ok(pb::Arg {
                    name: arg.name.clone(),
                    sort: export_pattern(&arg.sort, sorts)?,
                })
            })
            .collect::<Result<Vec<_>, String>>()
    };
    let inputs = arguments(&signature.fixed)?;
    let varargs = arguments(&signature.tail)?;
    let output = export_pattern(&signature.output, sorts)?;
    Ok(pb::Primitive {
        name: description.key.clone(),
        signature: Some(pb::GenericSignature {
            type_param_count: u32::try_from(signature.params.len())
                .map_err(|_| "too many type parameters")?,
            inputs,
            varargs,
            output: Some(output),
        }),
        ..Default::default()
    })
}

/// Inert wire projection and validation against the actual native registry.
pub trait PortableTypeInfo {
    /// Export available native declarations and report every remaining gap.
    fn portable_builtin_catalog(&self) -> Result<PortableCatalog, String>;
    /// Project one actual native signature into an independently owned catalog.
    fn export_builtin_definition(
        &self,
        key: &str,
        destination: &mut pb::BuiltinCatalog,
    ) -> Result<(), String>;
    /// Check signature evidence against the actual registered provider.
    fn check_portable_builtin_signature(
        &self,
        program: &pb::BuiltinCatalog,
        primitive: &pb::Primitive,
    ) -> Result<(), String>;
    /// Project the exact target selected by native sorts and optional runtime IDs.
    fn export_function_target(
        &self,
        name: &str,
        inputs: &[ArcSort],
        output: &ArcSort,
        resolved: Option<&egglog::sort::ResolvedFunctionId>,
        destination: &mut pb::Program,
    ) -> Result<String, String>;
    /// Check closed wire annotations before selecting an existing native instance.
    fn resolve_portable_builtin(
        &self,
        program: &pb::Program,
        key: &str,
        arguments: &[u32],
        output: u32,
        native: &[ArcSort],
    ) -> Result<String, String>;
}

impl PortableTypeInfo for TypeInfo {
    fn resolve_portable_builtin(
        &self,
        program: &pb::Program,
        key: &str,
        arguments: &[u32],
        output: u32,
        native: &[ArcSort],
    ) -> Result<String, String> {
        if self.builtin_description(key).is_ok_and(|description| {
            matches!(
                description.typing,
                BuiltinTyping::FunctionApplication | BuiltinTyping::FunctionConstructor
            )
        }) {
            return Err("function application/construction requires its structural node".into());
        }
        if native.len() != arguments.len() + 1 {
            return Err("builtin native signature arity mismatch".into());
        }
        for (index, actual) in arguments.iter().copied().chain([output]).zip(native) {
            if native_pattern(&program.sorts, index, 0)? != self.native_sort_pattern(actual)? {
                return Err("native instance binding disagrees with wire sort".into());
            }
        }
        if self.builtin_description(key).is_err() {
            let matches = self
                .get_prims(key)
                .into_iter()
                .flatten()
                .filter(|primitive| {
                    let any: &dyn std::any::Any = &*primitive.primitive;
                    any.downcast_ref::<crate::primitive::DefinedPrimitive>()
                        .is_some_and(|defined| {
                            defined.input.len() + 1 == native.len()
                                && defined
                                    .input
                                    .iter()
                                    .chain([&defined.output])
                                    .zip(native)
                                    .all(|(expected, actual)| {
                                        std::sync::Arc::ptr_eq(expected, actual)
                                    })
                        })
                })
                .count();
            if matches == 1 {
                return Ok(key.to_owned());
            }
            return Err(format!(
                "computed primitive {key} has {matches} matching native instances"
            ));
        }
        let selected = self.resolve_builtin(key, native).map_err(|error| {
            if error == format!("unknown builtin description {key}") {
                format!("unknown builtin definition {key}")
            } else {
                error
            }
        })?;
        Ok(selected
            .primitive
            .builtin_instance()
            .map_or_else(|| key.to_owned(), |instance| instance.dispatch_name.clone()))
    }
    fn portable_builtin_catalog(&self) -> Result<PortableCatalog, String> {
        let native = self.builtin_catalog()?;
        let mut result = PortableCatalog {
            definitions: pb::BuiltinCatalog::default(),
            undescribed_primitives: Vec::new(),
            undescribed_families: native.undescribed_families,
            undescribed_family_primitives: native.undescribed_family_primitives,
            undescribed_sorts: native.undescribed_sorts,
        };
        for description in &native.descriptions {
            if description.key == "egglog.core.map.flat"
                || matches!(
                    description.typing,
                    BuiltinTyping::FunctionConstructor | BuiltinTyping::FunctionApplication
                )
            {
                continue;
            }
            result.definitions.primitives.push(project_primitive(
                description,
                &mut result.definitions.sorts,
            )?);
        }
        result.definitions.primitive_sorts = native
            .families
            .into_iter()
            .map(|family| {
                Ok(pb::PrimitiveSort {
                    name: family.name,
                    arity: u32::try_from(family.arity)
                        .map_err(|_| "family arity exceeds wire limits")?,
                    ..Default::default()
                })
            })
            .collect::<Result<_, String>>()?;
        for name in native.undescribed_primitives {
            let mut described = false;
            if let Some(primitives) = self.get_prims(&name) {
                for primitive in primitives {
                    let any: &dyn std::any::Any = &*primitive.primitive;
                    if let Some(defined) = any.downcast_ref::<crate::primitive::DefinedPrimitive>()
                    {
                        let inputs = defined
                            .input
                            .iter()
                            .enumerate()
                            .map(|(index, sort)| {
                                Ok(pb::Arg {
                                    name: format!("_{index}"),
                                    sort: export_pattern(
                                        &self.native_sort_pattern(sort)?,
                                        &mut result.definitions.sorts,
                                    )?,
                                })
                            })
                            .collect::<Result<_, String>>()?;
                        let output = export_pattern(
                            &self.native_sort_pattern(&defined.output)?,
                            &mut result.definitions.sorts,
                        )?;
                        let projected = pb::Primitive {
                            name: defined.name.clone(),
                            signature: Some(pb::GenericSignature {
                                inputs,
                                output: Some(output),
                                ..Default::default()
                            }),
                            ..Default::default()
                        };
                        if let Some(previous) = result
                            .definitions
                            .primitives
                            .iter()
                            .find(|old| old.name == projected.name)
                        {
                            let mut sorts = vec![];
                            if normalized_signature(&result.definitions, previous, &mut sorts)?
                                != normalized_signature(
                                    &result.definitions,
                                    &projected,
                                    &mut sorts,
                                )?
                            {
                                return Err("computed native contexts disagree on signature".into());
                            }
                        } else {
                            result.definitions.primitives.push(projected);
                        }
                        described = true;
                    }
                }
            }
            if !described {
                result.undescribed_primitives.push(name);
            }
        }
        Ok(result)
    }

    fn export_builtin_definition(
        &self,
        key: &str,
        destination: &mut pb::BuiltinCatalog,
    ) -> Result<(), String> {
        let description = self.builtin_description(key)?;
        let projected = project_description(description)?;
        import_definition(&projected, destination).map(|_| ())
    }

    fn check_portable_builtin_signature(
        &self,
        program: &pb::BuiltinCatalog,
        primitive: &pb::Primitive,
    ) -> Result<(), String> {
        let native = project_description(self.builtin_description(&primitive.name)?)?;
        let root = definition_root(&native, &primitive.name)?;
        let mut sorts = vec![];
        if normalized_signature(program, primitive, &mut sorts)?
            != normalized_signature(&native, root, &mut sorts)?
        {
            return Err("builtin signature differs from native signature".into());
        }
        Ok(())
    }

    fn export_function_target(
        &self,
        name: &str,
        inputs: &[ArcSort],
        output: &ArcSort,
        resolved: Option<&egglog::sort::ResolvedFunctionId>,
        destination: &mut pb::Program,
    ) -> Result<String, String> {
        let target = self.resolve_function_target(name, inputs, output, resolved)?;
        if matches!(&target, egglog::builtin::NativeFunctionTarget::Primitive(primitives) if primitives.iter().any(|primitive| primitive.primitive.builtin_description().is_some_and(|description| matches!(description.typing, BuiltinTyping::FunctionApplication))))
        {
            return application_adapter(self, inputs, output, destination);
        }
        export_target(self, target, destination)
    }
}

// A first-class native application operation has no public callable identity.
// Close its concrete signature in ordinary program code, so named partials and
// extracted values retain the same existing function-value representation.
fn application_adapter(
    types: &TypeInfo,
    inputs: &[ArcSort],
    output: &ArcSort,
    destination: &mut pb::Program,
) -> Result<String, String> {
    use std::fmt::Write;
    let mut name = String::from("__egglog_application_");
    for sort in inputs.iter().chain([output]) {
        write!(name, "{}_", sort.name().len()).unwrap();
        for byte in sort.name().bytes() {
            write!(name, "{byte:02x}").unwrap();
        }
    }
    let mut adapter = pb::Program::default();
    let mut arguments = vec![];
    let mut nodes = vec![];
    for (index, sort) in inputs.iter().enumerate() {
        let sort = export_pattern(&types.native_sort_pattern(sort)?, &mut adapter.sorts)?;
        arguments.push(pb::Arg {
            sort,
            name: format!("_{index}"),
        });
        let node =
            u32::try_from(adapter.nodes.len()).map_err(|_| "too many application adapter nodes")?;
        adapter.nodes.push(pb::Node {
            sort_id: sort,
            kind: Some(pb::node::Kind::Var(format!("_{index}"))),
            ..Default::default()
        });
        nodes.push(node);
    }
    let (function, args) = nodes
        .split_first()
        .ok_or("application adapter requires a function input")?;
    let output = export_pattern(&types.native_sort_pattern(output)?, &mut adapter.sorts)?;
    let body =
        u32::try_from(adapter.nodes.len()).map_err(|_| "too many application adapter nodes")?;
    adapter.nodes.push(pb::Node {
        sort_id: output,
        kind: Some(pb::node::Kind::Apply(pb::Apply {
            function: Some(*function),
            args: args.to_vec(),
        })),
        ..Default::default()
    });
    adapter.declarations.push(pb::Declaration {
        kind: Some(pb::declaration::Kind::UserDefinedPrimitive(
            pb::UserDefinedPrimitive {
                name: name.clone(),
                inputs: arguments,
                output,
                body: Some(body),
            },
        )),
        ..Default::default()
    });
    definitions::reconcile_declarations(&adapter, destination)?;
    Ok(name)
}

fn export_target(
    _types: &TypeInfo,
    target: egglog::builtin::NativeFunctionTarget,
    _destination: &mut pb::Program,
) -> Result<String, String> {
    match target {
        egglog::builtin::NativeFunctionTarget::Function(name) => Ok(name),
        egglog::builtin::NativeFunctionTarget::Primitive(primitives) => {
            let mut selected = None;
            for primitive in primitives {
                let description = primitive.primitive.builtin_description();
                if description.is_some_and(|description| {
                    matches!(description.typing, BuiltinTyping::FunctionApplication)
                }) {
                    return Err(
                        "native application function value requires a program-defined adapter"
                            .into(),
                    );
                }
                let any: &dyn std::any::Any = &*primitive.primitive;
                let key = if let Some(defined) =
                    any.downcast_ref::<crate::primitive::DefinedPrimitive>()
                {
                    defined.name.clone()
                } else {
                    description
                        .ok_or("function target has no native description")?
                        .key
                        .clone()
                };
                if selected.as_ref().is_some_and(|old| old != &key) {
                    return Err(
                        "function target contexts have different canonical identities".into(),
                    );
                }
                selected = Some(key);
            }
            selected.ok_or("function target has no context".into())
        }
    }
}

/// Wire projection retaining the graph's native authoring environment.
pub trait PortableEGraph {
    /// Project actual sort provenance, including nominal equality sorts.
    fn export_sort(&self, sort: &ArcSort, destination: &mut Vec<pb::Sort>) -> Result<u32, String>;
    /// Recover a function value's exact target and captured input sorts.
    fn export_function_value_target(&self, sort: &ArcSort, value: Value) -> Result<String, String>;
    /// Select the native implementation for one fully annotated wire call.
    fn resolve_builtin_call(
        &self,
        program: &pb::Program,
        name: &str,
        arguments: &[u32],
        output: u32,
        native_sort_names: &[&str],
    ) -> Result<String, String>;
}

impl PortableEGraph for EGraph {
    fn export_sort(&self, sort: &ArcSort, destination: &mut Vec<pb::Sort>) -> Result<u32, String> {
        export_pattern(
            &self.authoring_type_info().native_sort_pattern(sort)?,
            destination,
        )
    }
    fn export_function_value_target(&self, sort: &ArcSort, value: Value) -> Result<String, String> {
        export_target(
            self.authoring_type_info(),
            self.resolve_function_value_target(sort, value)?,
            &mut pb::Program::default(),
        )
    }
    fn resolve_builtin_call(
        &self,
        program: &pb::Program,
        name: &str,
        arguments: &[u32],
        output: u32,
        native_sort_names: &[&str],
    ) -> Result<String, String> {
        let types = self.authoring_type_info();
        let native = native_sort_names
            .iter()
            .map(|name| {
                types
                    .get_sort_by_name(name)
                    .cloned()
                    .ok_or_else(|| format!("unknown authoring sort {name}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        types.resolve_portable_builtin(program, name, arguments, output, &native)
    }
}

/// Project one already selected native primitive without alias redispatch.
pub trait PortablePrimitive {
    /// Import the selected declaration or its retained authored computation.
    fn export_builtin(&self, destination: &mut pb::Program) -> Result<String, String>;
    /// Project a call or structural source facade after checking actual sorts.
    fn export_builtin_node(
        &self,
        graph: &EGraph,
        args: &[u32],
        span: Option<pb::Span>,
        destination: &mut pb::Program,
    ) -> Result<pb::node::Kind, String>;
    /// Project a table call, rejecting source facades that produce values.
    fn export_builtin_call(
        &self,
        graph: &EGraph,
        args: &[u32],
        span: Option<pb::Span>,
        destination: &mut pb::Program,
    ) -> Result<pb::Call, String>;
}

impl PortablePrimitive for SpecializedPrimitive {
    fn export_builtin(&self, _destination: &mut pb::Program) -> Result<String, String> {
        let any: &dyn std::any::Any = &*self.prim_with_id.primitive;
        if let Some(defined) = any.downcast_ref::<crate::primitive::DefinedPrimitive>() {
            return Ok(defined.name.clone());
        }
        let description = self
            .prim_with_id
            .primitive
            .builtin_description()
            .ok_or_else(|| format!("primitive {} has no native description", self.name()))?;
        if description.key == "egglog.core.map.flat"
            || matches!(
                description.typing,
                BuiltinTyping::FunctionConstructor | BuiltinTyping::FunctionApplication
            )
        {
            return Err("source facade requires structural call projection".into());
        }
        description.validate()?;
        Ok(description.key.clone())
    }
    fn export_builtin_node(
        &self,
        graph: &EGraph,
        args: &[u32],
        span: Option<pb::Span>,
        destination: &mut pb::Program,
    ) -> Result<pb::node::Kind, String> {
        let types = graph.authoring_type_info();
        if args.len() != self.input().len() {
            return Err("resolved builtin call arity mismatch".into());
        }
        for (arg, sort) in args.iter().zip(self.input()) {
            let node = destination
                .nodes
                .get(*arg as usize)
                .ok_or("builtin argument out of bounds")?;
            if native_pattern(&destination.sorts, node.sort_id, 0)?
                != types.native_sort_pattern(sort)?
            {
                return Err("builtin argument annotation differs from resolved sort".into());
            }
        }
        let description = self.prim_with_id.primitive.builtin_description();
        if description.is_some_and(|d| matches!(d.typing, BuiltinTyping::FunctionApplication)) {
            let (function, args) = args
                .split_first()
                .ok_or("native application requires a function")?;
            return Ok(pb::node::Kind::Apply(pb::Apply {
                function: Some(*function),
                args: args.to_vec(),
            }));
        }
        if description.is_some_and(|d| matches!(d.typing, BuiltinTyping::FunctionConstructor)) {
            let function = self
                .output()
                .clone()
                .as_arc_any()
                .downcast::<egglog::sort::FunctionSort>()
                .map_err(|_| "partial call requires native function sort")?;
            let Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::String(name)),
            })) = destination
                .nodes
                .get(args[0] as usize)
                .and_then(|n| n.kind.as_ref())
            else {
                return Err("function constructor target must be a literal string".into());
            };
            let name = name.clone();
            let inputs = self.input()[1..]
                .iter()
                .chain(function.inputs())
                .cloned()
                .collect::<Vec<_>>();
            let func = types.export_function_target(
                &name,
                &inputs,
                &function.output(),
                None,
                destination,
            )?;
            return Ok(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                value: Some(pb::primitive_value::Value::PartialCall(pb::Call {
                    func,
                    args: args[1..].to_vec(),
                })),
            }));
        }
        if description.is_some_and(|d| d.key == "egglog.core.map.flat") {
            // Reject conflicting native authority before extending value arenas.
            types
                .builtin_description("egglog.core.map.of")?
                .validate()?;
            let SortPattern::Family {
                args: parameters, ..
            } = types.native_sort_pattern(self.output())?
            else {
                return Err("flat Map requires a Map output".into());
            };
            let pair = SortPattern::Family {
                name: "Pair".into(),
                args: parameters,
            };
            let pair_sort = export_pattern(&pair, &mut destination.sorts)?;
            let vector_sort = export_pattern(
                &SortPattern::Family {
                    name: "Vec".into(),
                    args: vec![pair],
                },
                &mut destination.sorts,
            )?;
            let mut items = Vec::new();
            for children in args.chunks_exact(2) {
                let index = destination.nodes.len() as u32;
                destination.nodes.push(pb::Node {
                    sort_id: pair_sort,
                    span,
                    kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                        value: Some(pb::primitive_value::Value::Pair(pb::PairValue {
                            first: Some(children[0]),
                            second: Some(children[1]),
                        })),
                    })),
                });
                items.push(index);
            }
            let vector = destination.nodes.len() as u32;
            destination.nodes.push(pb::Node {
                sort_id: vector_sort,
                span,
                kind: Some(pb::node::Kind::PrimitiveValue(pb::PrimitiveValue {
                    value: Some(pb::primitive_value::Value::Vec(pb::ValueList { items })),
                })),
            });
            return Ok(pb::node::Kind::Call(pb::Call {
                func: "egglog.core.map.of".into(),
                args: vec![vector],
            }));
        }
        let func = self.export_builtin(destination)?;
        Ok(pb::node::Kind::Call(pb::Call {
            func,
            args: args.to_vec(),
        }))
    }
    fn export_builtin_call(
        &self,
        graph: &EGraph,
        args: &[u32],
        span: Option<pb::Span>,
        destination: &mut pb::Program,
    ) -> Result<pb::Call, String> {
        match self.export_builtin_node(graph, args, span, destination)? {
            pb::node::Kind::Call(call) => Ok(call),
            _ => Err("resolved primitive produces a structured value, not a table call".into()),
        }
    }
}

/// Relocate a finite structural pattern, retaining open binders for use checks.
pub fn import_sort(
    source: &[pb::Sort],
    index: u32,
    destination: &mut Vec<pb::Sort>,
) -> Result<u32, String> {
    fn visit(
        source: &[pb::Sort],
        index: u32,
        destination: &mut Vec<pb::Sort>,
        active: &mut HashSet<u32>,
        cache: &mut HashMap<u32, u32>,
    ) -> Result<u32, String> {
        if let Some(index) = cache.get(&index) {
            return Ok(*index);
        }
        if active.len() >= 256 || !active.insert(index) {
            return Err("cyclic or too-deep sort pattern".into());
        }
        let mut sort = source
            .get(index as usize)
            .ok_or("sort index out of bounds")?
            .clone();
        match sort.kind.as_mut().ok_or("missing sort kind")? {
            pb::sort::Kind::Primitive(family) => {
                if family.name.is_empty() {
                    return Err("empty host family name".into());
                }
                for child in &mut family.args {
                    *child = visit(source, *child, destination, active, cache)?;
                }
            }
            pb::sort::Kind::Func(function) => {
                for child in &mut function.params {
                    *child = visit(source, *child, destination, active, cache)?;
                }
                function.result = visit(source, function.result, destination, active, cache)?;
            }
            pb::sort::Kind::Eq(name) if !name.is_empty() => (),
            pb::sort::Kind::Var(_) => (),
            _ => return Err("unsupported builtin sort pattern".into()),
        }
        active.remove(&index);
        if let Some(existing) = destination
            .iter()
            .position(|existing| existing.kind == sort.kind)
        {
            cache.insert(index, existing as u32);
            return Ok(existing as u32);
        }
        let imported = u32::try_from(destination.len()).map_err(|_| "too many sorts")?;
        destination.push(sort);
        cache.insert(index, imported);
        Ok(imported)
    }
    visit(
        source,
        index,
        destination,
        &mut HashSet::default(),
        &mut HashMap::default(),
    )
}

pub(crate) fn normalized_signature(
    program: &pb::BuiltinCatalog,
    primitive: &pb::Primitive,
    sorts: &mut Vec<pb::Sort>,
) -> Result<pb::GenericSignature, String> {
    if primitive.name.is_empty() {
        return Err("builtin definition key must not be empty".into());
    }
    let mut signature = primitive
        .signature
        .clone()
        .ok_or("missing builtin signature")?;
    let output = signature
        .output
        .as_mut()
        .ok_or("missing builtin result sort")?;
    *output = import_sort(&program.sorts, *output, sorts)?;
    for arg in signature
        .inputs
        .iter_mut()
        .chain(signature.varargs.iter_mut())
    {
        arg.name.clear();
        arg.sort = import_sort(&program.sorts, arg.sort, sorts)?;
    }
    let mut pending: Vec<_> = signature
        .inputs
        .iter()
        .map(|a| a.sort)
        .chain(signature.varargs.iter().map(|a| a.sort))
        .chain(signature.output)
        .collect();
    let mut seen = HashSet::default();
    while let Some(index) = pending.pop() {
        if !seen.insert(index) {
            continue;
        }
        match sorts[index as usize].kind.as_ref().unwrap() {
            pb::sort::Kind::Var(index) if *index >= signature.type_param_count => {
                return Err("unbound builtin type parameter".into());
            }
            pb::sort::Kind::Primitive(family) => pending.extend(&family.args),
            pb::sort::Kind::Func(function) => {
                pending.extend(&function.params);
                pending.push(function.result);
            }
            _ => (),
        }
    }
    Ok(signature)
}

fn definition_root<'a>(
    catalog: &'a pb::BuiltinCatalog,
    key: &str,
) -> Result<&'a pb::Primitive, String> {
    if key.is_empty() {
        return Err("empty builtin root identity".into());
    }
    let mut roots = catalog
        .primitives
        .iter()
        .filter(|primitive| primitive.name == key);
    let root = roots.next().ok_or("missing builtin root definition")?;
    if roots.next().is_some() {
        return Err("duplicate builtin root definition".into());
    }
    Ok(root)
}

pub(crate) fn definition_key(catalog: &pb::BuiltinCatalog) -> Result<&str, String> {
    let [primitive] = catalog.primitives.as_slice() else {
        return Err("expected exactly one builtin definition".into());
    };
    normalized_signature(catalog, primitive, &mut vec![])?;
    Ok(&primitive.name)
}

/// Import an independently owned signature proof, rejecting conflicting native
/// identities and relocating only its referenced catalog sorts.
pub fn import_definition(
    source: &pb::BuiltinCatalog,
    destination: &mut pb::BuiltinCatalog,
) -> Result<String, String> {
    let key = definition_key(source)?.to_owned();
    let primitive = definition_root(source, &key)?;
    if let Some(previous) = destination.primitives.iter().find(|old| old.name == key) {
        let mut sorts = vec![];
        if normalized_signature(source, primitive, &mut sorts)?
            != normalized_signature(destination, previous, &mut sorts)?
        {
            return Err("conflicting builtin signature".into());
        }
        return Ok(key);
    }
    let mut primitive = primitive.clone();
    if let Some(signature) = &mut primitive.signature {
        for argument in signature
            .inputs
            .iter_mut()
            .chain(signature.varargs.iter_mut())
        {
            argument.sort = import_sort(&source.sorts, argument.sort, &mut destination.sorts)?;
        }
        let result = signature
            .output
            .as_mut()
            .ok_or("missing signature result")?;
        *result = import_sort(&source.sorts, *result, &mut destination.sorts)?;
    }
    for family in &source.primitive_sorts {
        if let Some(previous) = destination
            .primitive_sorts
            .iter()
            .find(|old| old.name == family.name)
        {
            if previous.arity != family.arity {
                return Err("conflicting primitive sort arity".into());
            }
        } else {
            destination.primitive_sorts.push(family.clone());
        }
    }
    // Generated proof fragments normally omit origins; preserve them when present.
    let offset =
        u32::try_from(destination.files.len()).map_err(|_| "too many builtin source files")?;
    if let Some(span) = &mut primitive.span {
        span.file = span
            .file
            .checked_add(offset)
            .ok_or("too many builtin source files")?;
    }
    destination.files.extend(source.files.iter().cloned());
    destination.primitives.push(primitive);
    Ok(key)
}
