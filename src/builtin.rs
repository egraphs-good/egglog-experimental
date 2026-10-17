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
use prost::Message;
use std::sync::{Arc, LazyLock};
pub mod definitions;
/// Resolve the concrete scalar endpoints of a portable signature.
pub fn signature_sorts(
    program: &pb::Program,
    primitive: &pb::HostPrimitive,
) -> Result<Vec<String>, String> {
    let Some(pb::host_primitive::Typing::Signature(signature)) = &primitive.typing else {
        return Err("function-application builtin typing is not implemented yet".into());
    };
    if primitive.name.is_empty() || !signature.type_params.is_empty() {
        return Err("builtin typing currently requires a named closed signature".into());
    }
    signature.inputs.iter().chain(&signature.varargs).map(|arg| arg.sort).chain(std::iter::once(signature.output.ok_or("missing builtin result sort")?)).map(|index| {
        let sort = program.sorts.get(index as usize).ok_or("builtin signature sort index out of bounds")?;
        match &sort.kind {
            Some(pb::sort::Kind::Family(family)) if family.args.is_empty() && !family.name.is_empty() => Ok(family.name.clone()),
            _ => Err("builtin signature requires a symbolic-family compiler beyond this scalar slice".into()),
        }
    }).collect()
}
pub mod registration;
pub use registration::{PortableRegistration, add_pure_with_definition};

/// Portable declarations plus explicit native provider inventory gaps.
pub struct PortableCatalog {
    /// Portable signatures and authored computations projected from native owners.
    pub definitions: pb::Program,
    /// Actual callable registrations without a portable projection.
    pub undescribed_primitives: Vec<String>,
    /// Actual family factories without a native description.
    pub undescribed_families: Vec<String>,
    /// Reserved native family operations without a description.
    pub undescribed_family_primitives: Vec<String>,
    /// Actual non-equality sorts without structural family provenance.
    pub undescribed_sorts: Vec<String>,
}

static LANGUAGE_METADATA: LazyLock<pb::Program> = LazyLock::new(|| {
    let bytes: &[u8] = include!("builtin/metadata.rs");
    pb::Program::decode(bytes).expect("valid presentation metadata")
});

fn export_pattern(pattern: &SortPattern, sorts: &mut Vec<pb::Sort>) -> Result<u32, String> {
    let kind = match pattern {
        SortPattern::Param(index) => {
            pb::sort::Kind::Var(u32::try_from(*index).map_err(|_| "too many parameters")?)
        }
        SortPattern::Eq(name) => pb::sort::Kind::Eq(name.clone()),
        SortPattern::Family { name, args } => pb::sort::Kind::Family(pb::HostSort {
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
            pb::sort::Kind::Family(family) => SortPattern::Family {
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
    program: &pb::Program,
    primitive: &pb::HostPrimitive,
) -> Result<BuiltinDescription, String> {
    let typing = match primitive
        .typing
        .as_ref()
        .ok_or("missing builtin typing form")?
    {
        pb::host_primitive::Typing::Application(_) => BuiltinTyping::FunctionApplication,
        pb::host_primitive::Typing::Signature(signature) => {
            if signature
                .equality_type_params
                .windows(2)
                .any(|w| w[0] >= w[1])
                || signature
                    .equality_type_params
                    .iter()
                    .any(|i| *i as usize >= signature.type_params.len())
            {
                return Err("invalid equality type parameter indices".into());
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
            BuiltinTyping::Signature(Signature {
                params: signature
                    .type_params
                    .iter()
                    .enumerate()
                    .map(|(i, name)| TypeParameter {
                        name: name.clone(),
                        equality: signature.equality_type_params.contains(&(i as u32)),
                    })
                    .collect(),
                fixed: arguments(&signature.inputs)?,
                tail: arguments(&signature.varargs)?,
                output: native_pattern(
                    &program.sorts,
                    signature.output.ok_or("missing builtin result")?,
                    0,
                )?,
            })
        }
    };
    // Aliases are presentation; the native checker compares the semantic scheme.
    Ok(BuiltinDescription {
        key: primitive.name.clone(),
        aliases: vec![format!("__wire_{}", primitive.name)],
        typing,
    })
}

/// Decode a fixture/provider description into the native semantic model.
/// Validation and installation remain explicit; helper records are not roots.
pub fn native_definition(program: &pb::Program) -> Result<BuiltinDescription, String> {
    let key = definition_key(program)?;
    let (declaration, primitive) = definition_root(program, key)?;
    let mut description = wire_description(program, primitive)?;
    if let Some(egglog) = declaration
        .bindings
        .as_ref()
        .and_then(|bindings| bindings.egglog.as_ref())
    {
        description.aliases = egglog
            .views
            .iter()
            .map(|view| view.symbol.clone())
            .collect();
    }
    Ok(description)
}

/// Project the native macro's closed signature, without reauthoring its types.
pub fn closed_signature(
    key: &str,
    alias: &str,
    inputs: &[(&str, ArcSort)],
    tail: &[(&str, ArcSort)],
    output: ArcSort,
) -> Result<pb::Program, String> {
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
) -> Result<pb::Program, String> {
    project_description(&egglog::builtin::homogeneous_signature(
        key, alias, inputs, output,
    )?)
}

/// Native inference for one wire fixture's own canonical registration root.
pub fn type_constraints(
    definition: &pb::Program,
    span: &Span,
) -> Box<dyn constraint::TypeConstraint> {
    let native = native_definition(definition).expect("valid native fixture description");
    egglog::builtin::rooted_type_constraints(&native.key, &native, span)
}

/// Project a native scheme and attach Experimental-owned language views.
pub fn project_description(description: &BuiltinDescription) -> Result<pb::Program, String> {
    description.validate()?;
    let mut program = pb::Program {
        ir_version: 1,
        ..Default::default()
    };
    let typing = match &description.typing {
        BuiltinTyping::FunctionApplication => {
            pb::host_primitive::Typing::Application(pb::FunctionApplication {})
        }
        BuiltinTyping::FunctionConstructor => {
            return Err(
                "function construction projects to PartialCall, not a host callable".into(),
            );
        }
        BuiltinTyping::Signature(signature) => {
            let mut arguments = |args: &[Argument]| {
                args.iter()
                    .map(|arg| {
                        Ok(pb::Arg {
                            name: arg.name.clone(),
                            sort: export_pattern(&arg.sort, &mut program.sorts)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()
            };
            let inputs = arguments(&signature.fixed)?;
            let varargs = arguments(&signature.tail)?;
            let output = export_pattern(&signature.output, &mut program.sorts)?;
            pb::host_primitive::Typing::Signature(pb::GenericSignature {
                type_params: signature.params.iter().map(|p| p.name.clone()).collect(),
                inputs,
                varargs,
                output: Some(output),
                equality_type_params: signature
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(i, p)| p.equality.then_some(i as u32))
                    .collect(),
            })
        }
    };
    let bindings = Some(pb::CallableBindings {
        egglog: Some(pb::EgglogBindings {
            views: description
                .aliases
                .iter()
                .map(|symbol| pb::EgglogCallable {
                    symbol: symbol.clone(),
                    datatype_member: false,
                })
                .collect(),
        }),
        ..Default::default()
    });
    let root = pb::Declaration {
        kind: Some(pb::declaration::Kind::HostPrimitive(pb::HostPrimitive {
            name: description.key.clone(),
            typing: Some(typing),
        })),
        bindings,
        ..Default::default()
    };
    let families = program
        .sorts
        .iter()
        .filter_map(|sort| match &sort.kind {
            Some(pb::sort::Kind::Family(family)) => {
                Some((family.name.clone(), family.args.len() as u32))
            }
            _ => None,
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    for (name, arity) in families {
        program.declarations.push(pb::Declaration {
            kind: Some(pb::declaration::Kind::HostSortFamily(pb::HostSortFamily {
                name,
                arity,
                ..Default::default()
            })),
            ..Default::default()
        });
    }
    program.declarations.push(root);
    apply_language_metadata(&mut program, &LANGUAGE_METADATA, &description.key)?;
    Ok(program)
}

fn apply_language_metadata(
    program: &mut pb::Program,
    metadata: &pb::Program,
    key: &str,
) -> Result<(), String> {
    // A signature-only custom registration does not author family presentation.
    // Its TypeInfo export later supplies the actual registered family records.
    if !metadata.declarations.iter().any(|declaration| {
        matches!(&declaration.kind,
        Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == key)
    }) {
        return Ok(());
    }
    let mut decorated = program.clone();
    for declaration in &mut decorated.declarations {
        match &mut declaration.kind {
            Some(pb::declaration::Kind::HostSortFamily(family)) => {
                family.bindings = metadata.declarations.iter().find_map(|d| match &d.kind { Some(pb::declaration::Kind::HostSortFamily(m)) if m.name == family.name => m.bindings.clone(), _ => None });
            }
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == key => {
                if let Some(source) = metadata.declarations.iter().find(|d| matches!(&d.kind, Some(pb::declaration::Kind::HostPrimitive(p)) if p.name == key)) {
                    let mut bindings = source.bindings.clone().unwrap_or_default();
                    let mut import = |index: u32| import_sort(&metadata.sorts, index, &mut program.sorts);
                    if let Some(python) = &mut bindings.python { for view in &mut python.views { if let Some(pb::binding_owner::Kind::Sort(index)) = view.owner.as_mut().and_then(|owner| owner.kind.as_mut()) { *index = import(*index)?; } } }
                    if let Some(rust) = &mut bindings.rust { for view in &mut rust.views {
                        if let Some(pb::binding_owner::Kind::Sort(index)) = view.owner.as_mut().and_then(|owner| owner.kind.as_mut()) { *index = import(*index)?; }
                        if let Some(trait_impl) = &mut view.trait_impl { for argument in &mut trait_impl.args { if let Some(index) = &mut argument.sort { *index = import(*index)?; } } }
                    } }
                    bindings.egglog = declaration.bindings.as_ref().and_then(|b| b.egglog.clone());
                    declaration.bindings = Some(bindings);
                }
            }
            _ => (),
        }
    }
    decorated.sorts = program.sorts.clone();
    *program = decorated;
    Ok(())
}

/// Inert wire projection and validation against the actual native registry.
pub trait PortableTypeInfo {
    /// Export available native declarations and report every remaining gap.
    fn portable_builtin_catalog(&self) -> Result<PortableCatalog, String>;
    /// Import one actual native owner and its language/default context.
    fn export_builtin_definition(
        &self,
        key: &str,
        destination: &mut pb::Program,
    ) -> Result<(), String>;
    /// Check a submitted signature without replacing native authority.
    fn check_portable_builtin_signature(
        &self,
        program: &pb::Program,
        primitive: &pb::HostPrimitive,
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

fn primitive_definition(
    primitive: &dyn Primitive,
    destination: &mut pb::Program,
) -> Result<Option<String>, String> {
    let any: &dyn std::any::Any = primitive;
    if let Some(defined) = any.downcast_ref::<crate::primitive::DefinedPrimitive>() {
        let definition = defined.definition.as_ref().map_err(Clone::clone)?;
        definitions::reconcile_declarations(definition, destination)?;
        return Ok(Some(defined.name.clone()));
    }
    Ok(None)
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
        if native.len() != arguments.len() + 1 {
            return Err("builtin native signature arity mismatch".into());
        }
        for (index, actual) in arguments.iter().copied().chain([output]).zip(native) {
            if native_pattern(&program.sorts, index, 0)? != self.native_sort_pattern(actual)? {
                return Err("native instance binding disagrees with wire sort".into());
            }
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
            definitions: pb::Program {
                ir_version: 1,
                ..Default::default()
            },
            undescribed_primitives: native.undescribed_primitives,
            undescribed_families: native.undescribed_families,
            undescribed_family_primitives: native.undescribed_family_primitives,
            undescribed_sorts: native.undescribed_sorts,
        };
        for description in &native.descriptions {
            if description.key == "egglog.core.map.flat"
                || matches!(description.typing, BuiltinTyping::FunctionConstructor)
            {
                continue;
            }
            self.export_builtin_definition(&description.key, &mut result.definitions)?;
        }
        for family in native.families {
            let family = registration::family_metadata(self, &family)?;
            definitions::reconcile_declarations(
                &pb::Program {
                    ir_version: 1,
                    declarations: vec![pb::Declaration {
                        kind: Some(pb::declaration::Kind::HostSortFamily(family)),
                        ..Default::default()
                    }],
                    ..Default::default()
                },
                &mut result.definitions,
            )?;
        }
        let mut gaps = Vec::new();
        for name in result.undescribed_primitives {
            let mut authored = false;
            if let Some(primitives) = self.get_prims(&name) {
                for primitive in primitives {
                    authored |=
                        primitive_definition(&*primitive.primitive, &mut result.definitions)?
                            .is_some();
                }
            }
            if !authored {
                gaps.push(name);
            }
        }
        result.undescribed_primitives = gaps;
        Ok(result)
    }

    fn export_builtin_definition(
        &self,
        key: &str,
        destination: &mut pb::Program,
    ) -> Result<(), String> {
        let description = self.builtin_description(key)?;
        let mut projected = project_description(description)?;
        for declaration in &mut projected.declarations {
            if let Some(pb::declaration::Kind::HostSortFamily(family)) = &mut declaration.kind {
                *family = registration::family_metadata(
                    self,
                    &FamilyDescription {
                        name: family.name.clone(),
                        arity: family.arity as usize,
                    },
                )?;
            }
        }
        let metadata = self
            .extension_state::<registration::PortableMetadata>()
            .and_then(|metadata| metadata.primitives.get(key))
            .filter(|(owner, _)| std::ptr::eq(owner.as_ref(), description))
            .map(|(_, metadata)| metadata.clone());
        if let Some(metadata) = metadata {
            definitions::reconcile_declarations(&metadata, &mut projected)?;
        }
        definitions::reconcile_declarations(&projected, destination).map(|_| ())
    }

    fn check_portable_builtin_signature(
        &self,
        program: &pb::Program,
        primitive: &pb::HostPrimitive,
    ) -> Result<(), String> {
        self.check_builtin_signature(&wire_description(program, primitive)?)
    }

    fn export_function_target(
        &self,
        name: &str,
        inputs: &[ArcSort],
        output: &ArcSort,
        resolved: Option<&egglog::sort::ResolvedFunctionId>,
        destination: &mut pb::Program,
    ) -> Result<String, String> {
        export_target(
            self,
            self.resolve_function_target(name, inputs, output, resolved)?,
            destination,
        )
    }
}

fn export_target(
    types: &TypeInfo,
    target: egglog::builtin::NativeFunctionTarget,
    destination: &mut pb::Program,
) -> Result<String, String> {
    match target {
        egglog::builtin::NativeFunctionTarget::Function(name) => Ok(name),
        egglog::builtin::NativeFunctionTarget::Primitive(primitives) => {
            let mut selected = None;
            for primitive in primitives {
                let key =
                    if let Some(key) = primitive_definition(&*primitive.primitive, destination)? {
                        key
                    } else {
                        let description = primitive
                            .primitive
                            .builtin_description()
                            .ok_or("function target has no native description")?;
                        types.export_builtin_definition(&description.key, destination)?;
                        description.key.clone()
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
    fn export_builtin(&self, destination: &mut pb::Program) -> Result<String, String> {
        if let Some(key) = primitive_definition(&*self.prim_with_id.primitive, destination)? {
            return Ok(key);
        }
        let description = self
            .prim_with_id
            .primitive
            .builtin_description()
            .ok_or_else(|| format!("primitive {} has no native description", self.name()))?;
        if description.key == "egglog.core.map.flat"
            || matches!(description.typing, BuiltinTyping::FunctionConstructor)
        {
            return Err("source facade requires structural call projection".into());
        }
        definitions::reconcile_declarations(&project_description(description)?, destination)?;
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
            types.export_builtin_definition("egglog.core.map.of", destination)?;
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
        if description.is_some() {
            types.export_builtin_definition(&func, destination)?;
        }
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
            pb::sort::Kind::Family(family) => {
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
            for alias in sort.egglog_aliases {
                if !destination[existing].egglog_aliases.contains(&alias) {
                    destination[existing].egglog_aliases.push(alias);
                }
            }
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
    program: &pb::Program,
    primitive: &pb::HostPrimitive,
    sorts: &mut Vec<pb::Sort>,
) -> Result<pb::host_primitive::Typing, String> {
    if primitive.name.is_empty() {
        return Err("builtin definition key must not be empty".into());
    }
    let signature = match &primitive.typing {
        Some(pb::host_primitive::Typing::Signature(signature)) => signature,
        Some(typing @ pb::host_primitive::Typing::Application(_)) => return Ok(typing.clone()),
        None => return Err("missing builtin typing form".into()),
    };
    let mut signature = signature.clone();
    if signature
        .equality_type_params
        .windows(2)
        .any(|w| w[0] >= w[1])
        || signature
            .equality_type_params
            .iter()
            .any(|i| *i as usize >= signature.type_params.len())
    {
        return Err("invalid equality type parameter indices".into());
    }
    for label in &mut signature.type_params {
        label.clear();
    }
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
            pb::sort::Kind::Var(index) if (*index as usize) >= signature.type_params.len() => {
                return Err("unbound builtin type parameter".into());
            }
            pb::sort::Kind::Family(family) => pending.extend(&family.args),
            pb::sort::Kind::Func(function) => {
                pending.extend(&function.params);
                pending.push(function.result);
            }
            _ => (),
        }
    }
    Ok(pb::host_primitive::Typing::Signature(signature))
}

fn definition_root<'a>(
    program: &'a pb::Program,
    key: &str,
) -> Result<(&'a pb::Declaration, &'a pb::HostPrimitive), String> {
    if key.is_empty() {
        return Err("empty builtin root identity".into());
    }
    let mut roots = program
        .declarations
        .iter()
        .filter_map(|declaration| match &declaration.kind {
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if primitive.name == key => {
                Some((declaration, primitive))
            }
            _ => None,
        });
    let root = roots.next().ok_or("missing builtin root definition")?;
    if roots.next().is_some() {
        return Err("duplicate builtin root definition".into());
    }
    Ok(root)
}

pub(crate) fn definition_key(program: &pb::Program) -> Result<&str, String> {
    if program.ir_version != 1
        || !program.commands.is_empty()
        || !program.rules.is_empty()
        || !program.rulesets.is_empty()
    {
        return Err("builtin definition must contain only declaration templates".into());
    }
    let mut validated = vec![];
    for index in 0..program.sorts.len() {
        import_sort(&program.sorts, index as u32, &mut validated)?;
    }
    let mut key = None;
    for declaration in &program.declarations {
        match &declaration.kind {
            Some(pb::declaration::Kind::HostPrimitive(primitive)) if key.is_none() => {
                normalized_signature(program, primitive, &mut vec![])?;
                key = Some(primitive.name.as_str());
            }
            Some(pb::declaration::Kind::HostSortFamily(family)) if !family.name.is_empty() => {}
            _ => {
                return Err(
                    "expected exactly one builtin definition and family descriptors".into(),
                );
            }
        }
    }
    definitions::reconcile_declarations(program, &mut pb::Program::default())?;
    key.ok_or_else(|| "missing builtin definition".into())
}

/// Import one unambiguous host registration and its referenced closures.
pub fn import_definition(
    definition: &pb::Program,
    destination: &mut pb::Program,
) -> Result<String, String> {
    let key = definition_key(definition)?.to_owned();
    definitions::reconcile_declarations(definition, destination)?;
    Ok(key)
}

/// Import an explicit registration root without inferring it from record order.
pub fn import_rooted_definition(
    key: &str,
    definition: &pb::Program,
    destination: &mut pb::Program,
) -> Result<String, String> {
    let (_, primitive) = definition_root(definition, key)?;
    normalized_signature(definition, primitive, &mut vec![])?;
    definitions::check_builtin_context(definition, key, |_| Ok(definition.clone()))?;
    definitions::reconcile_declarations(definition, destination)?;
    Ok(key.into())
}

/// Supply scalar language views in the native signature's logical slot order.
pub fn scalar_member_bindings(
    signature: &pb::GenericSignature,
    python: &str,
    rust: &str,
    params: &[&str],
    rust_trait: Option<&str>,
    tail_repetitions: Option<u32>,
) -> pb::CallableBindings {
    assert!(signature.type_params.is_empty());
    let count = match tail_repetitions {
        Some(repetitions) => {
            assert!(!signature.varargs.is_empty());
            signature
                .inputs
                .len()
                .checked_add(
                    signature
                        .varargs
                        .len()
                        .checked_mul(repetitions as usize)
                        .unwrap(),
                )
                .unwrap()
        }
        None => {
            assert!(signature.varargs.is_empty());
            signature.inputs.len()
        }
    };
    assert_eq!(count, params.len() + 1);
    let inputs = signature
        .inputs
        .iter()
        .chain(signature.varargs.iter().cycle())
        .take(count)
        .collect::<Vec<_>>();
    let owner = Some(pb::BindingOwner {
        kind: Some(pb::binding_owner::Kind::Sort(inputs[0].sort)),
    });
    pb::CallableBindings {
        python: Some(pb::PythonBindings {
            views: vec![pb::PythonCallable {
                kind: pb::PythonCallKind::Method.into(),
                path: vec![python.into()],
                owner,
                receiver: Some(0),
                params: params
                    .iter()
                    .enumerate()
                    .map(|(index, name)| pb::PythonParameter {
                        core_input: Some(index as u32 + 1),
                        name: (*name).into(),
                        default_expr: None,
                    })
                    .collect(),
                tail_repetitions,
                ..Default::default()
            }],
        }),
        rust: Some(pb::RustBindings {
            views: vec![pb::RustCallable {
                path: vec![rust.into()],
                owner,
                receiver: Some(pb::RustReceiver {
                    core_input: Some(0),
                    borrowed: false,
                }),
                params: params
                    .iter()
                    .enumerate()
                    .map(|(index, name)| pb::RustParameter {
                        core_input: Some(index as u32 + 1),
                        name: if rust_trait.is_some() { "rhs" } else { name }.to_string(),
                        borrowed: false,
                    })
                    .collect(),
                trait_impl: rust_trait.map(|name| pb::RustTrait {
                    path: vec!["core".into(), "ops".into(), name.into()],
                    args: inputs[1..]
                        .iter()
                        .map(|arg| pb::RustType {
                            sort: Some(arg.sort),
                            borrowed: false,
                        })
                        .collect(),
                    output_associated_type: Some("Output".into()),
                }),
                tail_repetitions,
                ..Default::default()
            }],
        }),
        ..Default::default()
    }
}

#[cfg(test)]
mod projection_tests {
    use super::*;

    #[test]
    fn language_resource_contains_no_callable_signature_authority() {
        assert!(LANGUAGE_METADATA.nodes.is_empty());
        assert!(LANGUAGE_METADATA.commands.is_empty());
        assert!(LANGUAGE_METADATA.rules.is_empty());
        assert!(LANGUAGE_METADATA.rulesets.is_empty());
        for declaration in &LANGUAGE_METADATA.declarations {
            assert!(
                declaration
                    .bindings
                    .as_ref()
                    .is_none_or(|bindings| bindings.egglog.is_none())
            );
            match declaration.kind.as_ref().unwrap() {
                pb::declaration::Kind::HostPrimitive(primitive) => {
                    assert!(primitive.typing.is_none())
                }
                pb::declaration::Kind::HostSortFamily(family) => assert_eq!(family.arity, 0),
                _ => panic!("presentation resource contains a semantic declaration"),
            }
        }
    }
}
