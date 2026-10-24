//! Checked publication of a manual native primitive's semantic definition.

use super::*;

/// Check a manual primitive's semantic evidence before publishing its native owner.
/// The primitive's registered description remains the signature authority.
pub fn add_pure_with_definition<T: PurePrim + Clone>(
    graph: &mut EGraph,
    primitive: T,
    key: &str,
    definition: &pb::BuiltinCatalog,
    validator: Option<PrimitiveValidator>,
) -> Result<(), String> {
    let description = primitive
        .builtin_description()
        .ok_or("manual portable registration requires a native description")?;
    if description.key != key || definition_key(definition)? != key {
        return Err("manual builtin root identity mismatch".into());
    }
    let generated = project_description(description)?;
    let supplied = definition_root(definition, key)?;
    let native = definition_root(&generated, key)?;
    let mut sorts = vec![];
    if normalized_signature(definition, supplied, &mut sorts)?
        != normalized_signature(&generated, native, &mut sorts)?
    {
        return Err("manual builtin definition differs from native signature".into());
    }
    let families = graph.authoring_type_info().builtin_catalog()?.families;
    for family in &definition.primitive_sorts {
        if !families
            .iter()
            .any(|native| native.name == family.name && native.arity == family.arity as usize)
        {
            return Err(format!("unregistered builtin family {}", family.name));
        }
    }
    let mut staged = graph.clone();
    staged.add_pure_primitive(primitive, validator);
    staged.authoring_type_info().builtin_catalog()?;
    *graph = staged;
    Ok(())
}
