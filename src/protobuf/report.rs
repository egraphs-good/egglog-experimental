//! Backend diagnostics are opaque documents; semantic results live separately.

use super::{RequestOccurrences, pb};

pub(super) fn rule_reference(
    name: &str,
    context: &mut RequestOccurrences,
    response: &mut pb::RunProgramResponse,
) -> Result<Option<u32>, String> {
    let Some(origin) = context.origins.get(name).cloned() else {
        return Ok(None);
    };
    if let Some(index) = context.response_rules.get(&origin) {
        return Ok(Some(*index));
    }
    let record = context
        .records
        .get(&origin)
        .ok_or("missing registered rule record")?;
    let index = u32::try_from(response.rules.len()).map_err(|_| "too many diagnostic rules")?;
    let mut program = pb::Program {
        nodes: std::mem::take(&mut response.nodes),
        sorts: std::mem::take(&mut response.sorts),
        files: std::mem::take(&mut response.files),
        rules: std::mem::take(&mut response.rules),
        ..Default::default()
    };
    let result = super::graph::append_rule(&mut program, record, &mut context.file_offsets);
    response.nodes = program.nodes;
    response.sorts = program.sorts;
    response.files = program.files;
    response.rules = program.rules;
    result?;
    context.response_rules.insert(origin, index);
    Ok(Some(index))
}

pub(super) fn export(report: &egglog_reports::RunReport) -> Result<pb::Diagnostic, String> {
    let mut value = serde_json::to_value(report).map_err(|error| error.to_string())?;
    let object = value
        .as_object_mut()
        .expect("native report serializes as an object");
    object.remove("updated");
    object.remove("can_stop");
    Ok(pb::Diagnostic {
        format: "application/vnd.egglog.run-report+json".into(),
        content: serde_json::to_string(&value).map_err(|error| error.to_string())?,
    })
}

pub(super) fn explain(
    graph: &egglog::EGraph,
    registry: &super::rules::Registry,
    groups: &[String],
) -> Result<pb::Diagnostic, egglog::Error> {
    let names = registry
        .ordered_union(groups)
        .into_iter()
        .map(|index| format!("{}_holder", registry.rules[index].candidate.name))
        .collect::<Vec<_>>();
    let plans = graph.explain_rulesets(&names)?;
    Ok(pb::Diagnostic {
        format: "application/vnd.egglog.query-plan+json".into(),
        content: serde_json::to_string(&plans)
            .map_err(|error| egglog::Error::BackendError(error.to_string()))?,
    })
}
