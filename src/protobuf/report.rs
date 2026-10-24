//! Backend diagnostics are opaque documents; semantic results live separately.

use super::pb;

pub(super) fn export(report: &egglog_reports::RunReport) -> Result<pb::Diagnostic, String> {
    let mut value = serde_json::to_value(report).map_err(|error| error.to_string())?;
    let object = value
        .as_object_mut()
        .expect("native report serializes as an object");
    object.remove("updated");
    object.remove("can_stop");
    Ok(pb::Diagnostic {
        format: "application/vnd.egglog.run-report+json".into(),
        content: serde_json::to_vec(&value).map_err(|error| error.to_string())?,
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
        content: serde_json::to_vec(&plans)
            .map_err(|error| egglog::Error::BackendError(error.to_string()))?,
    })
}
