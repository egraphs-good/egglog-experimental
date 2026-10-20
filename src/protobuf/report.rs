//! Checked transport of the captured native report, without deriving aggregates.

use egglog_reports as native;

use super::{RequestOccurrences, pb};

// Intern the canonical occurrence, not each physical direction's name. Unknown
// native keys remain unclassified; they are not invented authored occurrences.
pub(super) fn rule_reference(
    name: &str,
    context: &mut RequestOccurrences,
    response: &mut pb::RunProgramResponse,
) -> Result<(Option<u32>, Option<i32>), String> {
    let Some((origin, direction)) = context.origins.get(name) else {
        return Ok((None, None));
    };
    let index = if let Some(index) = context.response_rules.get(origin) {
        *index
    } else {
        let index =
            u32::try_from(response.rules.len()).map_err(|_| "too many report occurrences")?;
        response.rules.push(origin.clone());
        context.response_rules.insert(origin.clone(), index);
        index
    };
    Ok((Some(index), Some((*direction).into())))
}

pub(super) fn export(
    report: &native::RunReport,
    selected: &[pb::RulesetRef],
    context: &mut RequestOccurrences,
    response: &mut pb::RunProgramResponse,
) -> Result<pb::NativeRunReport, String> {
    let original_rules = response.rules.len();
    let result = (|| {
        let mut iterations = Vec::with_capacity(report.iterations.len());
        for iteration in &report.iterations {
            let ruleset = &iteration.rule_set_report;
            let mut rule_reports = Vec::with_capacity(ruleset.rule_reports.len());
            for (name, reports) in &ruleset.rule_reports {
                let (rule, direction) = rule_reference(name, context, response)?;
                rule_reports.push(pb::NativeRuleReportsEntry {
                    rule,
                    direction,
                    native_name: name.to_string(),
                    reports: reports
                        .iter()
                        .map(|report| {
                            Ok(pb::NativeRuleReport {
                                plan: report.plan.as_ref().map(export_plan).transpose()?,
                                search_and_apply_time: Some(pb::ReportDuration {
                                    seconds: report.search_and_apply_time.as_secs(),
                                    nanos: report.search_and_apply_time.subsec_nanos(),
                                }),
                                num_matches: u64::try_from(report.num_matches)
                                    .map_err(|_| "native match count exceeds uint64")?,
                            })
                        })
                        .collect::<Result<_, String>>()?,
                });
            }
            iterations.push(pb::NativeIterationReport {
                rule_set_report: Some(pb::NativeRuleSetReport {
                    changed: ruleset.changed,
                    rule_reports,
                    search_and_apply_time: Some(pb::ReportDuration {
                        seconds: ruleset.search_and_apply_time.as_secs(),
                        nanos: ruleset.search_and_apply_time.subsec_nanos(),
                    }),
                    merge_time: Some(pb::ReportDuration {
                        seconds: ruleset.merge_time.as_secs(),
                        nanos: ruleset.merge_time.subsec_nanos(),
                    }),
                }),
                rebuild_time: Some(pb::ReportDuration {
                    seconds: iteration.rebuild_time.as_secs(),
                    nanos: iteration.rebuild_time.subsec_nanos(),
                }),
            });
        }
        let mut search_and_apply_time_per_rule = vec![];
        for (name, duration) in &report.search_and_apply_time_per_rule {
            let (rule, direction) = rule_reference(name, context, response)?;
            search_and_apply_time_per_rule.push(pb::RuleDurationEntry {
                rule,
                direction,
                native_name: name.to_string(),
                value: Some(pb::ReportDuration {
                    seconds: duration.as_secs(),
                    nanos: duration.subsec_nanos(),
                }),
            });
        }
        let mut num_matches_per_rule = vec![];
        for (name, count) in &report.num_matches_per_rule {
            let (rule, direction) = rule_reference(name, context, response)?;
            num_matches_per_rule.push(pb::RuleCountEntry {
                rule,
                direction,
                native_name: name.to_string(),
                value: u64::try_from(*count).map_err(|_| "native match count exceeds uint64")?,
            });
        }
        let mut ruleset_maps = [vec![], vec![], vec![]];
        for (destination, source) in ruleset_maps.iter_mut().zip([
            &report.search_and_apply_time_per_ruleset,
            &report.merge_time_per_ruleset,
            &report.rebuild_time_per_ruleset,
        ]) {
            for (name, duration) in source {
                // Prefer the actual selection for this output. Otherwise use a
                // unique live named binding (or unique current-request index).
                // Multiple aliases cannot reveal historical selection: omit
                // attribution, retaining the exact native row instead of guessing.
                let mut chosen = vec![];
                for reference in selected.iter().filter(|reference| match &reference.kind {
                    Some(pb::ruleset_ref::Kind::Name(logical)) => context
                        .names
                        .get(logical)
                        .is_some_and(|n| n == name.as_ref()),
                    Some(pb::ruleset_ref::Kind::Index(index)) => context
                        .rulesets
                        .get(*index as usize)
                        .is_some_and(|n| n == name.as_ref()),
                    None => false,
                }) {
                    if !chosen.contains(&reference) {
                        chosen.push(reference);
                    }
                }
                let ruleset = if let [chosen] = chosen.as_slice() {
                    Some((*chosen).clone())
                } else if !chosen.is_empty() {
                    // Multiple actually entered aliases are ambiguous even if
                    // there is only one live named fallback.
                    None
                } else {
                    let names: Vec<_> = context
                        .names
                        .iter()
                        .filter(|(_, physical)| physical.as_str() == name.as_ref())
                        .collect();
                    match names.as_slice() {
                        [(logical, _)] => Some(pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Name((*logical).clone())),
                        }),
                        [] => {
                            let indices: Vec<_> = context
                                .rulesets
                                .iter()
                                .enumerate()
                                .filter(|(_, physical)| physical.as_str() == name.as_ref())
                                .collect();
                            match indices.as_slice() {
                                [(index, _)] => Some(pb::RulesetRef {
                                    kind: Some(pb::ruleset_ref::Kind::Index(
                                        u32::try_from(*index)
                                            .map_err(|_| "ruleset index exceeds uint32")?,
                                    )),
                                }),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                };
                destination.push(pb::RulesetDurationEntry {
                    ruleset,
                    native_name: name.to_string(),
                    value: Some(pb::ReportDuration {
                        seconds: duration.as_secs(),
                        nanos: duration.subsec_nanos(),
                    }),
                });
            }
        }
        let [
            search_and_apply_time_per_ruleset,
            merge_time_per_ruleset,
            rebuild_time_per_ruleset,
        ] = ruleset_maps;
        Ok(pb::NativeRunReport {
            iterations,
            updated: report.updated,
            can_stop: report.can_stop,
            search_and_apply_time_per_rule,
            num_matches_per_rule,
            search_and_apply_time_per_ruleset,
            merge_time_per_ruleset,
            rebuild_time_per_ruleset,
        })
    })();
    if result.is_err() {
        // An unexportable observation must not leave unreferenced catalog rows.
        response.rules.truncate(original_rules);
        context
            .response_rules
            .retain(|_, index| (*index as usize) < original_rules);
    }
    result
}

fn export_plan(plan: &native::Plan) -> Result<pb::ReportPlan, String> {
    let mut stages = Vec::with_capacity(plan.stages.len());
    for (stage, stats, next) in &plan.stages {
        let kind = match stage {
            native::Stage::Intersect { scans } => {
                pb::report_stage::Kind::Intersect(pb::ReportIntersect {
                    scans: scans
                        .iter()
                        .map(
                            |native::SingleScan(table, (variable, column))| pb::ReportScan {
                                table: table.clone(),
                                columns: vec![pb::ReportColumn {
                                    variable: variable.clone(),
                                    column: *column,
                                }],
                            },
                        )
                        .collect(),
                })
            }
            native::Stage::FusedIntersect {
                cover,
                to_intersect,
            } => {
                let mut scans = std::iter::once(cover).chain(to_intersect).map(
                    |native::Scan(table, columns)| pb::ReportScan {
                        table: table.clone(),
                        columns: columns
                            .iter()
                            .map(|(variable, column)| pb::ReportColumn {
                                variable: variable.clone(),
                                column: *column,
                            })
                            .collect(),
                    },
                );
                pb::report_stage::Kind::FusedIntersect(pb::ReportFusedIntersect {
                    cover: scans.next(),
                    to_intersect: scans.collect(),
                })
            }
        };
        stages.push(pb::ReportStage {
            kind: Some(kind),
            stats: stats
                .as_ref()
                .map(|stats| {
                    Ok::<_, String>(pb::ReportStageStats {
                        num_candidates: u64::try_from(stats.num_candidates)
                            .map_err(|_| "stage count exceeds uint64")?,
                        num_succeeded: u64::try_from(stats.num_succeeded)
                            .map_err(|_| "stage count exceeds uint64")?,
                    })
                })
                .transpose()?,
            next: next
                .iter()
                .map(|index| {
                    if *index >= plan.stages.len() {
                        return Err("native plan successor is out of bounds".into());
                    }
                    u64::try_from(*index).map_err(|_| "stage index exceeds uint64".into())
                })
                .collect::<Result<_, String>>()?,
        });
    }
    Ok(pb::ReportPlan { stages })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protobuf::{Engine, source::Source};
    use egglog::{CommandOutput, ExecutionOrigin};
    use prost::Message;

    // Independent comparison of every transported native field. Map enumeration
    // and per-key vectors are compared in the captured instance's own order.
    fn assert_report(native: &native::RunReport, wire: &pb::NativeRunReport) {
        assert_eq!(
            (wire.updated, wire.can_stop),
            (native.updated, native.can_stop)
        );
        assert_eq!(native.iterations.len(), wire.iterations.len());
        for (iteration, decoded) in native.iterations.iter().zip(&wire.iterations) {
            let actual = &iteration.rule_set_report;
            let observed = decoded.rule_set_report.as_ref().unwrap();
            assert_eq!(observed.changed, actual.changed);
            for (time, encoded) in [
                (
                    actual.search_and_apply_time,
                    observed.search_and_apply_time.as_ref().unwrap(),
                ),
                (actual.merge_time, observed.merge_time.as_ref().unwrap()),
                (
                    iteration.rebuild_time,
                    decoded.rebuild_time.as_ref().unwrap(),
                ),
            ] {
                assert_eq!(
                    (encoded.seconds, encoded.nanos),
                    (time.as_secs(), time.subsec_nanos())
                );
            }
            assert_eq!(actual.rule_reports.len(), observed.rule_reports.len());
            for ((name, reports), row) in actual.rule_reports.iter().zip(&observed.rule_reports) {
                assert_eq!(name.as_ref(), row.native_name);
                assert_eq!(reports.len(), row.reports.len());
                for (report, value) in reports.iter().zip(&row.reports) {
                    assert_eq!(report.num_matches as u64, value.num_matches);
                    let time = value.search_and_apply_time.as_ref().unwrap();
                    assert_eq!(
                        (time.seconds, time.nanos),
                        (
                            report.search_and_apply_time.as_secs(),
                            report.search_and_apply_time.subsec_nanos()
                        )
                    );
                    assert_eq!(report.plan.is_some(), value.plan.is_some());
                    if let Some(plan) = &report.plan {
                        let decoded = value.plan.as_ref().unwrap();
                        assert_eq!(plan.stages.len(), decoded.stages.len());
                        for ((stage, stats, next), output) in
                            plan.stages.iter().zip(&decoded.stages)
                        {
                            assert_eq!(
                                next.iter().map(|n| *n as u64).collect::<Vec<_>>(),
                                output.next
                            );
                            assert_eq!(
                                stats
                                    .as_ref()
                                    .map(|s| (s.num_candidates as u64, s.num_succeeded as u64)),
                                output
                                    .stats
                                    .as_ref()
                                    .map(|s| (s.num_candidates, s.num_succeeded))
                            );
                            let scans = match (stage, output.kind.as_ref().unwrap()) {
                                (
                                    native::Stage::Intersect { scans },
                                    pb::report_stage::Kind::Intersect(out),
                                ) => {
                                    assert_eq!(scans.len(), out.scans.len());
                                    for (native::SingleScan(table, (variable, column)), scan) in
                                        scans.iter().zip(&out.scans)
                                    {
                                        assert_eq!(&scan.table, table);
                                        assert_eq!(
                                            scan.columns,
                                            [pb::ReportColumn {
                                                variable: variable.clone(),
                                                column: *column
                                            }]
                                        );
                                    }
                                    continue;
                                }
                                (
                                    native::Stage::FusedIntersect {
                                        cover,
                                        to_intersect,
                                    },
                                    pb::report_stage::Kind::FusedIntersect(out),
                                ) => {
                                    assert_eq!(to_intersect.len(), out.to_intersect.len());
                                    std::iter::once((cover, out.cover.as_ref().unwrap()))
                                        .chain(to_intersect.iter().zip(&out.to_intersect))
                                }
                                _ => panic!("plan stage changed kind"),
                            };
                            for (native::Scan(table, columns), scan) in scans {
                                assert_eq!(&scan.table, table);
                                assert_eq!(columns.len(), scan.columns.len());
                                for ((name, index), column) in columns.iter().zip(&scan.columns) {
                                    assert_eq!(
                                        (column.variable.as_str(), column.column),
                                        (name.as_str(), *index)
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(
            native.search_and_apply_time_per_rule.len(),
            wire.search_and_apply_time_per_rule.len()
        );
        for ((name, time), row) in native
            .search_and_apply_time_per_rule
            .iter()
            .zip(&wire.search_and_apply_time_per_rule)
        {
            assert_eq!(name.as_ref(), row.native_name);
            let value = row.value.as_ref().unwrap();
            assert_eq!(
                (value.seconds, value.nanos),
                (time.as_secs(), time.subsec_nanos())
            );
        }
        assert_eq!(
            native.num_matches_per_rule.len(),
            wire.num_matches_per_rule.len()
        );
        for ((name, count), row) in native
            .num_matches_per_rule
            .iter()
            .zip(&wire.num_matches_per_rule)
        {
            assert_eq!(name.as_ref(), row.native_name);
            assert_eq!(*count as u64, row.value);
        }
        for (map, rows) in [
            (
                &native.search_and_apply_time_per_ruleset,
                &wire.search_and_apply_time_per_ruleset,
            ),
            (&native.merge_time_per_ruleset, &wire.merge_time_per_ruleset),
            (
                &native.rebuild_time_per_ruleset,
                &wire.rebuild_time_per_ruleset,
            ),
        ] {
            assert_eq!(map.len(), rows.len());
            for ((name, time), row) in map.iter().zip(rows) {
                assert_eq!(name.as_ref(), row.native_name);
                let value = row.value.as_ref().unwrap();
                assert_eq!(
                    (value.seconds, value.nanos),
                    (time.as_secs(), time.subsec_nanos())
                );
            }
        }
    }

    #[test]
    fn actual_report_and_getter_roundtrip_with_distinct_selected_route() {
        for (level, composite) in [
            pb::ReportLevel::TimeOnly,
            pb::ReportLevel::WithPlan,
            pb::ReportLevel::StageInfo,
        ]
        .into_iter()
        .flat_map(|level| [false, true].map(|composite| (level, composite)))
        {
            let mut engine = Engine::default();
            let id = pb::CreateEGraphResponse::decode(
                engine
                    .create(
                        &pb::CreateEGraphRequest {
                            sorts: vec![pb::Sort {
                                kind: Some(pb::sort::Kind::Family(pb::HostSort {
                                    name: "i64".into(),
                                    args: vec![],
                                })),
                                ..Default::default()
                            }],
                            options: Some(pb::EGraphOptions {
                                cost_sort: Some(0),
                                ..Default::default()
                            }),
                            ..Default::default()
                        }
                        .encode_to_vec(),
                    )
                    .unwrap()
                    .as_slice(),
            )
            .unwrap()
            .egraph_id;
            engine
                .configure_resources(
                    &pb::ConfigureEGraphResourcesRequest {
                        egraph_id: id,
                        operation: Some(
                            pb::configure_e_graph_resources_request::Operation::ReportLevel(
                                level.into(),
                            ),
                        ),
                    }
                    .encode_to_vec(),
                )
                .unwrap();
            let source = Source::new(
                None,
                r#"
                (datatype M (N i64) (Box M) (Wrap M))
                (ruleset shared)
                (rewrite (Box x) x :ruleset shared)
                (rewrite (Wrap x) x :ruleset shared)
                (Box (N 1))
                (Wrap (N 2))
                (run shared 1)
            "#,
            )
            .unwrap();
            let mut compared = false;
            for program in source {
                let mut program = program.unwrap();
                if !matches!(
                    program.commands.last().and_then(|c| c.kind.as_ref()),
                    Some(pb::command::Kind::Run(_))
                ) {
                    let response = pb::RunProgramResponse::decode(
                        engine
                            .run(
                                &pb::RunProgramRequest {
                                    egraph_id: id,
                                    program: Some(program),
                                    profile: true,
                                    include_run_reports: false,
                                }
                                .encode_to_vec(),
                            )
                            .unwrap()
                            .as_slice(),
                    )
                    .unwrap();
                    assert_eq!(response.error, None);
                    continue;
                }
                program.rulesets.push(pb::Ruleset {
                    name: Some("selected".into()),
                    kind: Some(pb::ruleset::Kind::Combined(pb::CombinedRuleset {
                        rulesets: vec![pb::RulesetRef {
                            kind: Some(pb::ruleset_ref::Kind::Name("shared".into())),
                        }],
                    })),
                    ..Default::default()
                });
                let selected = pb::RulesetRef {
                    kind: Some(pb::ruleset_ref::Kind::Name("selected".into())),
                };
                let Some(pb::command::Kind::Run(run)) = &mut program.commands[0].kind else {
                    unreachable!()
                };
                run.ruleset = Some(selected.clone());
                if composite {
                    program.commands = vec![pb::Command {
                        kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                            times: Some(1),
                            body: vec![program.commands[0].clone(); 2],
                            ..Default::default()
                        })),
                        ..Default::default()
                    }];
                }
                let session = engine.graphs.get_mut(&id).unwrap();
                let prepared = session.prepare(&mut program).unwrap();
                let mut response = pb::RunProgramResponse {
                    profile: Some(pb::ProfileSummary::default()),
                    ruleset_publication: Some(pb::RulesetPublication::default()),
                    ..Default::default()
                };
                let mut context = session.install(prepared, &mut response).unwrap();
                // Independent native codec oracle for this known fixture shape,
                // using the authoritative prepared selector rather than the
                // adapter's former private control-tree lowering.
                let leaf = egglog::ast::Schedule::Run(
                    egglog::span!(),
                    egglog::ast::RunConfig {
                        ruleset: context.names["selected"].clone(),
                        until: None,
                    },
                );
                let schedule = if composite {
                    egglog::ast::Schedule::Repeat(
                        egglog::span!(),
                        1,
                        Box::new(egglog::ast::Schedule::Sequence(
                            egglog::span!(),
                            vec![leaf.clone(), leaf],
                        )),
                    )
                } else {
                    leaf
                };
                let commands = vec![egglog::ast::Command::RunSchedule(schedule)];
                let mut captured = None;
                session
                    .graph
                    .run_program_observed(
                        commands,
                        &mut |_, origin, output| {
                            if origin == ExecutionOrigin::Requested
                                && let CommandOutput::RunSchedule(report) = output
                            {
                                captured = Some(report);
                            }
                        },
                        &mut |_, _| {},
                    )
                    .unwrap();
                let captured = captured.unwrap();
                if composite {
                    assert_eq!(captured.iterations.len(), 2);
                }
                let wire = export(
                    &captured,
                    std::slice::from_ref(&selected),
                    &mut context,
                    &mut response,
                )
                .unwrap();
                let decoded = pb::NativeRunReport::decode(wire.encode_to_vec().as_slice()).unwrap();
                assert_report(&captured, &decoded);
                assert_eq!(decoded.num_matches_per_rule.len(), 2);
                assert!(
                    decoded
                        .num_matches_per_rule
                        .iter()
                        .all(|row| row.rule.is_some()
                            && row.direction == Some(pb::NativeRuleDirection::Single.into()))
                );
                assert!(
                    response
                        .rules
                        .iter()
                        .all(|rule| rule.root.as_ref().unwrap().kind
                            == Some(pb::ruleset_ref::Kind::Name("shared".into())))
                );
                assert!(
                    decoded
                        .search_and_apply_time_per_ruleset
                        .iter()
                        .all(|row| row.ruleset.as_ref() == Some(&selected))
                );
                let plans: Vec<_> = decoded
                    .iterations
                    .iter()
                    .flat_map(|i| &i.rule_set_report.as_ref().unwrap().rule_reports)
                    .flat_map(|r| &r.reports)
                    .collect();
                assert!(!plans.is_empty());
                assert!(
                    plans
                        .iter()
                        .all(|r| r.plan.is_some() == (level != pb::ReportLevel::TimeOnly))
                );
                let actual = session.graph.get_overall_run_report();
                let stats = export(actual, &[], &mut context, &mut response).unwrap();
                assert_report(
                    actual,
                    &pb::NativeRunReport::decode(stats.encode_to_vec().as_slice()).unwrap(),
                );
                compared = true;
            }
            assert!(compared);
        }
    }

    #[test]
    fn whole_schedule_failure_keeps_effects_not_an_incomplete_report() {
        use egglog::ast::{Command, RunConfig, Schedule};
        use egglog::{ExecutionEvent, NativeLoopStop};
        let source = "(datatype M (N i64) (Goal i64) (After i64)) (ruleset good) (ruleset bad) (ruleset suffix) (rule ((N x)) ((Goal x)) :ruleset good) (rule ((N x)) ((Goal (+ x 9223372036854775807))) :ruleset bad) (rule ((N x)) ((After x)) :ruleset suffix) (N 1) (run good 1) (N 2)";
        for mode in [
            pb::ExecutionMode::Normal,
            pb::ExecutionMode::TermEncoding,
            pb::ExecutionMode::Proofs,
            pb::ExecutionMode::ProofTesting,
        ] {
            let mut native_graph = match mode {
                pb::ExecutionMode::Normal => egglog::EGraph::default(),
                pb::ExecutionMode::TermEncoding => {
                    egglog::EGraph::default().with_term_encoding_enabled()
                }
                pb::ExecutionMode::Proofs => egglog::EGraph::default().with_proofs_enabled(),
                _ => egglog::EGraph::default()
                    .with_proofs_enabled()
                    .with_proof_testing(),
            };
            native_graph.parse_and_run_program(None, source).unwrap();
            let native_before = native_graph.get_overall_run_report().clone();
            let leaf = |name: &str| {
                Schedule::Run(
                    egglog::span!(),
                    RunConfig {
                        ruleset: name.into(),
                        until: None,
                    },
                )
            };
            let schedule = Schedule::Repeat(
                egglog::span!(),
                1,
                Box::new(Schedule::Sequence(
                    egglog::span!(),
                    vec![
                        leaf("good"),
                        Schedule::Saturate(
                            egglog::span!(),
                            Box::new(Schedule::Sequence(
                                egglog::span!(),
                                vec![leaf("bad"), leaf("suffix")],
                            )),
                        ),
                        leaf("suffix"),
                    ],
                )),
            );
            let mut failed_loops = vec![];
            let error = native_graph
                .run_program_observed(
                    vec![Command::RunSchedule(schedule)],
                    &mut |_, _, _| panic!("failed whole schedule produced output"),
                    &mut |_, event| {
                        if let ExecutionEvent::LoopFinished {
                            schedule: Some(site),
                            completed,
                            stop,
                            result,
                            ..
                        } = event
                        {
                            assert!(result.is_err());
                            failed_loops.push((site.path.to_vec(), completed, stop));
                        }
                    },
                )
                .unwrap_err();
            assert!(
                matches!(error, egglog::Error::BackendError(_)),
                "{mode:?}: {error:?}"
            );
            assert_eq!(
                failed_loops,
                [(vec![0, 1], 0, None::<NativeLoopStop>), (vec![], 0, None)]
            );
            let native_after = export(
                native_graph.get_overall_run_report(),
                &[],
                &mut RequestOccurrences::default(),
                &mut pb::RunProgramResponse::default(),
            )
            .unwrap();
            assert_report(&native_before, &native_after);
            native_graph
                .parse_and_run_program(None, "(check (Goal 2)) (fail (check (After 1)))")
                .unwrap();

            let mut engine = Engine::default();
            let request = pb::CreateEGraphRequest {
                sorts: vec![pb::Sort {
                    kind: Some(pb::sort::Kind::Family(pb::HostSort {
                        name: "i64".into(),
                        args: vec![],
                    })),
                    ..Default::default()
                }],
                options: Some(pb::EGraphOptions {
                    cost_sort: Some(0),
                    execution_mode: mode.into(),
                    ..Default::default()
                }),
                threads: Some(1),
                ..Default::default()
            };
            let id = pb::CreateEGraphResponse::decode(
                engine.create(&request.encode_to_vec()).unwrap().as_slice(),
            )
            .unwrap()
            .egraph_id;
            // Source publishes a ruleset body only at its first Run. Export
            // the two remaining definitions, without executing those Runs.
            for program in
                Source::new(None, &format!("{source} (run bad 1) (run suffix 1)")).unwrap()
            {
                let mut program = program.unwrap();
                if program.commands.iter().any(|command| matches!(&command.kind,
                    Some(pb::command::Kind::Run(run)) if matches!(run.ruleset.as_ref().and_then(|r| r.kind.as_ref()), Some(pb::ruleset_ref::Kind::Name(name)) if name == "bad" || name == "suffix"))) {
                    program.commands.clear();
                }
                let response = pb::RunProgramResponse::decode(
                    engine
                        .run(
                            &pb::RunProgramRequest {
                                egraph_id: id,
                                program: Some(program),
                                profile: true,
                                include_run_reports: true,
                            }
                            .encode_to_vec(),
                        )
                        .unwrap()
                        .as_slice(),
                )
                .unwrap();
                assert_eq!(response.error, None, "{mode:?}");
            }
            let leaf = |name: &str| pb::Command {
                kind: Some(pb::command::Kind::Run(pb::Run {
                    ruleset: Some(pb::RulesetRef {
                        kind: Some(pb::ruleset_ref::Kind::Name(name.into())),
                    }),
                    ..Default::default()
                })),
                ..Default::default()
            };
            let whole = pb::Command {
                kind: Some(pb::command::Kind::Repeat(pb::Repeat {
                    times: Some(1),
                    body: vec![
                        leaf("good"),
                        pb::Command {
                            kind: Some(pb::command::Kind::Saturate(pb::Saturate {
                                body: vec![leaf("bad"), leaf("suffix")],
                                ..Default::default()
                            })),
                            ..Default::default()
                        },
                        leaf("suffix"),
                    ],
                    ..Default::default()
                })),
                ..Default::default()
            };
            for wrappers in 0..=2 {
                let child = pb::CloneEGraphResponse::decode(
                    engine
                        .clone_egraph(&pb::CloneEGraphRequest { egraph_id: id }.encode_to_vec())
                        .unwrap()
                        .as_slice(),
                )
                .unwrap()
                .egraph_id;
                let before = engine.graphs[&child].graph.get_overall_run_report().clone();
                let mut command = whole.clone();
                for _ in 0..wrappers {
                    command = pb::Command {
                        kind: Some(pb::command::Kind::Fail(Box::new(command))),
                        ..Default::default()
                    };
                }
                let response = pb::RunProgramResponse::decode(
                    engine
                        .run(
                            &pb::RunProgramRequest {
                                egraph_id: child,
                                program: Some(pb::Program {
                                    ir_version: 1,
                                    commands: vec![command],
                                    ..Default::default()
                                }),
                                profile: true,
                                include_run_reports: true,
                            }
                            .encode_to_vec(),
                        )
                        .unwrap()
                        .as_slice(),
                )
                .unwrap();
                assert!(response.outputs.is_empty());
                if wrappers == 1 {
                    assert_eq!(response.error, None);
                } else {
                    let error = response.error.as_ref().unwrap();
                    let location = error
                        .location
                        .as_ref()
                        .unwrap_or_else(|| panic!("mode {mode:?}, wrappers {wrappers}: {error:?}"));
                    if wrappers == 0 {
                        assert_eq!(location.path, [0, 1, 0]);
                        assert_eq!(location.iterations, [0, 0]);
                    } else {
                        assert_eq!(location.path, [0]);
                        assert!(location.iterations.is_empty());
                    }
                    let after = export(
                        engine.graphs[&child].graph.get_overall_run_report(),
                        &[],
                        &mut RequestOccurrences::default(),
                        &mut pb::RunProgramResponse::default(),
                    )
                    .unwrap();
                    assert_report(&before, &after);
                }
                let profile = response.profile.unwrap();
                assert_eq!(profile.complete, wrappers == 1);
                assert_eq!(profile.runs.len(), 2);
                assert_eq!(profile.runs[0].command_path, [0, 0]);
                assert_eq!(profile.runs[1].command_path, [0, 1, 0]);
                assert_eq!(profile.runs[1].search_and_apply_nanos, None);
                assert_eq!(profile.runs[1].invocations, 1);
                // Direct native observation of retained rows is test-only;
                // production execution above used only the encoded API.
                let session = &mut engine.graphs.get_mut(&child).unwrap().graph;
                let goal = super::super::native_name("call", "Goal");
                let after = super::super::native_name("call", "After");
                session
                    .parse_and_run_program(
                        None,
                        &format!("(check ({goal} 2)) (fail (check ({after} 1)))"),
                    )
                    .unwrap();
            }
        }
    }

    #[test]
    fn entered_alias_ambiguity_is_not_named_fallback() {
        let mut report = native::RunReport::default();
        report
            .search_and_apply_time_per_ruleset
            .insert("physical".into(), std::time::Duration::from_nanos(7));
        report
            .search_and_apply_time_per_ruleset
            .insert("other".into(), std::time::Duration::from_nanos(11));
        let mut context = RequestOccurrences {
            names: [
                ("r".into(), "physical".into()),
                ("s".into(), "other".into()),
            ]
            .into(),
            rulesets: vec!["physical".into()],
            ..Default::default()
        };
        let named = pb::RulesetRef {
            kind: Some(pb::ruleset_ref::Kind::Name("r".into())),
        };
        let indexed = pb::RulesetRef {
            kind: Some(pb::ruleset_ref::Kind::Index(0)),
        };
        for (selected, expected) in [
            (vec![], Some(named.clone())),
            (vec![named.clone(), named.clone()], Some(named.clone())),
            (vec![indexed.clone()], Some(indexed.clone())),
            (vec![named.clone(), indexed], None),
        ] {
            let wire = export(
                &report,
                &selected,
                &mut context,
                &mut pb::RunProgramResponse::default(),
            )
            .unwrap();
            let row = wire
                .search_and_apply_time_per_ruleset
                .iter()
                .find(|row| row.native_name == "physical")
                .unwrap();
            assert_eq!(row.ruleset, expected);
            assert_eq!(row.value.as_ref().unwrap().nanos, 7);
            let other = wire
                .search_and_apply_time_per_ruleset
                .iter()
                .find(|row| row.native_name == "other")
                .unwrap();
            assert_eq!(
                other.ruleset.as_ref().unwrap().kind,
                Some(pb::ruleset_ref::Kind::Name("s".into()))
            );
        }
    }

    #[test]
    fn native_groups_ranges_and_unknown_keys_are_not_coalesced() {
        let mut report = native::RunReport::default();
        let mut context = RequestOccurrences::default();
        let mut response = pb::RunProgramResponse::default();
        let occurrence = pb::RuleAttribution {
            root: Some(pb::RulesetRef {
                kind: Some(pb::ruleset_ref::Kind::Name("live".into())),
            }),
            ..Default::default()
        };
        for (name, direction) in [
            ("forward", pb::NativeRuleDirection::Forward),
            ("reverse", pb::NativeRuleDirection::Reverse),
        ] {
            report
                .search_and_apply_time_per_rule
                .insert(name.into(), std::time::Duration::from_nanos(600));
            context
                .origins
                .insert(name.into(), (occurrence.clone(), direction));
        }
        report.search_and_apply_time_per_rule.insert(
            "unknown".into(),
            std::time::Duration::new(u64::MAX, 999_999_999),
        );
        // Aggregate query counts need not follow the time/history map's keys.
        let wire = export(&report, &[], &mut context, &mut response).unwrap();
        let decoded = pb::NativeRunReport::decode(wire.encode_to_vec().as_slice()).unwrap();
        assert_report(&report, &decoded);
        assert_eq!(response.rules, [occurrence]);
        assert_eq!(decoded.search_and_apply_time_per_rule.len(), 3);
        assert!(decoded.num_matches_per_rule.is_empty());
        for row in &decoded.search_and_apply_time_per_rule {
            if row.native_name == "unknown" {
                assert_eq!((row.rule, row.direction), (None, None));
            } else {
                assert_eq!(row.rule, Some(0));
                assert_eq!(row.value.as_ref().unwrap().nanos, 600);
            }
        }
        assert!(
            export_plan(&native::Plan {
                stages: vec![(native::Stage::Intersect { scans: vec![] }, None, vec![1])]
            })
            .is_err()
        );
        assert_eq!(
            export_plan(&native::Plan::default()).unwrap(),
            pb::ReportPlan::default()
        );
    }
}
