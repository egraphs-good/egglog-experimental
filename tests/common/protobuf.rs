//! Test-only observation collection. Product APIs retain the original frames.
//! Relocate each local arena once; never identify distinct node locations.

use egglog_proto as pb;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Observed {
    pub output: pb::RunProgramOutput,
    pub error: Option<pb::Error>,
}

impl Observed {
    pub fn from_frames(frames: impl IntoIterator<Item = pb::RunProgramResponse>) -> Self {
        let mut result = Self::default();
        let mut count = 0;
        for frame in frames {
            count += 1;
            assert!(result.error.is_none(), "frame follows terminal error");
            let Some(outcome) = frame.result else {
                panic!("frame has no result")
            };
            let mut output = match outcome {
                pb::run_program_response::Result::Error(error) => {
                    result.error = Some(error);
                    continue;
                }
                pb::run_program_response::Result::Output(output) => output,
            };
            let nodes = u32::try_from(result.output.nodes.len()).unwrap();
            let sorts = u32::try_from(result.output.sorts.len()).unwrap();
            let bump = |index: &mut u32, offset| {
                *index = index.checked_add(offset).unwrap();
            };
            for sort in &mut output.sorts {
                match &mut sort.kind {
                    Some(pb::sort::Kind::Primitive(primitive)) => {
                        for child in &mut primitive.args {
                            bump(child, sorts);
                        }
                    }
                    Some(pb::sort::Kind::Func(function)) => {
                        for child in &mut function.params {
                            bump(child, sorts);
                        }
                        bump(&mut function.result, sorts);
                    }
                    _ => (),
                }
            }
            for node in &mut output.nodes {
                bump(&mut node.sort_id, sorts);
                use pb::{node::Kind as N, primitive_value::Value as V};
                match &mut node.kind {
                    Some(N::Call(call) | N::GetCost(call)) => {
                        for child in &mut call.args {
                            bump(child, nodes);
                        }
                    }
                    Some(N::Eq(union)) => {
                        for child in &mut union.members {
                            bump(child, nodes);
                        }
                    }
                    Some(N::PrimitiveValue(value)) => match &mut value.value {
                        Some(V::Vec(list) | V::Set(list) | V::Multiset(list)) => {
                            for child in &mut list.items {
                                bump(child, nodes);
                            }
                        }
                        Some(V::Map(map)) => {
                            for entry in &mut map.entries {
                                bump(entry.key.as_mut().unwrap(), nodes);
                                bump(entry.value.as_mut().unwrap(), nodes);
                            }
                        }
                        Some(V::Pair(pair)) => {
                            bump(pair.first.as_mut().unwrap(), nodes);
                            bump(pair.second.as_mut().unwrap(), nodes);
                        }
                        Some(V::Maybe(maybe)) => {
                            if let Some(child) = &mut maybe.value {
                                bump(child, nodes);
                            }
                        }
                        Some(V::Lambda(lambda)) => {
                            for child in &mut lambda.captures {
                                bump(child, nodes);
                            }
                            bump(&mut lambda.body, nodes);
                        }
                        Some(V::PartialCall(call)) => {
                            for child in &mut call.args {
                                bump(child, nodes);
                            }
                        }
                        Some(V::Custom(custom)) => {
                            for child in &mut custom.args {
                                bump(child, nodes);
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
            for command in &mut output.outputs {
                match &mut command.kind {
                    Some(pb::command_output::Kind::Extraction(extraction)) => {
                        for term in extraction
                            .roots
                            .iter_mut()
                            .flat_map(|root| &mut root.variants)
                        {
                            bump(&mut term.term, nodes);
                            if let Some(cost) = &mut term.cost {
                                bump(cost, nodes);
                            }
                        }
                    }
                    Some(pb::command_output::Kind::TableRows(table)) => {
                        for cell in table
                            .rows
                            .iter_mut()
                            .flat_map(|row| row.args.iter_mut().chain(row.output.iter_mut()))
                        {
                            match &mut cell.kind {
                                Some(pb::table_cell::Kind::Term(index)) => bump(index, nodes),
                                Some(pb::table_cell::Kind::UnavailableSort(index)) => {
                                    bump(index, sorts)
                                }
                                None => panic!("table cell has no kind"),
                            }
                        }
                    }
                    Some(pb::command_output::Kind::TableStats(tables)) => {
                        for column in tables.stats.iter_mut().flat_map(|table| &mut table.columns) {
                            bump(&mut column.sort, sorts);
                        }
                    }
                    // Nested Programs and proof arenas are independently owned.
                    _ => (),
                }
            }
            result.output.nodes.extend(output.nodes);
            result.output.sorts.extend(output.sorts);
            result.output.outputs.extend(output.outputs);
        }
        assert!(count > 0, "execution lacks a completion frame");
        result
    }
}
