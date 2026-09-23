#![cfg(feature = "typed")]

use egglog::ast::Command;
use egglog::program::{CommandOutcome, Program};
use egglog_experimental::typed::{builtins::I64, prelude::*};

#[sort(name = "ProgramMath")]
struct Math;

#[declarations]
impl Math {
    #[constructor(name = "program_num")]
    fn num(value: I64) -> Self;
    #[constructor(name = "program_add")]
    fn add(left: Self, right: Self) -> Self;
}

#[relation(name = "program_seen")]
fn seen(value: I64);

#[function(name = "program_score", merge = |old: I64, new: I64| old.max(new))]
fn score(value: I64) -> I64;

#[ruleset]
fn fold(left: &I64, right: &I64) -> Rule {
    rewrite(
        Math::add(Math::num(left), Math::num(right)),
        Math::num(left + right),
    )
}

#[test]
fn install_definitions_does_not_materialize_or_run() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    let declaration = Definition::callable(|value: &I64| score(value))?;
    let group = ruleset(rule((), seen(9)));
    let (result, record) = graph.record(|graph| {
        graph.install((Math::sort_ref(), &declaration, &group))?;
        graph.install((&declaration, &group))
    })?;
    result?;
    assert_eq!(graph.num_tuples()?, 0);
    assert!(
        record
            .entries
            .iter()
            .all(|entry| !matches!(entry.command, Command::Action(_) | Command::RunSchedule(_)))
    );
    assert_eq!(
        record
            .entries
            .iter()
            .filter(|entry| matches!(
                &entry.command, Command::Function { name, .. } if name == "program_score"
            ))
            .count(),
        1
    );
    assert_eq!(
        graph
            .freeze()?
            .table(|value: &I64| score(value))?
            .rows
            .len(),
        0
    );
    assert!(!graph.check(seen(9))?);
    graph.run(group)?;
    assert!(graph.check(seen(9))?);
    Ok(())
}

#[test]
fn selectors_reject_computation_and_primitives() {
    assert!(Definition::callable(|value: &I64| score(value + 1)).is_err());
    assert!(Definition::callable(|left: &I64, right: &I64| left + right).is_err());
    assert!(Definition::callable(|left: &Math, right: &Math| Math::add(right, left)).is_err());
}

#[test]
fn scope_recording_does_not_consume_authoring_budget() -> Result<(), TypedError> {
    let mut graph = EGraph::new(EGraphOptions {
        lowering_limits: LoweringLimits {
            max_commands: 0,
            ..LoweringLimits::default()
        },
        ..EGraphOptions::default()
    });
    let (result, record) = graph.record(|graph| {
        graph.push()?;
        graph.pop()?;
        assert!(graph.pop().is_err());
        graph.check(())
    })?;
    assert!(result?);
    assert_eq!(record.entries.len(), 3);
    assert!(matches!(
        record.entries[2].outcome,
        CommandOutcome::Failure { .. }
    ));
    Ok(())
}

#[test]
fn offline_program_serializes_and_executes_with_core() -> Result<(), Box<dyn std::error::Error>> {
    let root = let_("root", Math::add(Math::num(2), Math::num(3)));
    let mut builder = ProgramBuilder::default();
    builder.install((Math::sort_ref(), &fold))?;
    builder.register(&root)?;
    builder.run(fold.saturate())?;
    builder.check(eq(&root, Math::num(5)))?;
    let program = builder.finish()?;
    assert!(program.to_egglog().contains("run-schedule"));
    let restored = Program::from_json(&program.to_json()?)?;
    let mut graph = egglog_experimental::new_experimental_egraph();
    graph.run_shared_program(restored)?;
    Ok(())
}

#[test]
fn offline_scopes_restore_captures_and_keep_fresh_names() -> Result<(), Box<dyn std::error::Error>>
{
    let root = let_("root", Math::num(1));
    let mut builder = ProgramBuilder::default();
    builder.push()?;
    builder.register(&root)?;
    builder.pop()?;
    assert!(builder.check(&root).is_err());
    assert!(builder.pop().is_err());
    builder.register(&root)?;
    builder.check(eq(&root, Math::num(1)))?;
    let program = builder.finish()?;
    let globals: Vec<_> = program
        .commands
        .iter()
        .filter_map(|command| match command {
            Command::Function {
                name,
                let_binding: true,
                ..
            } => Some(name),
            _ => None,
        })
        .collect();
    assert_eq!(globals.len(), 2);
    assert_ne!(globals[0], globals[1]);
    egglog_experimental::new_experimental_egraph().run_shared_program(program)?;
    Ok(())
}

#[test]
fn failed_builder_batch_does_not_leak_installation_state() -> Result<(), Box<dyn std::error::Error>>
{
    let mut builder = ProgramBuilder::new(LoweringLimits {
        max_commands: 1,
        ..LoweringLimits::default()
    });
    let declaration = Definition::callable(|value: &I64| Math::num(value))?;
    assert!(matches!(
        builder.install(&declaration),
        Err(TypedError::LoweringLimit(_))
    ));
    builder.install(Math::sort_ref())?;
    builder.install(declaration)?;
    let program = builder.finish()?;
    assert_eq!(program.commands.len(), 2);
    assert!(matches!(program.commands[0], Command::Sort { .. }));
    assert!(matches!(program.commands[1], Command::Constructor { .. }));
    Ok(())
}

#[test]
fn installation_is_scoped_and_healthy_preflight_is_atomic() -> Result<(), TypedError> {
    #[sort(name = "program_score")]
    struct Conflicting;
    let declaration = Definition::callable(|value: &I64| score(value))?;
    let mut graph = EGraph::default();
    let (result, record) = graph.record(|graph| {
        graph.push()?;
        graph.install(&declaration)?;
        graph.pop()?;
        assert!(graph.freeze()?.table(|value: &I64| score(value)).is_err());
        graph.install(&declaration)?;
        assert!(matches!(
            graph.install(Conflicting::sort_ref()),
            Err(TypedError::Invalid(_))
        ));
        graph.check(())
    })?;
    assert!(result?);
    assert_eq!(
        record
            .entries
            .iter()
            .filter(|entry| matches!(
                &entry.command, Command::Function { name, .. } if name == "program_score"
            ))
            .count(),
        2
    );
    assert!(
        record
            .entries
            .iter()
            .all(|entry| matches!(entry.outcome, CommandOutcome::Success))
    );
    Ok(())
}

#[test]
fn recording_retains_failures_and_pop_but_does_not_invent_observations() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    let (result, record) = graph.record(|graph| {
        assert!(graph.record(|_| ()).is_err());
        assert!(!graph.check(seen(7))?);
        graph.push()?;
        let error = graph.register((seen(7), panic("recorded failure"), seen(8)));
        assert!(matches!(error, Err(TypedError::Core { completed, .. }) if completed > 0));
        assert!(matches!(graph.check(()), Err(TypedError::NeedsRestore)));
        graph.pop()?;
        assert!(!graph.check(seen(7))?);
        let value = graph.extract(&Math::num(3))?;
        assert_eq!(value, Math::num(3));
        graph.stats()?;
        graph.num_tuples()?;
        graph.freeze()?;
        Ok::<(), TypedError>(())
    })?;
    result?;
    assert!(
        record
            .entries
            .iter()
            .any(|entry| matches!(entry.command, Command::Push(1)))
    );
    assert!(
        record
            .entries
            .iter()
            .any(|entry| matches!(entry.command, Command::Pop(_, 1)))
    );
    assert_eq!(
        record
            .entries
            .iter()
            .filter(|entry| matches!(entry.outcome, CommandOutcome::Failure { .. }))
            .count(),
        3
    );
    assert!(!record.entries.iter().any(|entry| matches!(
        entry.command,
        Command::Extract(..) | Command::PrintOverallStatistics(..) | Command::PrintSize(..)
    )));
    assert!(
        !record
            .program()
            .unwrap()
            .to_egglog()
            .contains("(program_seen 8)")
    );
    // The stopped recording does not prevent a second independently owned record.
    let (result, second) = graph.record(|graph| graph.register(seen(9)))?;
    result?;
    assert_eq!(second.entries.len(), 1);
    Ok(())
}

#[test]
fn recording_stops_when_rust_callback_unwinds() -> Result<(), TypedError> {
    let mut graph = EGraph::default();
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = graph.record(|_| panic!("host callback failed"));
    }));
    assert!(unwind.is_err());
    let (_, record) = graph.record(|_| ())?;
    assert!(record.entries.is_empty());
    Ok(())
}
