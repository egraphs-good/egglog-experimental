use egglog::EGraph;
use egglog_experimental::PortableTypeInfo;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

// Introduce another body expression around caller tokens, as a provider's own
// registration wrapper may do. The receiver must follow the forwarded `self`,
// not these wrapper-authored braces.
macro_rules! forward_context_primitive {
    ($graph:expr, $context:expr, $inputs:ident, $body:expr) => {
        egglog_experimental::add_primitive!(
            $graph,
            "forwarded-receiver"[id = "test.receiver.forwarded"] =
                {$context: (Arc<AtomicUsize>, i64)} [$inputs: i64] -> i64 {
                    {
                        let _ = self::Ordering::SeqCst;
                        $body
                    }
                }
        );
    };
}

struct Provider {
    calls: Arc<AtomicUsize>,
    offset: i64,
}

impl Provider {
    fn register(&self, graph: &mut EGraph) {
        egglog::add_primitive!(
            graph,
            "native-receiver"[id = "test.receiver.native"] =
                {(self.calls.clone(), self.offset): (Arc<AtomicUsize>, i64)}
                |value: i64| -> i64 {
                    {
                        self.ctx.0.fetch_add(1, Ordering::SeqCst);
                        value + self.ctx.1
                    }
                }
        );
        egglog_experimental::add_primitive!(
            graph,
            "bindings-receiver"[id = "test.receiver.bindings"] =
                {(self.calls.clone(), self.offset): (Arc<AtomicUsize>, i64)}
                |value: i64| -?> i64 {
                    Some({
                        self.ctx.0.fetch_add(1, Ordering::SeqCst);
                        value + self.ctx.1
                    })
                }
        );
        forward_context_primitive!(graph, (self.calls.clone(), self.offset), values, {
            self.ctx.0.fetch_add(1, Ordering::SeqCst);
            values.map(|value| value + self.ctx.1).sum()
        });
        egglog_experimental::add_primitive_with_validator!(
            graph,
            "validator-receiver"[id = "test.receiver.validator"] =
                {(self.calls.clone(), self.offset): (Arc<AtomicUsize>, i64)}
                |value: i64| -> i64 {
                    {
                        self.ctx.0.fetch_add(1, Ordering::SeqCst);
                        value + self.ctx.1
                    }
                },
            |_: &mut egglog::TermDag, _: &[egglog::TermId]| None
        );
    }
}

#[test]
fn caller_receiver_survives_portable_and_nested_macro_forwarding() {
    let provider = Provider {
        calls: Arc::new(AtomicUsize::new(0)),
        offset: 10,
    };
    let mut graph = EGraph::default();
    provider.register(&mut graph);
    let catalog = graph.type_info().portable_builtin_catalog().unwrap();
    for key in [
        "test.receiver.native",
        "test.receiver.bindings",
        "test.receiver.forwarded",
        "test.receiver.validator",
    ] {
        assert!(
            catalog
                .definitions
                .primitives
                .iter()
                .any(|primitive| primitive.name == key)
        );
    }
    assert_eq!(provider.calls.load(Ordering::SeqCst), 0);
    graph
        .parse_and_run_program(
            None,
            "(check (= (native-receiver 1) 11))
             (check (= (bindings-receiver 2) 12))
             (check (= (forwarded-receiver 1 2) 23))
             (check (= (validator-receiver 3) 13))",
        )
        .unwrap();
    assert_eq!(provider.calls.load(Ordering::SeqCst), 4);
}
