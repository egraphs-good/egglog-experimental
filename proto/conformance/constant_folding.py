# mypy: allow-empty-bodies, disable-error-code="prop-decorator"
"""The public high-level Python version of constant-folding.egg."""

from __future__ import annotations

from egglog import *


class Math(Expr, egg_sort="Math"):
    @method(egg_fn="Num")
    def __init__(self, value: i64Like) -> None: ...

    @method(egg_fn="Add")
    def __add__(self, other: Math) -> Math: ...

    @method(egg_fn="value")
    @property
    def value(self) -> i64: ...


@ruleset(name="")
def fold(e: Math, a: i64, b: i64):
    yield rule(eq(e).to(Math(a) + Math(b)), name="fold").then(
        union(e).with_(Math(a + b)),
        set_(e.value).to(a + b),
        subsume(Math(a) + Math(b)),
    )


def run_example(graph: EGraph) -> None:
    sum_ = graph.let("sum", Math(2) + Math(3))
    graph.run(fold)
    graph.check(eq(sum_).to(Math(5)), eq(sum_.value).to(i64(5)))
    best, cost = graph.extract(sum_, include_cost=True)
    assert best == Math(5) and cost == 2


if __name__ == "__main__":
    graph = EGraph()
    run_example(graph)
    snapshot = graph.freeze()
