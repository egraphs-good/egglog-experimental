# Constant folding: Egglog source and protobuf

This example folds `2 + 3`, records its value in a table, and subsumes the original
addition row. It checks the result, asks for up to two variants, then freezes
the graph.

```egglog
(datatype Math
  (Num i64)
  (Add Math Math))
(function value (Math) i64 :no-merge)
(let sum (Add (Num 2) (Num 3)))
(rule ((= e (Add (Num a) (Num b))))
      ((union e (Num (+ a b)))
       (set (value e) (+ a b))
       (subsume (Add (Num a) (Num b))))
      :name "fold")
(run 1)
(check (= sum (Num 5)) (= (value sum) 5))
(extract sum 2)
```

`value` is a table function; conflicting writes must agree. The API caller appends
`Freeze` after the source commands. It has no source spelling in this example.

## Input messages

The messages below use Protobuf Text Format. This is a compact, manually authored
equivalent of the source, executed as written. The text frontend normally emits
separate Programs per statement. Here their arenas are packed together, ordinary
expressions share nodes, and query variables use `e`, `a`, and `b`. Optional source
spans, files and documentation are omitted.

Arena indices are zero-based and local to each message. Comments label entries;
they are not fields. Omitted scalar fields take protobuf defaults: for example,
an omitted `sort_id` means sort 0. Builtins such as `i64` and its resolved addition
primitive come from the backend catalog, not user declarations.

Create a graph with i64 cost annotations (`CreateEGraphRequest`):

```textproto
sorts {
  application {
    name: "i64"
  }
}
options {
  cost_sort: 0
}
threads: 1
```

The actual `CreateEGraphResponse` assigns handle 1:

```textproto
egraph_id: 1
threads: 1
```

Submit this `RunProgramRequest`. A source `let` becomes a nullary function and a
`Set`. Node 13 computes `a + b` and is shared by the rule's union and table write.
The empty ruleset name selects the default group.

```textproto
# Manually authored equivalent request; this is not a raw Source dump.
egraph_id: 1
program {
  sorts { application { name: "i64" } } # sorts[0]
  sorts { eq: "Math" }                  # sorts[1]

  nodes { primitive_value { i64: 2 } }                           # nodes[0]
  nodes { primitive_value { i64: 3 } }                           # nodes[1]
  nodes { sort_id: 1 call { func: "Num" args: 0 } }              # nodes[2]
  nodes { sort_id: 1 call { func: "Num" args: 1 } }              # nodes[3]
  nodes { sort_id: 1 call { func: "Add" args: 2 args: 3 } }      # nodes[4]
  nodes { sort_id: 1 call { func: "sum" } }                      # nodes[5]
  nodes { var: "a" }                                            # nodes[6]
  nodes { var: "b" }                                            # nodes[7]
  nodes { sort_id: 1 call { func: "Num" args: 6 } }              # nodes[8]
  nodes { sort_id: 1 call { func: "Num" args: 7 } }              # nodes[9]
  nodes { sort_id: 1 call { func: "Add" args: 8 args: 9 } }      # nodes[10]
  nodes { sort_id: 1 var: "e" }                                 # nodes[11]
  nodes { sort_id: 1 union { members: 11 members: 10 } }         # nodes[12]: query
  nodes { call { func: "egglog.core.i64.add" args: 6 args: 7 } } # nodes[13]
  nodes { sort_id: 1 call { func: "Num" args: 13 } }             # nodes[14]
  nodes { sort_id: 1 union { members: 11 members: 14 } }         # nodes[15]: union action
  nodes { call { func: "value" args: 5 } }                       # nodes[16]
  nodes { primitive_value { i64: 5 } }                           # nodes[17]
  nodes { sort_id: 1 call { func: "Num" args: 17 } }             # nodes[18]
  nodes { sort_id: 1 union { members: 5 members: 18 } }          # nodes[19]: first check
  nodes { union { members: 16 members: 17 } }                    # nodes[20]: second check

  declarations { eq_sort { name: "Math" } }
  declarations { constructor { name: "Num" inputs { sort: 0 } output: 1 } }
  declarations { constructor { name: "Add" inputs { sort: 1 } inputs { sort: 1 } output: 1 } }
  declarations { function { name: "value" inputs { sort: 1 } output: 0 } }
  # Source lowers (let sum ...) to this nullary function plus the first Set.
  declarations { function { name: "sum" output: 1 } }

  rulesets {
    name: ""
    value {
      rules {
        name: "fold"
        eval_mode: RULE_EVAL_MODE_SEMINAIVE
        rule {
          query: 12
          head { term: 15 }
          head { set { target { func: "value" args: 11 } value: 13 } }
          head { subsume { func: "Add" args: 8 args: 9 } }
        }
      }
    }
  }
  commands { action { set { target { func: "sum" } value: 4 } } } # commands[0]
  commands { run { rulesets { name: "" } } } # commands[1]
  commands { check { facts: 19 facts: 20 } } # commands[2]
  commands { extract { roots: 5 variants: 2 extractor: EXTRACTOR_TREE } } # commands[3]
  commands { freeze {} } # commands[4]: appended by the API caller
}
```

## Response stream

These are the four complete `RunProgramResponse` frames, in order. Each output
arena has its own indices; input indices do not carry into responses.

The run reports a change. Its omitted `can_stop` is false; this one round is not
a saturation claim. `location.path: 1` identifies input command 1.

```textproto
output {
  outputs {
    run {
      updated: true
    }
    location {
      path: 1
    }
  }
}
```

The check at command 2 succeeds without an output. Extraction at command 3
returns one variant, `(Num 5)`, despite requesting up to two. `term: 1` points to
output node 1; `cost: 2` points to output node 2, whose numeric value is also 2.

```textproto
output {
  nodes { primitive_value { i64: 5 } } # nodes[0]
  nodes { sort_id: 1 call { func: "Num" args: 0 } } # nodes[1]
  nodes { primitive_value { i64: 2 } } # nodes[2]
  sorts { application { name: "i64" } } # sorts[0]
  sorts { eq: "Math" } # sorts[1]
  outputs {
    extraction {
      roots {
        variants {
          term: 1
          cost: 2
        }
      }
    }
    location {
      path: 3
    }
  }
}
```

The full snapshot at command 4 includes declarations, the saved rule, and actions
that reconstruct the data. Its first three `Action.term` commands inventory the
classes `{Num(2)}`, `{Num(3)}`, and `{Num(5), Add(class 0, class 1)}`. The Add row remains a constructor member of class 2; the final `Subsume` marks
it as subsumed, excluding it from ordinary rule matching and extraction. The two
`Set` actions restore the `value` and `sum` rows. Saved rule code has its own bound
variables and is not part of the stored-class inventory.

This Python-hosted prototype also exports installed primitive sort references,
including its unused `PyObject` sort. Repeated Math/i64 entries denote
the same types; the exporter retains extra entries used by saved rule code.
Builtin descriptors are not included. The omitted `execution_mode` is NORMAL,
and the omitted ruleset binding name is the default group `""`. Declarations and
ruleset bindings install before commands regardless of Text Format field order;
only the command list specifies execution order.

```textproto
output {
  outputs {
    snapshot {
      options {
        cost_sort: 0
        seminaive: true
      }
      program {
        nodes { sort_id: 1 union { members: 4 } } # nodes[0]
        nodes { sort_id: 1 union { members: 6 } } # nodes[1]
        nodes { sort_id: 1 union { members: 8 members: 9 } } # nodes[2]
        nodes { primitive_value { i64: 2 } } # nodes[3]
        nodes { sort_id: 1 call { func: "Num" args: 3 } } # nodes[4]
        nodes { primitive_value { i64: 3 } } # nodes[5]
        nodes { sort_id: 1 call { func: "Num" args: 5 } } # nodes[6]
        nodes { primitive_value { i64: 5 } } # nodes[7]
        nodes { sort_id: 1 call { func: "Num" args: 7 } } # nodes[8]
        nodes { sort_id: 1 call { func: "Add" args: 0 args: 1 } } # nodes[9]
        nodes { sort_id: 10 union { members: 13 members: 16 } } # nodes[10]
        nodes { sort_id: 10 union { members: 13 members: 17 } } # nodes[11]
        nodes { sort_id: 11 call { func: "egglog.core.i64.add" args: 18 args: 19 } } # nodes[12]
        nodes { sort_id: 10 var: "e" } # nodes[13]
        nodes { sort_id: 10 call { func: "Num" args: 18 } } # nodes[14]
        nodes { sort_id: 10 call { func: "Num" args: 19 } } # nodes[15]
        nodes { sort_id: 10 call { func: "Add" args: 14 args: 15 } } # nodes[16]
        nodes { sort_id: 10 call { func: "Num" args: 12 } } # nodes[17]
        nodes { sort_id: 11 var: "a" } # nodes[18]
        nodes { sort_id: 11 var: "b" } # nodes[19]
        sorts { application { name: "i64" } } # sorts[0]
        sorts { eq: "Math" } # sorts[1]
        sorts { application { name: "String" } } # sorts[2]
        sorts { application { name: "PyObject" } } # sorts[3]
        sorts { application { name: "Unit" } } # sorts[4]
        sorts { application { name: "BigRat" } } # sorts[5]
        sorts { application { name: "bool" } } # sorts[6]
        sorts { application { name: "f64" } } # sorts[7]
        sorts { application { name: "Rational" } } # sorts[8]
        sorts { application { name: "BigInt" } } # sorts[9]
        sorts { eq: "Math" } # sorts[10]
        sorts { application { name: "i64" } } # sorts[11]
        declarations { eq_sort { name: "Math" } }
        declarations { constructor { name: "Num" inputs { } output: 1 } }
        declarations { constructor { name: "Add" inputs { sort: 1 } inputs { sort: 1 } output: 1 } }
        declarations { function { name: "value" inputs { sort: 1 } } }
        declarations { function { name: "sum" output: 1 } }
        commands { action { term: 0 } }
        commands { action { term: 1 } }
        commands { action { term: 2 } }
        commands { action { set { target { func: "value" args: 2 } value: 7 } } }
        commands { action { set { target { func: "sum" } value: 2 } } }
        commands { action { subsume { func: "Add" args: 0 args: 1 } } }
        rulesets {
          value {
            rules {
              rule {
                query: 10
                head { term: 11 }
                head { set { target { func: "value" args: 13 } value: 12 } }
                head { subsume { func: "Add" args: 14 args: 15 } }
              }
              name: "fold"
              eval_mode: RULE_EVAL_MODE_SEMINAIVE
            }
          }
        }
      }
    }
    location {
      path: 4
    }
  }
}
```

Finally, an empty output frame precedes the end of the stream:

```textproto
output { }
```

## What subsumption changes

`Num(5)` already has the lower cost. Subsumption removes the other extraction
alternative: deleting only the rule's subsume action returns both `(Num 5)` at
cost 2 and `(Add (Num 2) (Num 3))` at cost 5 for the same two-variant request.

The source and compact request were executed and compared: declarations, saved
rule structure under variable renaming, and all six stored rows agree. Every
shown Text Format message parses back to the executed protobuf bytes. Restoring
the snapshot into a fresh graph reproduces the data, checks and extraction.
