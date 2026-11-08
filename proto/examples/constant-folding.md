# Constant folding: Egglog source and protobuf

This example folds `2 + 3`, records its value in a table, and subsumes the
original addition row. It checks the result, extracts its best term,
then freezes the graph.

The same program is also authored through the [Python API](../conformance/constant_folding.py)
and [Rust API](../conformance/rust/constant_folding.rs). Recorded input Programs
from all three are checked against one [expected TextProto](../conformance/constant-folding.expected.textproto)
after only reordering declarations/arenas and remapping indices.

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
(extract sum)
```

## Input messages

These are actual prototype messages in Protobuf Text Format, formatted
compactly. Source emits one Program; the caller appends `Freeze` to its
commands. Nodes and names are retained as emitted.

Arena indices are zero-based and local to each message. Omitted scalar
fields have protobuf defaults: for example, an omitted `sort_id` means index 0.
Comments label entries and are not fields. Builtins come from the backend catalog.

Create a graph with i64 cost annotations (`CreateEGraphRequest`):

```textproto
sorts { primitive { name: "i64" } } # sorts[0]
options {
  cost_sort: 0
}
threads: 1
```

The `CreateEGraphResponse` assigns its handle:

```textproto
egraph_id: 1
threads: 1
```

Submit the `RunProgramRequest`:

```textproto
egraph_id: 1
program {
  nodes { sort_id: 1 primitive_value { i64: 2 } } # nodes[0]
  nodes { call { func: "Num" args: 0 } } # nodes[1]
  nodes { sort_id: 1 primitive_value { i64: 3 } } # nodes[2]
  nodes { call { func: "Num" args: 2 } } # nodes[3]
  nodes { call { func: "Add" args: 1 args: 3 } } # nodes[4]
  nodes { binding: "sum" } # nodes[5]
  nodes { var: "e" } # nodes[6]
  nodes { sort_id: 1 var: "a" } # nodes[7]
  nodes { call { func: "Num" args: 7 } } # nodes[8]
  nodes { sort_id: 1 var: "b" } # nodes[9]
  nodes { call { func: "Num" args: 9 } } # nodes[10]
  nodes { call { func: "Add" args: 8 args: 10 } } # nodes[11]
  nodes { eq { members: 6 members: 11 } } # nodes[12]
  nodes { var: "e" } # nodes[13]
  nodes { sort_id: 1 var: "a" } # nodes[14]
  nodes { sort_id: 1 var: "b" } # nodes[15]
  nodes { sort_id: 1 call { func: "egglog.core.i64.add" args: 14 args: 15 } } # nodes[16]
  nodes { call { func: "Num" args: 16 } } # nodes[17]
  nodes { eq { members: 13 members: 17 } } # nodes[18]
  nodes { var: "e" } # nodes[19]
  nodes { sort_id: 1 var: "a" } # nodes[20]
  nodes { sort_id: 1 var: "b" } # nodes[21]
  nodes { sort_id: 1 call { func: "egglog.core.i64.add" args: 20 args: 21 } } # nodes[22]
  nodes { sort_id: 1 var: "a" } # nodes[23]
  nodes { call { func: "Num" args: 23 } } # nodes[24]
  nodes { sort_id: 1 var: "b" } # nodes[25]
  nodes { call { func: "Num" args: 25 } } # nodes[26]
  nodes { binding: "sum" } # nodes[27]
  nodes { sort_id: 1 primitive_value { i64: 5 } } # nodes[28]
  nodes { call { func: "Num" args: 28 } } # nodes[29]
  nodes { eq { members: 27 members: 29 } } # nodes[30]
  nodes { binding: "sum" } # nodes[31]
  nodes { sort_id: 1 call { func: "value" args: 31 } } # nodes[32]
  nodes { sort_id: 1 primitive_value { i64: 5 } } # nodes[33]
  nodes { sort_id: 1 eq { members: 32 members: 33 } } # nodes[34]
  nodes { binding: "sum" } # nodes[35]
  sorts { eq: "Math" } # sorts[0]
  sorts { primitive { name: "i64" } } # sorts[1]
  constructors { name: "Num" inputs: 1 }
  constructors { name: "Add" inputs: 0 inputs: 0 }
  commands { let { binding: 5 value: 4 } }
  commands {
    run {
      rulesets {
        ruleset {
          rules {
            rule {
              query: 12
              actions { term: 18 }
              actions { set { target { func: "value" args: 19 } value: 22 } }
              actions { subsume { func: "Add" args: 24 args: 26 } }
            }
            name: "fold"
            eval_mode: RULE_EVAL_MODE_SEMINAIVE
          }
        }
      }
    }
  }
  commands {
    check {
      facts: 30 facts: 34
    }
  }
  commands {
    extract {
      roots: 35
      variants: 1
      extractor: EXTRACTOR_TREE
    }
  }
  commands {
    freeze { }
  }
  rulesets {
    value {
      rules {
        rule {
          query: 12
          actions { term: 18 }
          actions { set { target { func: "value" args: 19 } value: 22 } }
          actions { subsume { func: "Add" args: 24 args: 26 } }
        }
        name: "fold"
        eval_mode: RULE_EVAL_MODE_SEMINAIVE
      }
    }
  }
  functions { name: "value" inputs: 0 output: 1 }
}
```

## Response stream

These are the complete response frames, in order. Each owns its arenas; input
indices do not carry into responses.

The run reports a change. Its omitted `can_stop` is false; one round
does not establish saturation. The check succeeds without an output.

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

Extraction returns `(Num 5)` at cost 2. `term` and `cost` index this frame's nodes.

```textproto
output {
  nodes { primitive_value { i64: 5 } } # nodes[0]
  nodes { sort_id: 1 call { func: "Num" args: 0 } } # nodes[1]
  nodes { primitive_value { i64: 2 } } # nodes[2]
  sorts { primitive { name: "i64" } } # sorts[0]
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

Freeze includes declarations, saved rules, and ordinary commands
reconstructing the data. Eq nodes preserve classes and their alternatives;
Set restores function rows, Let restores the global sum binding, and Subsume
marks the retained Add row. The sort arena contains Math/i64. Saved code retains
its variable binders.

```textproto
output {
  outputs {
    snapshot {
      options {
        cost_sort: 1
        seminaive: true
      }
      program {
        nodes { binding: "sum" } # nodes[0]
        nodes { eq { members: 5 } } # nodes[1]
        nodes { eq { members: 7 } } # nodes[2]
        nodes { eq { members: 9 members: 10 } } # nodes[3]
        nodes { sort_id: 1 primitive_value { i64: 2 } } # nodes[4]
        nodes { call { func: "Num" args: 4 } } # nodes[5]
        nodes { sort_id: 1 primitive_value { i64: 3 } } # nodes[6]
        nodes { call { func: "Num" args: 6 } } # nodes[7]
        nodes { sort_id: 1 primitive_value { i64: 5 } } # nodes[8]
        nodes { call { func: "Num" args: 8 } } # nodes[9]
        nodes { call { func: "Add" args: 1 args: 2 } } # nodes[10]
        nodes { sort_id: 2 eq { members: 17 members: 18 } } # nodes[11]
        nodes { sort_id: 2 eq { members: 19 members: 20 } } # nodes[12]
        nodes { sort_id: 3 call { func: "egglog.core.i64.add" args: 21 args: 22 } } # nodes[13]
        nodes { sort_id: 2 var: "e" } # nodes[14]
        nodes { sort_id: 2 call { func: "Num" args: 23 } } # nodes[15]
        nodes { sort_id: 2 call { func: "Num" args: 24 } } # nodes[16]
        nodes { sort_id: 2 var: "e" } # nodes[17]
        nodes { sort_id: 2 call { func: "Add" args: 25 args: 26 } } # nodes[18]
        nodes { sort_id: 2 var: "e" } # nodes[19]
        nodes { sort_id: 2 call { func: "Num" args: 27 } } # nodes[20]
        nodes { sort_id: 3 var: "a" } # nodes[21]
        nodes { sort_id: 3 var: "b" } # nodes[22]
        nodes { sort_id: 3 var: "a" } # nodes[23]
        nodes { sort_id: 3 var: "b" } # nodes[24]
        nodes { sort_id: 2 call { func: "Num" args: 28 } } # nodes[25]
        nodes { sort_id: 2 call { func: "Num" args: 29 } } # nodes[26]
        nodes { sort_id: 3 call { func: "egglog.core.i64.add" args: 30 args: 31 } } # nodes[27]
        nodes { sort_id: 3 var: "a" } # nodes[28]
        nodes { sort_id: 3 var: "b" } # nodes[29]
        nodes { sort_id: 3 var: "a" } # nodes[30]
        nodes { sort_id: 3 var: "b" } # nodes[31]
        sorts { eq: "Math" } # sorts[0]
        sorts { primitive { name: "i64" } } # sorts[1]
        sorts { eq: "Math" } # sorts[2]
        sorts { primitive { name: "i64" } } # sorts[3]
        constructors { name: "Num" inputs: 1 }
        constructors { name: "Add" inputs: 0 inputs: 0 }
        commands { action { term: 1 } }
        commands { action { term: 2 } }
        commands { action { term: 3 } }
        commands { action { set { target { func: "value" args: 3 } value: 8 } } }
        commands { action { subsume { func: "Add" args: 1 args: 2 } } }
        commands { let { binding: 0 value: 3 } }
        rulesets {
          value {
            rules {
              rule {
                query: 11
                actions { term: 12 }
                actions { set { target { func: "value" args: 14 } value: 13 } }
                actions { subsume { func: "Add" args: 15 args: 16 } }
              }
              name: "fold"
              eval_mode: RULE_EVAL_MODE_SEMINAIVE
            }
          }
        }
        functions { name: "value" inputs: 0 output: 1 }
      }
    }
    location {
      path: 4
    }
  }
}
```

The final frame acknowledges completion:

```textproto
output { }
```

The printed messages parse back to their executed bytes. Restoring the
snapshot into a fresh graph repeats the check and extraction successfully.

## Error context

Install this source, then run `reject` in a later Program:

```egglog
(datatype Math (Num i64) (Add Math Math))
(ruleset reject)
(rule ((Num 5)) ((panic "example error"))
      :ruleset reject :name "reject-five")
(Num 5)
```

The actual terminal response contains the saved rule and only its referenced
constructor. Its node/sort references belong to the returned Program.

```textproto
error {
  code: ERROR_CODE_RUNTIME_FAILURE
  message: "Panic: example error"
  context {
    nodes { call { func: "Num" args: 1 } } # nodes[0]
    nodes { sort_id: 1 primitive_value { i64: 5 } } # nodes[1]
    sorts { eq: "Math" } # sorts[0]
    sorts { primitive { name: "i64" } } # sorts[1]
    constructors { name: "Num" inputs: 1 }
    rulesets {
      value {
        rules {
          rule {
            query: 0
            actions { panic: "example error" }
          }
          name: "reject-five"
          eval_mode: RULE_EVAL_MODE_SEMINAIVE
        }
      }
    }
  }
  location {
    path: 0
  }
  site {
    path: 7 path: 0 path: 2 path: 1 path: 0 path: 1 path: 3 path: 0
  }
}
```

`location` identifies the submitted Run. `site.path` selects
`context.rulesets[0].value.rules[0].rule.actions[0]`; it does not refer to the
original setup request.
