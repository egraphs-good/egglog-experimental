# Constant folding: Egglog source and protobuf

This example folds `2 + 3`, records its value in a table, and subsumes the
original addition row. It checks the result, requests up to two variants,
then freezes the graph.

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

## Input messages

These are actual prototype messages in Protobuf Text Format, formatted
compactly. Source emits one Program; the caller appends `Freeze` to its
commands. Nodes, names, spans and source files are retained as emitted.

Arena indices are zero-based and local to each message. Omitted scalar
fields have protobuf defaults: for example, an omitted `sort_id` or
span `file` means index 0. Input spans use byte offsets into `files`; successful
results omit source metadata. Comments label entries and are not fields.
Builtins come from the backend catalog.

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

Submit the sourcefree `RunProgramRequest`:

```textproto
egraph_id: 1
program {
  nodes { sort_id: 1 primitive_value { i64: 2 } span { start: 103 end: 104 } } # nodes[0]
  nodes { call { func: "Num" args: 0 } span { start: 98 end: 105 } } # nodes[1]
  nodes { sort_id: 1 primitive_value { i64: 3 } span { start: 111 end: 112 } } # nodes[2]
  nodes { call { func: "Num" args: 2 } span { start: 106 end: 113 } } # nodes[3]
  nodes { call { func: "Add" args: 1 args: 3 } span { start: 93 end: 114 } } # nodes[4]
  nodes { span { start: 84 end: 115 } binding: "sum" } # nodes[5]
  nodes { var: "e" span { start: 126 end: 127 } } # nodes[6]
  nodes { sort_id: 1 var: "a" span { start: 138 end: 139 } } # nodes[7]
  nodes { call { func: "Num" args: 7 } span { start: 133 end: 140 } } # nodes[8]
  nodes { sort_id: 1 var: "b" span { start: 146 end: 147 } } # nodes[9]
  nodes { call { func: "Num" args: 9 } span { start: 141 end: 148 } } # nodes[10]
  nodes { call { func: "Add" args: 8 args: 10 } span { start: 128 end: 149 } } # nodes[11]
  nodes { union { members: 6 members: 11 } span { start: 123 end: 150 } } # nodes[12]
  nodes { var: "e" span { start: 166 end: 167 } } # nodes[13]
  nodes { sort_id: 1 var: "a" span { start: 176 end: 177 } } # nodes[14]
  nodes { sort_id: 1 var: "b" span { start: 178 end: 179 } } # nodes[15]
  nodes { sort_id: 1 call { func: "egglog.core.i64.add" args: 14 args: 15 } span { start: 173 end: 180 } } # nodes[16]
  nodes { call { func: "Num" args: 16 } span { start: 168 end: 181 } } # nodes[17]
  nodes { union { members: 13 members: 17 } span { start: 159 end: 182 } } # nodes[18]
  nodes { var: "e" span { start: 202 end: 203 } } # nodes[19]
  nodes { sort_id: 1 var: "a" span { start: 208 end: 209 } } # nodes[20]
  nodes { sort_id: 1 var: "b" span { start: 210 end: 211 } } # nodes[21]
  nodes { sort_id: 1 call { func: "egglog.core.i64.add" args: 20 args: 21 } span { start: 205 end: 212 } } # nodes[22]
  nodes { sort_id: 1 var: "a" span { start: 240 end: 241 } } # nodes[23]
  nodes { call { func: "Num" args: 23 } span { start: 235 end: 242 } } # nodes[24]
  nodes { sort_id: 1 var: "b" span { start: 248 end: 249 } } # nodes[25]
  nodes { call { func: "Num" args: 25 } span { start: 243 end: 250 } } # nodes[26]
  nodes { span { start: 292 end: 295 } binding: "sum" } # nodes[27]
  nodes { sort_id: 1 primitive_value { i64: 5 } span { start: 301 end: 302 } } # nodes[28]
  nodes { call { func: "Num" args: 28 } span { start: 296 end: 303 } } # nodes[29]
  nodes { union { members: 27 members: 29 } span { start: 289 end: 304 } } # nodes[30]
  nodes { span { start: 315 end: 318 } binding: "sum" } # nodes[31]
  nodes { sort_id: 1 call { func: "value" args: 31 } span { start: 308 end: 319 } } # nodes[32]
  nodes { sort_id: 1 primitive_value { i64: 5 } span { start: 320 end: 321 } } # nodes[33]
  nodes { sort_id: 1 union { members: 32 members: 33 } span { start: 305 end: 322 } } # nodes[34]
  nodes { span { start: 333 end: 336 } binding: "sum" } # nodes[35]
  sorts { eq: "Math" span { end: 45 } } # sorts[0]
  sorts { primitive { name: "i64" } } # sorts[1]
  declarations { constructor { name: "Num" inputs { sort: 1 } } span { start: 17 end: 26 } }
  declarations { constructor { name: "Add" inputs { } inputs { } } span { start: 29 end: 44 } }
  declarations { function { name: "value" inputs { } output: 1 } span { start: 46 end: 83 } }
  commands { span { start: 84 end: 115 } let { binding: 5 value: 4 } }
  commands {
    run {
      rulesets {
        ruleset {
          rules {
            rule {
              query: 12
              head { term: 18 span { start: 159 end: 182 } }
              head { set { target { func: "value" args: 19 } value: 22 } span { start: 190 end: 213 } }
              head { span { start: 221 end: 252 } subsume { func: "Add" args: 24 args: 26 } }
            }
            name: "fold"
            eval_mode: RULE_EVAL_MODE_SEMINAIVE
            span {
              start: 116
              end: 273
            }
          }
        }
      }
    }
    span {
      start: 274
      end: 281
    }
  }
  commands {
    check {
      facts: 30 facts: 34
    }
    span {
      start: 282
      end: 323
    }
  }
  commands {
    extract {
      roots: 35
      variants: 2
      extractor: EXTRACTOR_TREE
    }
    span {
      start: 324
      end: 339
    }
  }
  commands {
    freeze { }
  }
  files {
    contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
  }
  rulesets {
    value {
      rules {
        rule {
          query: 12
          head { term: 18 span { start: 159 end: 182 } }
          head { set { target { func: "value" args: 19 } value: 22 } span { start: 190 end: 213 } }
          head { span { start: 221 end: 252 } subsume { func: "Add" args: 24 args: 26 } }
        }
        name: "fold"
        eval_mode: RULE_EVAL_MODE_SEMINAIVE
        span {
          start: 116
          end: 273
        }
      }
    }
  }
}
```

## Response stream

These are the complete response frames, in order. Each owns its arenas
and source files; input indices do not carry into responses.

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

Extraction returns `(Num 5)` at cost 2. The request's
variant count is an upper bound. `term` and `cost` index this frame's nodes.

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
reconstructing the data. Union nodes preserve classes and their alternatives;
Set restores function rows, Let restores the global sum binding, and Subsume
marks the retained Add row. The sort arena contains Math/i64. Saved code retains
its variable binders, without source spans or files.

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
        nodes { union { members: 5 } } # nodes[1]
        nodes { union { members: 7 } } # nodes[2]
        nodes { union { members: 9 members: 10 } } # nodes[3]
        nodes { sort_id: 1 primitive_value { i64: 2 } } # nodes[4]
        nodes { call { func: "Num" args: 4 } } # nodes[5]
        nodes { sort_id: 1 primitive_value { i64: 3 } } # nodes[6]
        nodes { call { func: "Num" args: 6 } } # nodes[7]
        nodes { sort_id: 1 primitive_value { i64: 5 } } # nodes[8]
        nodes { call { func: "Num" args: 8 } } # nodes[9]
        nodes { call { func: "Add" args: 1 args: 2 } } # nodes[10]
        nodes { sort_id: 2 union { members: 17 members: 18 } } # nodes[11]
        nodes { sort_id: 2 union { members: 19 members: 20 } } # nodes[12]
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
        declarations { constructor { name: "Num" inputs { sort: 1 } } }
        declarations { constructor { name: "Add" inputs { } inputs { } } }
        declarations { function { name: "value" inputs { } output: 1 } }
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
                head { term: 12 }
                head { set { target { func: "value" args: 14 } value: 13 } }
                head { subsume { func: "Add" args: 15 args: 16 } }
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

The final frame acknowledges completion:

```textproto
output { }
```

The printed messages parse back to their executed bytes. Restoring the
snapshot into a fresh graph repeats the check and extraction successfully.
