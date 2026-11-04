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
span `file` means index 0. Spans use byte offsets into `files`. Comments
label entries and are not fields. Builtins come from the backend catalog.

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

Submit the batched `RunProgramRequest`:

```textproto
egraph_id: 1
program {
  nodes { primitive_value { i64: 2 } span { start: 103 end: 104 } } # nodes[0]
  nodes { sort_id: 1 call { func: "Num" args: 0 } span { start: 98 end: 105 } } # nodes[1]
  nodes { primitive_value { i64: 3 } span { start: 111 end: 112 } } # nodes[2]
  nodes { sort_id: 1 call { func: "Num" args: 2 } span { start: 106 end: 113 } } # nodes[3]
  nodes { sort_id: 1 call { func: "Add" args: 1 args: 3 } span { start: 93 end: 114 } } # nodes[4]
  nodes { sort_id: 1 var: "__proto_source_local_0_0" span { start: 126 end: 127 } } # nodes[5]
  nodes { var: "__proto_source_local_0_1" span { start: 138 end: 139 } } # nodes[6]
  nodes { sort_id: 1 call { func: "Num" args: 6 } span { start: 133 end: 140 } } # nodes[7]
  nodes { var: "__proto_source_local_0_2" span { start: 146 end: 147 } } # nodes[8]
  nodes { sort_id: 1 call { func: "Num" args: 8 } span { start: 141 end: 148 } } # nodes[9]
  nodes { sort_id: 1 call { func: "Add" args: 7 args: 9 } span { start: 128 end: 149 } } # nodes[10]
  nodes { sort_id: 1 union { members: 5 members: 10 } span { start: 123 end: 150 } } # nodes[11]
  nodes { sort_id: 1 var: "__proto_source_local_0_0" span { start: 166 end: 167 } } # nodes[12]
  nodes { var: "__proto_source_local_0_1" span { start: 176 end: 177 } } # nodes[13]
  nodes { var: "__proto_source_local_0_2" span { start: 178 end: 179 } } # nodes[14]
  nodes { call { func: "egglog.core.i64.add" args: 13 args: 14 } span { start: 173 end: 180 } } # nodes[15]
  nodes { sort_id: 1 call { func: "Num" args: 15 } span { start: 168 end: 181 } } # nodes[16]
  nodes { sort_id: 1 union { members: 12 members: 16 } span { start: 159 end: 182 } } # nodes[17]
  nodes { sort_id: 1 var: "__proto_source_local_0_0" span { start: 202 end: 203 } } # nodes[18]
  nodes { var: "__proto_source_local_0_1" span { start: 208 end: 209 } } # nodes[19]
  nodes { var: "__proto_source_local_0_2" span { start: 210 end: 211 } } # nodes[20]
  nodes { call { func: "egglog.core.i64.add" args: 19 args: 20 } span { start: 205 end: 212 } } # nodes[21]
  nodes { var: "__proto_source_local_0_1" span { start: 240 end: 241 } } # nodes[22]
  nodes { sort_id: 1 call { func: "Num" args: 22 } span { start: 235 end: 242 } } # nodes[23]
  nodes { var: "__proto_source_local_0_2" span { start: 248 end: 249 } } # nodes[24]
  nodes { sort_id: 1 call { func: "Num" args: 24 } span { start: 243 end: 250 } } # nodes[25]
  nodes { sort_id: 1 call { func: "sum" } span { start: 292 end: 295 } } # nodes[26]
  nodes { primitive_value { i64: 5 } span { start: 301 end: 302 } } # nodes[27]
  nodes { sort_id: 1 call { func: "Num" args: 27 } span { start: 296 end: 303 } } # nodes[28]
  nodes { sort_id: 1 union { members: 26 members: 28 } span { start: 289 end: 304 } } # nodes[29]
  nodes { sort_id: 1 call { func: "sum" } span { start: 315 end: 318 } } # nodes[30]
  nodes { call { func: "value" args: 30 } span { start: 308 end: 319 } } # nodes[31]
  nodes { primitive_value { i64: 5 } span { start: 320 end: 321 } } # nodes[32]
  nodes { union { members: 31 members: 32 } span { start: 305 end: 322 } } # nodes[33]
  nodes { sort_id: 1 call { func: "sum" } span { start: 333 end: 336 } } # nodes[34]
  sorts { primitive { name: "i64" } } # sorts[0]
  sorts { eq: "Math" } # sorts[1]
  declarations { span { end: 45 } eq_sort { name: "Math" } }
  declarations { constructor { name: "Num" inputs { } output: 1 } span { start: 17 end: 26 } }
  declarations { constructor { name: "Add" inputs { sort: 1 } inputs { sort: 1 } output: 1 } span { start: 29 end: 44 } }
  declarations { function { name: "value" inputs { sort: 1 } } span { start: 46 end: 83 } }
  declarations { function { name: "sum" output: 1 } span { start: 84 end: 115 } }
  commands { action { set { target { func: "sum" } value: 4 } span { start: 84 end: 115 } } span { start: 84 end: 115 } }
  commands {
    run {
      rulesets {
        ruleset {
          rules {
            rule {
              query: 11
              head { term: 17 span { start: 159 end: 182 } }
              head { set { target { func: "value" args: 18 } value: 21 } span { start: 190 end: 213 } }
              head { span { start: 221 end: 252 } subsume { func: "Add" args: 23 args: 25 } }
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
      facts: 29 facts: 33
    }
    span {
      start: 282
      end: 323
    }
  }
  commands {
    extract {
      roots: 34
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
          query: 11
          head { term: 17 span { start: 159 end: 182 } }
          head { set { target { func: "value" args: 18 } value: 21 } span { start: 190 end: 213 } }
          head { span { start: 221 end: 252 } subsume { func: "Add" args: 23 args: 25 } }
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
files {
  contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
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
files {
  contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
}
```

Freeze includes declarations, saved rules, and ordinary commands
reconstructing the data. Union nodes preserve classes and their alternatives;
Set restores function rows, and Subsume marks the retained Add row, excluding
it from ordinary matching and extraction. The sort arena contains only
referenced Math/i64 types. Saved code retains its variable binders, spans and
source files. The prototype repeats some sort and file entries when appending
saved code; they denote the same types and source.

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
        nodes { sort_id: 2 union { members: 16 members: 17 } span { file: 1 start: 123 end: 150 } } # nodes[10]
        nodes { sort_id: 2 union { members: 18 members: 19 } span { file: 1 start: 159 end: 182 } } # nodes[11]
        nodes { sort_id: 3 call { func: "egglog.core.i64.add" args: 20 args: 21 } span { file: 1 start: 205 end: 212 } } # nodes[12]
        nodes { sort_id: 2 var: "__proto_source_local_0_0" span { file: 1 start: 202 end: 203 } } # nodes[13]
        nodes { sort_id: 2 call { func: "Num" args: 22 } span { file: 1 start: 235 end: 242 } } # nodes[14]
        nodes { sort_id: 2 call { func: "Num" args: 23 } span { file: 1 start: 243 end: 250 } } # nodes[15]
        nodes { sort_id: 2 var: "__proto_source_local_0_0" span { file: 1 start: 126 end: 127 } } # nodes[16]
        nodes { sort_id: 2 call { func: "Add" args: 24 args: 25 } span { file: 1 start: 128 end: 149 } } # nodes[17]
        nodes { sort_id: 2 var: "__proto_source_local_0_0" span { file: 1 start: 166 end: 167 } } # nodes[18]
        nodes { sort_id: 2 call { func: "Num" args: 26 } span { file: 1 start: 168 end: 181 } } # nodes[19]
        nodes { sort_id: 3 var: "__proto_source_local_0_1" span { file: 1 start: 208 end: 209 } } # nodes[20]
        nodes { sort_id: 3 var: "__proto_source_local_0_2" span { file: 1 start: 210 end: 211 } } # nodes[21]
        nodes { sort_id: 3 var: "__proto_source_local_0_1" span { file: 1 start: 240 end: 241 } } # nodes[22]
        nodes { sort_id: 3 var: "__proto_source_local_0_2" span { file: 1 start: 248 end: 249 } } # nodes[23]
        nodes { sort_id: 2 call { func: "Num" args: 27 } span { file: 1 start: 133 end: 140 } } # nodes[24]
        nodes { sort_id: 2 call { func: "Num" args: 28 } span { file: 1 start: 141 end: 148 } } # nodes[25]
        nodes { sort_id: 3 call { func: "egglog.core.i64.add" args: 29 args: 30 } span { file: 1 start: 173 end: 180 } } # nodes[26]
        nodes { sort_id: 3 var: "__proto_source_local_0_1" span { file: 1 start: 138 end: 139 } } # nodes[27]
        nodes { sort_id: 3 var: "__proto_source_local_0_2" span { file: 1 start: 146 end: 147 } } # nodes[28]
        nodes { sort_id: 3 var: "__proto_source_local_0_1" span { file: 1 start: 176 end: 177 } } # nodes[29]
        nodes { sort_id: 3 var: "__proto_source_local_0_2" span { file: 1 start: 178 end: 179 } } # nodes[30]
        sorts { primitive { name: "i64" } } # sorts[0]
        sorts { eq: "Math" } # sorts[1]
        sorts { eq: "Math" } # sorts[2]
        sorts { primitive { name: "i64" } } # sorts[3]
        declarations { span { end: 45 } eq_sort { name: "Math" } }
        declarations { constructor { name: "Num" inputs { } output: 1 } span { start: 17 end: 26 } }
        declarations { constructor { name: "Add" inputs { sort: 1 } inputs { sort: 1 } output: 1 } span { start: 29 end: 44 } }
        declarations { function { name: "value" inputs { sort: 1 } } span { start: 46 end: 83 } }
        declarations { function { name: "sum" output: 1 } span { start: 84 end: 115 } }
        commands { action { term: 0 } }
        commands { action { term: 1 } }
        commands { action { term: 2 } }
        commands { action { set { target { func: "value" args: 2 } value: 7 } } }
        commands { action { set { target { func: "sum" } value: 2 } } }
        commands { action { subsume { func: "Add" args: 0 args: 1 } } }
        files {
          contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
        }
        files {
          contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
        }
        rulesets {
          value {
            rules {
              rule {
                query: 10
                head { term: 11 span { file: 1 start: 159 end: 182 } }
                head { set { target { func: "value" args: 13 } value: 12 } span { file: 1 start: 190 end: 213 } }
                head { span { file: 1 start: 221 end: 252 } subsume { func: "Add" args: 14 args: 15 } }
              }
              name: "fold"
              eval_mode: RULE_EVAL_MODE_SEMINAIVE
              span {
                file: 1
                start: 116
                end: 273
              }
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
files {
  contents: "(datatype Math\n  (Num i64)\n  (Add Math Math))\n(function value (Math) i64 :no-merge)\n(let sum (Add (Num 2) (Num 3)))\n(rule ((= e (Add (Num a) (Num b))))\n      ((union e (Num (+ a b)))\n       (set (value e) (+ a b))\n       (subsume (Add (Num a) (Num b))))\n      :name \"fold\")\n(run 1)\n(check (= sum (Num 5)) (= (value sum) 5))\n(extract sum 2)\n"
}
```

The final frame acknowledges completion:

```textproto
output { }
```

The printed messages parse back to their executed bytes. Restoring the
snapshot into a fresh graph repeats the check and extraction successfully.
