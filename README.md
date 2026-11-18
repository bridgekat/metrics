# Lean term graph metrics

A term graph shows how a compiled Lean expression is built from smaller expressions and which binder introduces each variable it uses. A theorem has a **type** (its statement) and a **value** (its proof). Both are expressions, so the same graph model applies to proofs, ordinary definitions, and the types that appear inside them.

The extractor reads compiled `.olean` files. It sees the term that Lean elaborated, including implicit arguments and the proof produced by tactics. A tactic such as `simp` can produce many expression nodes. The graph describes that proof's structure and dependencies. Its measurements have no calibrated interpretation as a score of mathematical quality.

## From a term to a graph

Start with the **occurrence tree**. Give every occurrence of an expression constructor its own node. An application `f x` has an application node with two children, the function and the argument. If `f` occurs twice, there are two occurrences to visit. This holds even when Lean internally shares the same expression object.

Add **reference edges**. A binder introduces a variable that may be used in its body. For example, the lambda in `fun (x : Nat) => x` binds the final `x`. A tree edge tells us where a use sits in the syntax. A reference edge goes **from the binder to the use** and tells us where that use gets its meaning. One binder can have many outgoing reference edges or none.

| Node | Children in traversal order | Where its variable is in scope |
| --- | --- | --- |
| Application `f a` | Function, argument | No variable introduced |
| Lambda `fun (x : T) => b` | Parameter type `T`, body `b` | In `b` |
| Forall `∀ x : T, U` | Parameter type `T`, result type `U` | In `U`. Lean also represents `T → U` this way. |
| Let `let x : T := v; b` | Annotation `T`, defining value `v`, body `b` | In `b`. Occurrences in `T` and `v` resolve in the enclosing scope. |

A **de Bruijn index** identifies a local variable by how many enclosing binders to step past. Index 0 means the nearest binder in scope, index 1 means the next one out. This also resolves shadowing. In `fun (x : Nat) => let x : Nat := x; x`, the use on the right of `:=` refers to the lambda, and the final use refers to the let. Both indices are 0 because the scope has changed.

### A worked example

Consider the following value in isolation. The table lists its expression occurrences in **preorder**. The traversal visits a node first and then each child's entire subtree from left to right.

```lean
fun (f : Nat → Nat) =>
  let x : Nat := f Nat.zero
  f x
```

| ID | Occurrence | Tree parent | Binder of this use |
| ---: | --- | ---: | --- |
| 0 | lambda binding `f` | — | |
| 1 | forall for the arrow `Nat → Nat` | 0 | |
| 2 | `Nat`, arrow domain | 1 | |
| 3 | `Nat`, arrow result | 1 | |
| 4 | let binding `x` | 0 | |
| 5 | `Nat`, annotation of `x` | 4 | |
| 6 | application `f Nat.zero` | 4 | |
| 7 | `f`, index 0 | 6 | 0 |
| 8 | `Nat.zero` | 6 | |
| 9 | application `f x` | 4 | |
| 10 | `f`, index 1 | 9 | 0 |
| 11 | `x`, index 0 | 9 | 4 |

There are **12 nodes and 3 reference edges** (0 → 7, 0 → 10, and 4 → 11). Node 10 has tree parent 9 because it occupies the function position of the final application. Its binder is 0 because the outer lambda introduced that function. In the `--graph` JSON array, each row's index is its ID, and the `parent` and `binder` fields encode those two incoming edges. A null field means the corresponding edge is absent.

A **cut** is the boundary immediately after visiting one node and before visiting the next. A binding is **live** at that cut when it has activated and still has a reference ahead. Lambdas and foralls activate at their own node. A let activates when the traversal finishes its defining value. A binding with no uses is never live. Tree edges determine traversal order. Only binder-to-use edges contribute to liveness.

| Cut after node(s) | Live bindings | Number live | Sum of type sizes |
| --- | --- | ---: | ---: |
| 0–7 | `f` | 1 | 3 |
| 8–9 | `f`, `x` | 2 | 4 |
| 10 | `x` | 1 | 1 |
| 11 | none | 0 | 0 |

**Width is 2**, the largest number simultaneously live. **Weighted width is 4**, the largest sum of their annotation sizes. The type of `f` costs three nodes (1–3). The type of `x` costs one (5). At cut 7, the first use of `f` has occurred, but the second use still lies ahead. At cut 8, the defining value of `x` is complete, so both are live. Each live binding is charged once regardless of its number of future uses.

### From one declaration to files and imports

For a declaration, wrap its type and value in a synthetic let and end its body with a synthetic unit `()`. This adds the signature and the wrapper to the graph of the value illustrated above. For a whole file, put the next declaration in the preceding let's body. For example, these two declarations have the following graph shape in pseudocode.

```text
let twice : Nat → Nat := fun n => Nat.add n n
let four  : Nat       := twice (twice 1)
()
```

Each use of `n` links to the lambda. Both uses of `twice` link to the first declaration let. Its definition occurs once. The final unit marks the end of the file and introduces no reference. The extractor puts prerequisites before users and uses compiled declaration order to break ties among roots. It includes private and generated declarations.

The **boundary** determines how to interpret a global name. With `decl` on `four`, `twice` is an external constant leaf. With `file` on their shared file, the two uses of `twice` become references to its declaration binder. With `module`, dependencies in imported files also enter the graph.

In linked mode, concatenate the included declarations into one synthetic file with a single final unit. Imports determine the order of the files. Within a file the scheduler visits each root's prerequisites before the root, taking roots in compiled order and keeping the first visit to each declaration. Uses in later files resolve directly to the earlier declaration lets. The JSON field `module` on each `declLet` records its source module. Moving a declaration across a file boundary preserves both widths whenever the included terms and their order stay the same.

For example, suppose `Base` defines `seed`, `Left` and `Right` each import `Base`, and `Cases` imports both. Here is the relevant part of the linked graph in pseudocode, with prerequisites of `seed` omitted.

```text
let seed  : Box       := …
let left  : Box       := seed
let right : Box       := seed
let pair  : Box × Box := (left, right)
()
```

Both uses of `seed` point to the same binder. It stays live until the use inside `right`. When the definition of `right` finishes, both `left` and `right` are live for `pair`, each with the weight of its own `Box` annotation. An import-only entry point contributes its selected declarations to the chain without adding a node of its own. To inspect this example, run `lake exe metrics module MetricsTest.Cases Fixture.pair --graph` after building the fixtures.

### Kernel-generated declarations and axioms

Lean creates an inductive type, its constructors, and its recursor (the operation for reasoning by cases or induction) together. Each receives a declaration let with its actual Lean type. For the value, the extractor uses a **schema node**. This node stands for the kernel construction and has a child for each dependency supplied to it. The schema can therefore depend on earlier declarations and locally bound variables without requiring one Lean function type that fits every inductive.

```lean
def Element := Nat

inductive Box where
  | pack : Element → Box

inductive Tagged (α : Type) (tag : α) where
  | mk : Tagged α tag
```

The signature `Box : Type` alone would miss the dependency on `Element`. The extractor inspects the constructor signatures, so the schema defining `Box` has a child referring to the earlier `Element` let. The constructor schema for `Box.pack` depends on its owning type. The recursor schema for `Box.rec` depends on `Box.pack` through its computation rule.

For `Tagged`, the value has the schematic shape `fun (α : Type) (tag : α) => inductiveSchema(α, tag)`. The occurrence of `α` in the type of `tag` and the schema's `α` argument both refer to the first lambda. The schema's `tag` argument refers to the second. Uniform parameters generalized from a Lean section are handled the same way.

Named schema dependencies occur once each, in deterministic order. For mutually defined inductives, the extractor considers the whole family's signatures and constructors, treating the family's own type names as internal. Recursor schemas also include external names in rule right-hand sides, with recursive calls in the same family treated as internal. Primitive quotient declarations have a schema kind of their own. Generated declarations with ordinary definition bodies use those bodies.

In a closed graph the accepted standard axiom leaves are `propext`, `Classical.choice`, and `Quot.sound`. An encountered `sorryAx` or an unsupported axiom declaration fails extraction. An open boundary can leave an external name unexamined. The extractor trusts the compiled environment.

## Reading a measurement

| JSON field | Meaning |
| --- | --- |
| `nodes`, `references` | All occurrence nodes, including synthetic wrappers, and all binder-to-use edges. An application stays binary. Metadata wrappers, implicit arguments, literals, sorts and projections occupy nodes. A projection can carry a reference through its structure name. |
| `width` | Peak number of live bindings in the fixed preorder. For a used binding its live cuts range from activation (inclusive) to its last reference (exclusive). |
| `weightedWidth` | Peak sum of the live bindings' type sizes. Size counts annotation occurrences, skipping metadata wrappers. Definition bodies do not add to the weight. |
| `unusedLets` | Local lets, including elaborated haves, with no reference from their body. The node ID distinguishes shadowed names. |
| `unusedParameters` | Corresponding outer forall and lambda binders for which both the statement and the value omit the parameter. Matching proceeds through metadata and stops when either binder sequence ends. Passing a parameter to a callee counts as a use. |

For a reproducible proof example, the test suite measures `Fixture.conjunction`. It proves `(P ∧ Q) ∧ R` from proofs of `P`, `Q`, and `R`. Its declaration graph has 56 nodes, width 6, and weighted width 6. All reported measurements can be recomputed from the optional graph export. The export preserves topology, node kinds, binding names and declaration ownership. It omits literal values, universe payloads and metadata contents.

## Can this scale to a whole library?

**For a library-wide survey of individual declarations, the tool can process the library in batches. For one exact width of a large linked library, the current implementation is limited by the size of the expanded graph.** These answer different research questions.

| Question | Command | What sets the working size |
| --- | --- | --- |
| Which declarations have large proofs, high width, or unused bindings? | `dump` | A worker loads the compiled environment once, measures one declaration at a time, and writes one JSON line per declaration. Graph memory depends on the largest individual graph being processed. |
| How many bindings stay live across declarations in this file? | `file` | The entire file graph is held in memory. External declarations are leaves. |
| How many bindings stay live across imports? | `module` | All selected declarations form a single in-memory graph. Each declaration has one definition regardless of how many files use it. Repeated expression occurrences within definitions still count separately. |

**Why per-declaration peaks cannot be combined.** In the two-declaration example, measuring `four` alone treats `twice` as an external leaf. In file mode, the `twice` binder stays live into the definition of `four`. The separate reports omit that interval. A maximum or sum of their widths cannot recover the file width. The same issue arises at import boundaries.

**Cost of one measurement.** Let *N* be the number of *emitted occurrence nodes*, including all included annotations, bodies, and synthetic nodes. Once the graph exists, the width calculation makes a fixed number of passes. It finds each binder's last reference, computes annotation sizes from subtree boundaries, and sweeps the activation and expiry events. This takes expected O(*N*) time with hash maps and O(*N*) space. The extractor also loads the environment and schedules dependencies before emission. The node cap applies during emission and therefore does not bound all memory or time spent by the process. Omitting `--graph` saves the cost of serializing and writing the node array. The worker still builds the graph internally.

**What was measured.** These checks used Lean `v4.36.0-rc2` and the default limit of 2,000,000 nodes per graph.

| Measurement | Observed result |
| --- | --- |
| `dump` on `Numlib.Algebra.LinearRecurrence` | 113 completed records with 3,518,311 nodes in total. The largest completed graph had 396,916 nodes. One additional record reported an unsupported dependency cycle in `LinearRecurrence.mkSolWith._unsafe_rec`. |
| `file Numlib.Algebra.Field.GeomSum` | 8,932 nodes, width 9, weighted width 115. |
| `module Numlib.Algebra.Field.GeomSum geom_sum_eq_ite_of_pow_eq_one` | Linking this theorem's transitive dependencies exceeded the node limit. Its linked width is unknown. |

The first run shows how a batch can process more nodes in total than the limit for a single graph. For a library survey, shard `dump` by module, aggregate the successful records, and report the error count alongside the distribution. Each shard loads its own copy of the imported environment, so available memory constrains the worker count. The checks above cover two Numlib files. Full-library coverage, wall time, and peak RAM have yet to be measured.

For an exact linked-library metric beyond the current in-memory budget, one possible implementation would write ordered node and reference records to disk, determine subtree ends and last uses in a separate pass, then sweep the resulting events. This would move storage off heap while retaining the fixed traversal and cross-boundary intervals. Traversal time and disk volume would still grow with the number of emitted occurrences.

## Run

Build the executable and run the regression suite in this directory.

```sh
lake build
lake exe checkMetrics
lake exe metrics decl MetricsTest.Cases Fixture.conjunction --graph
```

From the built numlib project root, run the executable inside the project's Lake environment. On Windows the executable has an additional `.exe` suffix.

```sh
tool=tools/metrics/.lake/build/bin/metrics
lake env "$tool" decl Numlib.Algebra.Field.GeomSum geom_sum_eq_ite_of_pow_eq_one
lake env "$tool" file Numlib.Algebra.Field.GeomSum --graph
lake env "$tool" module Init.Prelude Nat.rec
```

| Command | Declarations included |
| --- | --- |
| `decl MODULE NAME` | The named declaration, with its signature and value. Other globals form the open boundary. |
| `file MODULE` | All declarations of that compiled file, including private and generated declarations. Imported globals form the open boundary. |
| `module MODULE` | All declarations in the root file and transitively imported files sharing its first module-name component. Other libraries contribute the declarations reachable from those roots. This includes the contents of import-only library entry points. |
| `module MODULE NAME` | The named declaration and its transitive dependencies, across files and libraries. |

Each command writes one JSON record to stdout. The default limit is two million occurrence nodes per graph. Set `--max-nodes N` to change it. An exceeded limit, unsupported cycle, missing body, or encountered `sorryAx` fails the measurement. Counts are never truncated. External globals at an open boundary are not inspected transitively.

For project-wide per-declaration JSON Lines, run `bash tools/metrics/run.sh . OUT 4` from the project root. The wrapper runs four disjoint module shards with roots Numlib and NumlibSurface. The following command scans a single file in one shard.

```sh
lake env "$tool" dump --roots Numlib.Algebra.Field.GeomSum --out OUT
```

`dump` accepts `--full A,B` to select module prefixes (the roots by default), `--shard i/n` with zero-based indices, `--graph`, and `--max-nodes N`. Each worker writes `decls.i.jsonl`, continues after a per-declaration failure, and exits nonzero if any record contains an `error`. Use a fresh output directory when changing shard counts.

The regression suite independently enumerates live sets on small graphs and checks the schema and import examples. This JSON format supersedes the earlier metrics dump and Python reports.
