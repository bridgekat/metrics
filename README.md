# metrics

Numerical measurements of the quality of Lean code, taken from the compiled `.olean` files of a
project. It reads types and proof terms, not source text, so what it reports is what the proofs
do, not what they look like. See [Metrics](#metrics) for what is measured, and
[What the metrics are worth](#what-the-metrics-are-worth) for how far each one has been validated.
It was developed on, and its defaults are set for, the `numlib` project (backbone `Numlib`,
surface `NumlibSurface`) with a quarter of Mathlib as the baseline.

It has two halves:

- `metrics` (Lean, this directory): three commands that import the project and write JSON lines.
  - `dump`: one record per declaration, with sizes, structural hashes, the lemmas a proof applies,
    and how the declaration uses its own binders.
  - `replace`: for every theorem, whether one earlier lemma closes its statement.
  - `leak`: for every theorem, whether its proof still checks when the definitions it mentions are
    made irreducible.
- `analysis/` (Python, no dependencies): turns those records into findings and library indices.

Nothing here edits the measured project or needs the network.

## Running it

The extractor imports the project's `.olean` files, so it must be built with the project's exact
toolchain (`lean-toolchain` here pins the same release as numlib; change both together). The
project must be built first (`lake build` in it). The commands run inside the project's
environment (`lake env`, from the project's root), which is how they find its modules and Mathlib;
the extractor itself depends on nothing but Lean.

```
lake build                                   # here: once, and after editing the extractor
bash run.sh PROJECT OUT/dump 4               # dump, in 4 shards: about three minutes
python analysis/report.py OUT/dump PROJECT OUT/report     [--replace OUT/replace] [--leak OUT/leak]
```

Every shard imports the whole project (3 to 8 GB of memory each). If the project has
`scripts/lbuild.sh` (numlib's build-slot script), `run.sh` takes one slot per shard through it, so
a measurement and the project's own builds do not run each other out of memory; a long
measurement then holds the slots for its whole run. `replace` and `leak` take the same `--roots`,
`--full`, `--sample`, `--shard` and `--out` arguments as `dump` and are run the same way, one
process per shard; `run.sh` runs them when the command is given before the output directory:

```
bash run.sh PROJECT OUT/replace 5 replace --full Numlib,Mathlib --sample 30     --heartbeats 40000 --max-cand 100
bash run.sh PROJECT OUT/leak 5 leak --full Numlib,NumlibSurface,Mathlib --sample 30 --heartbeats 20000 --max-cand 16
```

On five shards they took 54 and 14 minutes on an idle machine (October 2026), and about three
times as long while the project was being built.

`report.py` writes `summary.json` (library indices with bootstrap intervals), `findings.jsonl`
(every finding on a backbone declaration), `files.csv` (findings per module) and `defs.csv` (the
API of each definition). `validate.py` reports which findings of the October 2026 manual review
(`analysis/labels.json`) the metrics recover.

## How a proof is read

Three conventions decide what counts as a step of a proof. They were arrived at by experiment;
the first version without them measured mostly elaboration noise.

1. **Auxiliary theorems are inlined.** The elaborator moves parts of a proof into constants named
   `foo._proof_1_2` or `foo._simp_1_3`. They are read as their body applied to their arguments, so
   a proof is measured whole.
2. **Lemmas and glue.** A theorem constant counts as a *lemma* unless it is *glue*: declared in a
   logic or tactic module (`Init`, `Std`, `Mathlib.Logic`, `Mathlib.Tactic`, ...), or an instance,
   or a theorem whose conclusion is a class. Glue is transparent: `Eq.mpr`, `congrArg` and the
   `ring` normaliser's lemmas say how a step was carried out, not which step it was.
3. **Explicit arguments only.** The *lemma forest* of a term is its tree of nested lemma
   applications, following explicit arguments. Implicit arguments repeat, as data, proofs that are
   steps elsewhere (a subtype's witness occurs in the type of everything built on it), and
   following them multiplies the count by orders of magnitude.

The *lemma sequence* of a proof is its lemma forest read in order. For clone detection the simp
lemmas are dropped from it, which leaves what the author chose to apply.

A declaration is *written* when it has a source range of its own. Declarations generated from
another one (`to_additive`, `simps`, structure boilerplate) share its range and are folded into it.

## Metrics

Each metric yields *findings* (a declaration and the evidence) and an *index* (the share of a
library's written theorems with a finding). The letters follow the review angles of the Tau Ceti
rubrics that the metric is evidence for.

### S: size

| | Definition |
|---|---|
| S1 | Source lines of a theorem, statement and proof. Index: median, 90th and 99th percentile; share of theorems over 50 lines (`P2.long_proof`); share of all proof lines that sit in them. |
| S2 | Size of the proof term as a DAG, and length of the lemma sequence. |

Size is a description, not a defect. Generated proofs are longer than hand-shortened ones, and
shortening a proof that works costs far more than finding it did.

### R: reuse

| | Definition |
|---|---|
| R1 `duplicate` | The statement is another theorem's: `exact` (same term up to binder names and universe levels), `inst` (also up to which instances are assumed), `perm` (also up to the order of hypotheses). All three ignore the orientation of `=`, `↔`, `≠`. An instance chosen by hand (a matrix norm) is part of the statement and is not ignored. |
| R3 `wrapper` | The lemma sequence has length one. Descriptive only: see below. |
| R4 `clone` | Another proof applies the same lemmas in the same order: the two lemma sequences (simp lemmas dropped, length at least 8) share at least 5 three-lemma windows, covering at least 60% of the shorter one. |
| R5 `subproof` | The proof contains a tree of at least 5 nested lemma applications that occurs, identically, in one or two other declarations. (A tree that many proofs contain is what a tactic emits.) |
| R6 `replaceable` | (`metrics replace`) One earlier lemma closes the statement, hypotheses discharged from the context: what `exact?` would find. `reproved` when the proof does not use that lemma and has at least two lemma applications of its own; `wrapper` when the proof is that one application. Statements true by reflexivity are excluded. |

### G: generality

How a declaration uses its own binders, followed through calls: a binder handed only to
declarations that ignore it is unused, and a class handed to a declaration that needs less of it
needs no more than that.

| | Definition |
|---|---|
| G1 `unused_hyp` | A hypothesis that neither the statement nor the proof term uses. |
| G2 `unused_class` | A class-typed binder that neither uses. |
| G4 `unused_var` | Any other binder that neither uses. Binders named with a leading underscore are not reported in G1, G2 or G4. |
| G3 `overstrong_class` | A class-typed binder that is only ever consumed at weaker classes, with the `drop`: `normed>algebraic` (a norm is assumed, only algebra is used), `normed>topological`, `topological>algebraic`. A drop within one family (`Preorder` used as `LE`) is recorded but not indexed: Mathlib does it by convention. |

### P: proof quality

| | Definition |
|---|---|
| P1 `dead_have` | The proof term binds a proof (`have h := ...`) that the rest of the term never uses. The unused-variable linter does not see these when a later tactic could have used the hypothesis. |
| P2 `long_proof` | S1 over 50 lines. |

### A: API design

| | Definition |
|---|---|
| A1 `private_general` | A private theorem whose statement mentions no constant declared in its own module (`foreign`), or none of the project (`mathlib`). |
| A2 `misplaced_general` | A public theorem whose statement mentions no constant of the project, in a file not marked as an upstreaming candidate. |
| A3 | Per definition: theorems that state something about it, how many are simp lemmas, users, modules that use it. |
| A4 `unused` / `unreached` | A declaration nobody refers to and no plan names; a declaration no surface declaration depends on, even indirectly. Instances, projections, simp lemmas and lemmas proved by reflexivity are not judged: their uses leave no name in a term. |
| A5 `leak` | (`metrics leak`) Per definition: the theorems whose proofs stop checking when the definition is made irreducible, in its own module and in others. Flagged when another module leaks, or when every user does (three users or more). |
| A7 `repeated_hypothesis` | A quantified hypothesis (a property of a function or a family) that six or more theorems spell out identically, up to the names of variables: a concept without a name. |
| simp | Share of theorems tagged `@[simp]`. |
| H1 | (`analysis/source.py`) Files marked "Upstreaming candidate" that import a module of the library that is not. |

## What the metrics are worth

A metric here is a claim of two kinds, and they are validated differently.

- **The fact.** "This hypothesis is unused", "this lemma closes that statement", "this proof
  unfolds that definition". For G1, G2, G4, P1, R1 `exact`, R6, A4 and A5 the fact is read off the
  compiled term or checked by Lean, and is right by construction up to the stated conventions.
  R4, R5, G3 and A1 are heuristics.
- **The judgement.** Whether the fact is a defect a reviewer would act on. That was measured by
  having independent readers judge 20 random findings per metric (the research report has the
  table). In short:
  - *act on the list* (two in three or better are real): P1, G2, R6 `reproved`, G1, R1;
  - *review the list* (about half): R4, R5, A1 `mathlib`, A7, A5, A2;
  - *an index, not a list* (the fact holds, the individual change is rarely worth making): G3,
    R6 `wrapper`, G4, A4, A1 `foreign`.

Three results of the experiments are worth knowing before using the numbers:

- **A baseline is needed.** Mathlib, measured the same way, is the reference. Several plausible
  metrics do not separate the two libraries at all: one-lemma proofs (R3) are *more* frequent in
  Mathlib, where they are API; a class binder used only through a weaker class of the same family
  is as frequent in Mathlib as here. Those are kept as descriptions and not used as indices.
- **Rates need the right denominator.** Among proofs long enough to compare, clones are as
  frequent in Mathlib as here; per theorem they are six times rarer, because Mathlib's proofs are
  short. The index is per theorem.
- **Exact facts can still be artifacts.** A lambda that ignores its argument is everywhere in
  types (a constant family applied to an index); only when the argument is a proof is it an unused
  step. Each such convention is documented where it is implemented.

## Record format (`dump`)

`consts.tsv`: id, name, kind (`t` theorem, `d` definition, `i` inductive, `c` constructor,
`r` recursor, `a` axiom, `o` opaque), module index, reducibility (`r`, `s`, `x`), flags
(`I` instance, `C` class, `S` structure, `s` simp, `p` private, `x` compiler-generated,
`j` projection, `m` matcher, `g` glue theorem, `D` deprecated).

`decls.N.jsonl`, one object per declaration of the selected modules:

| Field | Meaning |
|---|---|
| `i`, `f` | Constant id; 1 for a full record, 0 for statement hashes only. |
| `l0`, `l1`, `doc` | Source lines; whether it has a doc comment. |
| `h0`, `h1`, `h2` | Statement hashes: exact; instances erased, binders in order; instances erased, order-free. |
| `hc`, `hh`, `hv` | Hash of the conclusion; of each hypothesis; of each variable's type (variables identified by type). |
| `hm` | Per hypothesis: binder index, constant at the head of its conclusion, size, number of its own leading binders. |
| `nb`, `np`, `ch` | Number of binders, of hypotheses; constant at the head of the conclusion. |
| `ts`, `td`, `tc` | Statement: tree size, DAG size, constants. |
| `vs`, `vd`, `dp` | Proof term: tree size (saturating), DAG size, depth. |
| `pl` | How many of the binders the proof term binds itself. |
| `vh` | Hash of the proof term, instances erased. |
| `sk` | Hash and size of the whole lemma forest. |
| `vc` | Constants of the proof term, with the number of distinct sites. |
| `fp` | Lemma trees of size 3 or more: hash and size. |
| `ls` | Lemma sequence (constant ids), up to 4000. |
| `dh` | Number of unused proof bindings. |
| `bh`, `ba` | Constant at the head of the proof term, and its number of arguments. |
| `b` | Per binder: kind (`d`, `i`, `s`, `I`), hypothesis?, class, occurrences in the statement and how many of them as a direct argument, the same two for the proof term (`null` when the term does not bind it), uses of a class-typed binder as `[class consumed at, consumer, argument index, site]`, the constants it is passed to directly as `[constant, argument index]`, and its name. |

## Limits

- The tool sees terms. A proof that is clumsy in source but elaborates to a clean term is clean
  to it, and tactics that produce large terms from one line (`ring`, `linarith`, `norm_num`) make
  term size a poor proxy for effort; source lines (S1) and lemma applications are reported instead.
- `replace` finds what one lemma and `solve_by_elim` close within a budget. A result that needs a
  rewrite to match, or two lemmas, is not found; a statement that ran out of budget is reported as
  such, not as clean.
- `leak` uses the elaborator's `Meta.check`, not the kernel, and reports nothing for a proof that
  does not check as written within the budget. A consumer that rewrites with a `rfl` lemma of the
  definition still counts as unfolding it, because `simp` applies such a lemma by unfolding.
- Uses that leave no name in a term are invisible: the same `rfl` lemmas look unused.
- Mathlib is a baseline, not an ideal: its rates say what a carefully reviewed library looks like
  under the same measurement, deprecated aliases and all.
