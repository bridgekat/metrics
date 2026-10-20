"""Draw a random sample of findings per metric, as worksheets for a precision check.

    python sample.py FINDINGS.jsonl OUT_DIR [--n 20] [--seed 202610] [--only R4.clone,R5.subproof]

Each worksheet is a JSON list of items: an id, where the declaration is, the evidence, and the
claim in words. A checker fills in `verdict` and `note` for each (see the report for the protocol).
"""
import collections
import json
import os
import random
import sys


def key_of(f):
    m = f["metric"]
    if m == "G3.overstrong_class":
        return "G3." + f["drop"]
    if m == "R6.replaceable":
        return "R6." + f["kind"]
    if m == "A1.private_general":
        return "A1." + f["scope"]
    return m


def claim(f):
    m = f["metric"]
    d = f["decl"]
    if m == "R1.duplicate":
        return f"The statement of {d} is the statement of {f['partner']} ({f['partner_at']}), strength '{f['strength']}'."
    if m == "R4.clone":
        return (f"The proof of {d} applies the same lemmas in the same order as the proof of {f['partner']} "
                f"({f['partner_at']}): {f['shared']} shared three-lemma windows, {int(100 * f['contain'])}% of the shorter proof.")
    if m == "R5.subproof":
        return (f"The proof of {d} contains a subproof (a tree of {f['size']} nested lemma applications) that also "
                f"occurs, identically, in {f['partner']} ({f['partner_at']}), and in {f['n_decls']} declarations in all.")
    if m == "R6.replaceable":
        via = f" (direction {f['dir']})" if f.get("dir") else ""
        return (f"The statement of {d} is closed by one application of the earlier lemma {f['partner']} ({f['partner_at']}){via}, "
                f"hypotheses taken from the context; kind '{f['kind']}', the written proof applies {f['lemmas']} lemmas over {f['lines']} lines.")
    if m == "G1.unused_hyp":
        return f"Hypothesis '{f.get('binder_name', '#' + str(f['binder']))}' of {d} is used neither by the statement nor by the proof term" + ("" if f["direct"] else " (it is only passed to declarations that ignore it)") + "."
    if m == "G2.unused_class":
        return f"The class binder [{f['cls']}] (binder '{f.get('binder_name', '#' + str(f['binder']))}') of {d} is used neither by the statement nor by the proof term" + ("" if f["direct"] else " (it is only passed to declarations that ignore it)") + "."
    if m == "G4.unused_var":
        return f"Binder '{f.get('binder_name', '#' + str(f['binder']))}' of {d} is used neither by the statement nor by the proof term" + ("" if f["direct"] else " (it is only passed to declarations that ignore it)") + "."
    if m == "G3.overstrong_class":
        return (f"{d} assumes [{f['cls']}] (binder '{f.get('binder_name', '#' + str(f['binder']))}') but statement and proof only ever use it as: "
                f"{', '.join(f['needs'][:8])}. Drop: {f['drop']}.")
    if m == "P1.dead_have":
        return f"The proof of {d} contains {f['count']} intermediate proof step(s) (a `have`, or the like) whose result the rest of the proof term never uses."
    if m == "A1.private_general":
        scope = "no constant of this project at all" if f["scope"] == "mathlib" else "no constant declared in its own file"
        return f"{d} is private, and its statement mentions {scope}."
    if m == "A2.misplaced_general":
        return f"{d} is public, its statement mentions only Mathlib constants, and its file is not marked as an upstreaming candidate."
    if m == "A4.unused":
        return f"No other declaration of the project (backbone or surface) refers to {d}, and no plan names it."
    if m == "A5.leak":
        return (f"Of the {f['users']} theorems that mention the definition {d}, {f['leaking']} have proofs that only check when it "
                f"unfolds ({f['cross_leak']} of {f['cross']} in other modules, {f['same_leak']} of {f['same']} in its own). "
                f"Examples in other modules: {', '.join(f.get('examples', [])[:4]) or 'none'}.")
    return m


def main():
    args = sys.argv[1:]
    src, out = args[0], args[1]
    n = int(args[args.index("--n") + 1]) if "--n" in args else 20
    seed = int(args[args.index("--seed") + 1]) if "--seed" in args else 202610
    only = set(args[args.index("--only") + 1].split(",")) if "--only" in args else None
    max_lines = int(args[args.index("--max-lines") + 1]) if "--max-lines" in args else None
    os.makedirs(out, exist_ok=True)
    groups = collections.defaultdict(list)
    with open(src, encoding="utf-8") as h:
        for line in h:
            f = json.loads(line)
            k = key_of(f)
            if only and k not in only:
                continue
            if f.get("line") is None:
                continue
            if max_lines and f["end"] - f["line"] + 1 > max_lines:
                continue
            groups[k].append(f)
    rng = random.Random(seed)
    for k, fs in sorted(groups.items()):
        # one finding per declaration, so that a sample is n declarations
        by_decl = {}
        for f in fs:
            by_decl.setdefault((f["module"], f["decl"]), f)
        pool = sorted(by_decl.values(), key=lambda f: (f["module"], f["decl"]))
        pick = rng.sample(pool, min(n, len(pool)))
        items = []
        for j, f in enumerate(pick):
            items.append({
                "id": f"{k}#{j + 1}", "metric": k, "decl": f["decl"],
                "file": f["module"].replace(".", "/") + ".lean", "line": f["line"], "end": f["end"],
                "claim": claim(f),
                "evidence": {x: y for x, y in f.items() if x not in ("metric", "decl", "module", "line", "end")},
                "verdict": None, "note": None})
        path = os.path.join(out, f"worksheet-{k.replace('>', '-to-').replace('.', '-')}.json")
        with open(path, "w", encoding="utf-8") as h:
            json.dump({"metric": k, "population": len(pool), "seed": seed, "items": items}, h, indent=1, ensure_ascii=False)
        print(f"{k}: {len(pick)} of {len(pool)} -> {path}")


if __name__ == "__main__":
    main()
