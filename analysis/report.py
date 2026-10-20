"""Compute every metric and write the results.

    python report.py DATA_DIR REPO OUT_DIR [--replace DIR] [--leak DIR]

Writes to OUT_DIR:
  summary.json    the library-level indices of the backbone, the surface and the Mathlib sample,
                  each with a bootstrap interval over modules
  findings.jsonl  every finding on a backbone declaration: metric, declaration, file, line, evidence
  files.csv       per backbone module: size and the number of findings of each metric
  defs.csv        per backbone definition: its API (lemmas, simp lemmas, users, leaks)
"""
import collections
import csv
import json
import os
import random
import sys

import metrics as M
import semantic as S
from view import View, pct, quantiles

CLONE = dict(min_len=8, min_shared=5, min_contain=0.6)


def drop_simp_view(v):
    """Lemma sequences without simp lemmas: what is left is what the author chose to apply."""
    cs = v.cs
    for r in cs.recs.values():
        if "ls" in r and "ls_all" not in r:
            r["ls_all"] = r["ls"]
            r["ls_core"] = [k for k in r["ls"] if not cs.consts[k].has("s")]


def with_core(v, fn, *a, **kw):
    """Run a metric on the simp-free lemma sequences."""
    cs = v.cs
    for r in cs.recs.values():
        if "ls_core" in r:
            r["ls"] = r["ls_core"]
    try:
        return fn(*a, **kw)
    finally:
        for r in cs.recs.values():
            if "ls_all" in r:
                r["ls"] = r["ls_all"]


def all_findings(v, libs, replace_dir=None, leak_dir=None, binders=None, pool_dups=("Numlib", "Mathlib")):
    fs = []
    fs += M.statement_duplicates(v, libs, pool=pool_dups if libs != ("Mathlib",) else ("Mathlib",))
    fs += M.wrappers(v, libs)
    fs += with_core(v, M.clones, v, libs, **CLONE)
    fs += M.subtree_clones(v, libs)
    fs += M.binder_findings(v, libs, binders=binders)
    fs += M.dead_steps(v, libs)
    fs += M.long_proofs(v, libs)
    fs += M.private_general(v, libs)
    if libs != ("Mathlib",):
        fs += M.misplaced_general(v, libs)
        fs += M.unused_declarations(v, libs)
    if replace_dir:
        fs += [f for f in S.replaceable(v, replace_dir, libs) if not f["glue"]]
    return fs


def flag_names(f):
    """The index or indices a finding counts toward."""
    m = f["metric"]
    out = [m]
    if m == "G3.overstrong_class":
        out = ["G3." + f["drop"]] if f["drop"] != "same" else []
    elif m == "R6.replaceable":
        out = ["R6." + f["kind"]]
    elif m == "R1.duplicate":
        out = ["R1.alias"] if f.get("alias") else ["R1.accessor"] if f.get("accessor") else ["R1.duplicate", "R1.duplicate_" + f["strength"]]
    elif m == "R4.clone" and not f["same_module"]:
        out = ["R4.clone", "R4.clone_cross_module"]
    elif m == "A1.private_general":
        out = ["A1.private_general"] + (["A1.private_mathlib_only"] if f["scope"] == "mathlib" else [])
    elif m == "A4.unreached":
        out = ["A4.unreached"]
    return out


def indices(v, libs, findings, tested=None):
    """Rates over the written theorems of `libs`, with a 90% bootstrap interval over modules."""
    cs = v.cs
    th = v.written_theorems(libs)
    thset = set(th)
    flags = collections.defaultdict(set)
    for f in findings:
        if f["cid"] in thset:
            for k in flag_names(f):
                flags[k].add(f["cid"])
    for c in th:
        if cs.consts[c].has("p"):
            flags["private"].add(c)
        if cs.consts[c].has("s"):
            flags["simp"].add(c)
    by_mod = collections.defaultdict(list)
    for c in th:
        by_mod[cs.consts[c].mod].append(c)
    mods = sorted(by_mod)
    rng = random.Random(202610)
    out = {}
    for k, ids in sorted(flags.items()):
        # R6 is a rate over the theorems the run actually tested
        base = th if not (k.startswith("R6.") and tested is not None) else [c for c in th if c in tested]
        if not base:
            continue
        baseset = set(base)
        per_mod = {m: (sum(1 for c in by_mod[m] if c in ids and c in baseset),
                       sum(1 for c in by_mod[m] if c in baseset)) for m in mods}
        point = pct(sum(a for a, _ in per_mod.values()), sum(b for _, b in per_mod.values()))
        boots = []
        for _ in range(300):
            a = b = 0
            for _ in mods:
                x, y = per_mod[mods[rng.randrange(len(mods))]]
                a += x
                b += y
            boots.append(pct(a, b))
        boots.sort()
        out[k] = {"pct": round(point, 3), "lo": round(boots[15], 3), "hi": round(boots[284], 3),
                  "count": len(ids & baseset), "of": len(base)}
    return out


def sizes(v, libs):
    cs = v.cs
    th = v.written_theorems(libs)
    lines = [v.lines(c) for c in th]
    s = {"theorems": len(th), "definitions": len(v.written_defs(libs)), "modules": len({cs.consts[c].mod for c in th})}
    s["lines_p50"], s["lines_p90"], s["lines_p99"] = quantiles(lines)
    s["dag_p50"], s["dag_p90"], s["dag_p99"] = quantiles([cs.recs[c]["vd"] for c in th])
    s["lemmas_p50"], s["lemmas_p90"], s["lemmas_p99"] = quantiles([len(cs.recs[c]["ls"]) for c in th])
    s["proof_lines"] = sum(lines)
    s["long_proof_line_share_pct"] = round(pct(sum(x for x in lines if x > 50), sum(lines)), 2)
    return s


def main():
    args = sys.argv[1:]
    data, repo, out = args[0], args[1], args[2]
    replace_dir = args[args.index("--replace") + 1] if "--replace" in args else None
    leak_dir = args[args.index("--leak") + 1] if "--leak" in args else None
    os.makedirs(out, exist_ok=True)
    v = View(data, repo)
    cs = v.cs
    drop_simp_view(v)
    bd = M.Binders(v)
    tested = None
    if replace_dir:
        tested = {r["i"] for r in S._rows(replace_dir, "replace") if "err" not in r}
    summary = {}
    found = {}
    for libs in (("Numlib",), ("NumlibSurface",), ("Mathlib",)):
        fs = all_findings(v, libs, replace_dir, leak_dir, bd)
        found[libs[0]] = fs
        summary[libs[0]] = {"sizes": sizes(v, libs), "indices": indices(v, libs, fs, tested)}
        if replace_dir:
            summary[libs[0]]["replace_coverage"] = dict(S.replace_coverage(v, replace_dir, libs))
        if leak_dir:
            summary[libs[0]]["leak"] = S.leak_summary(v, leak_dir, libs)
    # A7 is per hypothesis, not per theorem: its index is the share of theorems carrying one
    bundles = {}
    for libs in (("Numlib",), ("NumlibSurface",), ("Mathlib",)):
        rows = M.repeated_hypotheses(v, libs)
        bundles[libs[0]] = rows
        carriers = {c for f in rows for c in f["carriers"]}
        n = summary[libs[0]]["sizes"]["theorems"]
        summary[libs[0]]["repeated_hypotheses"] = {
            "hypotheses": len(rows), "theorems_carrying_one": len(carriers),
            "pct": round(pct(len(carriers), n), 3)}
    with open(os.path.join(out, "summary.json"), "w", encoding="utf-8") as h:
        json.dump(summary, h, indent=1)

    # findings on the backbone
    fs = found["Numlib"]
    leak_rows = S.leaks(v, leak_dir, ("Numlib",)) if leak_dir else []
    fs = fs + [dict(r, metric="A5.leak") for r in leak_rows if r["flag"]]
    fs = fs + [{k: x for k, x in f.items() if k != "carriers"} for f in bundles["Numlib"]]
    with open(os.path.join(out, "findings.jsonl"), "w", encoding="utf-8") as h:
        for f in fs:
            cid = f["cid"]
            row = {"metric": f["metric"], "decl": v.name(cid), "module": v.mod(cid),
                   "line": cs.recs[cid].get("l0"), "end": cs.recs[cid].get("l1")}
            for k, x in f.items():
                if k in ("cid", "metric"):
                    continue
                if k == "partner":
                    row["partner"] = v.name(x)
                    row["partner_at"] = v.loc(x) if x in cs.recs and "l0" in cs.recs[x] else cs.mod_name(x)
                elif k in ("cls",):
                    row[k] = cs.consts[x].name
                elif k in ("needs", "examples"):
                    row[k] = [v.name(i) if i in cs.recs else cs.consts[i].name for i in x]
                else:
                    row[k] = x
            h.write(json.dumps(row, ensure_ascii=False) + "\n")

    # per module
    # per module: the number of declarations with a finding of each kind
    seen = collections.defaultdict(set)
    for f in fs:
        for k in flag_names(f) or [f["metric"]]:
            seen[(cs.consts[f["cid"]].mod, k)].add(f["cid"])
    per = collections.defaultdict(collections.Counter)
    for (mi, k), ids in seen.items():
        per[mi][k] = len(ids)
    cols = sorted({k for c in per.values() for k in c})
    th_by_mod = collections.Counter(cs.consts[c].mod for c in v.written_theorems(("Numlib",)))
    lines_by_mod = collections.Counter()
    for c in v.written_theorems(("Numlib",)):
        lines_by_mod[cs.consts[c].mod] += v.lines(c)
    with open(os.path.join(out, "files.csv"), "w", encoding="utf-8", newline="") as h:
        w = csv.writer(h)
        w.writerow(["module", "upstreaming_candidate", "theorems", "proof_lines"] + cols)
        for mi in sorted(th_by_mod, key=lambda m: cs.modules[m]):
            w.writerow([cs.modules[mi], int(bool(v.upstream.get(mi))), th_by_mod[mi], lines_by_mod[mi]]
                       + [per[mi][k] for k in cols])

    # per definition
    leak_by = {r["cid"]: r for r in leak_rows}
    with open(os.path.join(out, "defs.csv"), "w", encoding="utf-8", newline="") as h:
        w = csv.writer(h)
        w.writerow(["definition", "module", "line", "lemmas", "own_lemmas", "simp", "users", "ext_modules",
                    "unfold_modules", "checked_users", "leaking_users", "cross_users", "cross_leaks"])
        for r in M.definition_api(v, ("Numlib",)):
            cid = r["cid"]
            lk = leak_by.get(cid, {})
            w.writerow([v.name(cid), v.mod(cid), cs.recs[cid].get("l0"), r["lemmas"], r["own_lemmas"], r["simp"],
                        r["users"], r["ext_modules"], r["unfold_modules"], lk.get("users", ""),
                        lk.get("leaking", ""), lk.get("cross", ""), lk.get("cross_leak", "")])
    print("wrote", out)
    for lib, s in summary.items():
        print("==", lib, s["sizes"])
        for k, x in s["indices"].items():
            print(f"   {k:28s} {x['pct']:7.2f}%  [{x['lo']:.2f}, {x['hi']:.2f}]  {x['count']}/{x['of']}")
        for k in ("replace_coverage", "leak", "repeated_hypotheses"):
            if k in s:
                print("  ", k, s[k])


if __name__ == "__main__":
    main()
