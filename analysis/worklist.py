"""Turn the findings of the act-on-the-list metrics into per-cluster worklists for a refactor round.

    python worklist.py DATA_DIR REPO OUT_DIR --replace DIR [--precision DIR ...] [--patches DIR ...]

An item is one declaration with the findings on it and what an editor needs to know before
touching it: whether it is private, which other files use it, whether a plan names it. Items whose
fix stays inside the declaration's own file go to the cluster that owns the file (`local`); items
whose fix needs edits in other files (a public duplicate with outside users, an unused hypothesis
whose callers pass it) go to one `cross` list, to be done after the clusters are merged.
"""
import collections
import glob
import json
import os
import sys

import metrics as M
import report
import semantic as S
from view import PROJECT, View

CLUSTERS = [
    ("convex", ("Numlib.Analysis.Convex",)),
    ("pde", ("Numlib.Analysis.Sobolev", "Numlib.Analysis.PDE", "Numlib.Variational", "Numlib.FiniteElement",
             "Numlib.Geometry")),
    ("matrix", ("Numlib.LinearAlgebra", "Numlib.Analysis.Matrix", "Numlib.Direct", "Numlib.Eigen", "Numlib.Krylov",
                "Numlib.Stationary", "Numlib.Multigrid", "Numlib.FloatingPoint", "Numlib.Projection",
                "Numlib.LinearSolve")),
    ("analysis", ("Numlib.Analysis", "Numlib.MeasureTheory", "Numlib.Topology", "Numlib.Order", "Numlib.Algebra",
                  "Numlib.Data", "Numlib.RingTheory", "Numlib.NumberTheory", "Numlib.Combinatorics",
                  "Numlib.Probability", "Numlib.Logic")),
    ("methods", ("Numlib",)),
]


def cluster_of(module):
    for name, prefixes in CLUSTERS:
        if any(module == p or module.startswith(p + ".") for p in prefixes):
            return name
    return "methods"


def main():
    args = sys.argv[1:]
    data, repo, out = args[0], args[1], args[2]
    replace_dir = args[args.index("--replace") + 1]
    prec_dirs = [args[i + 1] for i, a in enumerate(args) if a == "--precision"]
    patch_dirs = [args[i + 1] for i, a in enumerate(args) if a == "--patches"]
    os.makedirs(out, exist_ok=True)
    v = View(data, repo)
    cs = v.cs
    bd = M.Binders(v)
    libs = ("Numlib",)

    def path(cid):
        return v.mod(cid).replace(".", "/") + ".lean"

    def where(cid):
        if cid in cs.recs and "l0" in cs.recs[cid]:
            return f"{path(cid)}:{cs.recs[cid]['l0']}"
        return cs.mod_name(cid).replace(".", "/") + ".lean"

    # reader verdicts and ready patches, by declaration name
    verdicts = {}
    for d in prec_dirs:
        for p in glob.glob(os.path.join(d, "result-*.json")):
            for it in json.load(open(p, encoding="utf-8"))["items"]:
                verdicts[(it["metric"].split(".")[0], it["decl"])] = (it.get("verdict"), it.get("note"))
    patches = {}
    for d in patch_dirs:
        for p in glob.glob(os.path.join(d, "*.patch")):
            patches[os.path.basename(p)[:-6]] = p.replace("\\", "/")

    # A namespace that names no declaration and is used by one module only (`ExtensionHigher.`)
    # is where nobody looks for a general lemma: of two duplicates, keep the other one.
    ns_mods = collections.defaultdict(set)
    for c in cs.consts:
        if c is not None and "." in c.name:
            ns_mods[c.name.rsplit(".", 1)[0]].add(c.mod)

    def local_ns(x):
        name = v.name(x)
        if "." not in name:
            return False
        ns = name.rsplit(".", 1)[0]
        return ns not in cs.by_name and len(ns_mods.get(ns, ())) <= 1

    items = {}

    def item(cid):
        if cid not in items:
            c = cs.consts[cid]
            users = {u for u in v.users.get(cid, ()) if v.twin_of.get(u, u) != cid and u in cs.recs}
            outside = sorted({path(u) for u in users if cs.consts[u].mod != c.mod})
            items[cid] = {"decl": v.name(cid), "file": path(cid), "line": cs.recs[cid].get("l0"),
                          "end": cs.recs[cid].get("l1"), "private": c.has("p"),
                          "planned": v.is_planned(cid), "users_in_file": sum(1 for u in users if cs.consts[u].mod == c.mod),
                          "used_in_other_files": outside, "findings": []}
        return items[cid]

    def note(metric, cid):
        vd = verdicts.get((metric, v.name(cid)))
        return {"reader_verdict": vd[0], "reader_note": vd[1]} if vd else {}

    # R6 re-proved: the fix keeps the statement, so it is always local
    for f in S.replaceable(v, replace_dir, libs):
        if f["kind"] != "reproved" or f["glue"]:
            continue
        cid = f["cid"]
        e = {"metric": "R6.reproved", "partner": v.name(f["partner"]) if f["partner"] in cs.recs else cs.consts[f["partner"]].name,
             "partner_at": where(f["partner"]), "dir": f["dir"], "cross": False}
        e.update(note("R6", cid))
        if v.name(cid) in patches:
            e["ready_patch"] = patches[v.name(cid)]
        item(cid)["findings"].append(e)

    # R1 duplicates: one finding per pair, on the copy to delete
    seen_pairs = set()
    for f in M.statement_duplicates(v, libs):
        if f.get("alias") or f.get("accessor"):
            continue
        a, b = f["cid"], f["partner"]
        key = tuple(sorted((a, b)))
        if key in seen_pairs:
            continue
        seen_pairs.add(key)
        if v.lib.get(b) not in PROJECT:
            loser, keeper = a, b
        else:
            def rank(x):
                c = cs.consts[x]
                return (c.has("p"), local_ns(x), not v.upstream.get(c.mod, False), c.mod,
                        cs.recs[x].get("l0", 0))
            keeper, loser = sorted((a, b), key=rank)
            if v.lib.get(loser) != "Numlib":
                continue
        it = item(loser)
        keeper_private = keeper in cs.recs and cs.consts[keeper].has("p")
        cross = bool(it["used_in_other_files"]) or (keeper_private and cs.consts[keeper].mod != cs.consts[loser].mod)
        e = {"metric": "R1.duplicate", "strength": f["strength"],
             "keep": v.name(keeper) if keeper in cs.recs else cs.consts[keeper].name, "keep_at": where(keeper),
             "keep_is_private": keeper_private, "cross": cross}
        e.update(note("R1", a))
        e.update({k: x for k, x in note("R1", b).items() if k not in e})
        it["findings"].append(e)

    # G1, G2: unused hypotheses and class binders
    for f in M.binder_findings(v, libs, kinds="td", binders=bd):
        if f["metric"] not in ("G1.unused_hyp", "G2.unused_class"):
            continue
        cid = f["cid"]
        it = item(cid)
        e = {"metric": f["metric"], "binder": f["binder"], "binder_name": f["binder_name"],
             "only_passed_on": not f["direct"]}
        if "cls" in f:
            e["class"] = cs.consts[f["cls"]].name
        # dropping an explicit hypothesis breaks callers in other files; an instance does not
        e["cross"] = f["metric"] == "G1.unused_hyp" and bool(it["used_in_other_files"])
        e.update(note(f["metric"].split(".")[0], cid))
        it["findings"].append(e)

    # ready patches for unused proof steps
    by_name = {v.name(c): c for c in v.written_theorems(libs)}
    for name, p in patches.items():
        base = name.split(".with_")[0]
        if "/P1/" in p and base in by_name and "." + "with_" not in name:
            item(by_name[base])["findings"].append({"metric": "P1.dead_have", "ready_patch": p, "cross": False})

    local = collections.defaultdict(list)
    cross = []
    for cid, it in items.items():
        if not it["findings"]:
            continue
        lo = [f for f in it["findings"] if not f["cross"]]
        cr = [f for f in it["findings"] if f["cross"]]
        if lo:
            local[cluster_of(v.mod(cid))].append(dict(it, findings=lo))
        if cr:
            cross.append(dict(it, findings=cr))
    for name, xs in local.items():
        xs.sort(key=lambda it: (it["file"], it["line"] or 0))
        with open(os.path.join(out, f"local-{name}.json"), "w", encoding="utf-8") as h:
            json.dump(xs, h, indent=1, ensure_ascii=False)
        c = collections.Counter(f["metric"] for it in xs for f in it["findings"])
        print(f"{name:9s} {len(xs):4d} declarations in {len({it['file'] for it in xs}):3d} files  {dict(c)}")
    cross.sort(key=lambda it: (it["file"], it["line"] or 0))
    with open(os.path.join(out, "cross.json"), "w", encoding="utf-8") as h:
        json.dump(cross, h, indent=1, ensure_ascii=False)
    c = collections.Counter(f["metric"] for it in cross for f in it["findings"])
    print(f"{'cross':9s} {len(cross):4d} declarations in {len({it['file'] for it in cross}):3d} files  {dict(c)}")


if __name__ == "__main__":
    main()
