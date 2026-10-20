"""Recall of the metrics on the manual review's findings (`labels.json`).

For each labelled declaration, which metrics fire on it, and whether the one that corresponds to
the label's class does. This is the only ground truth there is, and it is small (one review of ten
files), so read the output as a list of hits and misses rather than as a rate.
"""
import collections
import json
import os
import sys

import metrics as M
import report
import semantic as S
from view import View

# the metric that should catch each class of finding
EXPECT = {
    "duplicate": ("R1.duplicate", "R6.replaceable"),
    "wrapper": ("R3.wrapper", "R6.replaceable"),
    "special_case": ("R6.replaceable",),
    "rederive": (),
    "clone": ("R4.clone", "R5.subproof"),
    "dead": ("A4.unused", "A4.unreached"),
    "overstrong_class": ("G3.overstrong_class",),
    "unused_class": ("G2.unused_class",),
    "unused_binder": ("G4.unused_var", "G2.unused_class"),
    "unused_hyp": ("G1.unused_hyp", "P1.dead_have"),
    "private_general": ("A1.private_general",),
    "api_leak": ("A3.api_leak",),
}


def resolve(v, label):
    cs = v.cs
    out = []
    for cid, r in cs.recs.items():
        if v.mod(cid) != label["module"]:
            continue
        nm = v.name(cid)
        if nm == label["decl"] or nm.endswith("." + label["decl"]):
            out.append(cid)
    # prefer the shortest name: `Foo.bar` over `Foo.bar.baz`
    out.sort(key=lambda c: len(v.name(c)))
    return out[:1]


def all_findings(v, libs=("Numlib",), extra=()):
    fs = []
    fs += M.statement_duplicates(v, libs)
    fs += M.wrappers(v, libs)
    fs += report.with_core(v, M.clones, v, libs, **report.CLONE)
    fs += M.subtree_clones(v, libs)
    fs += M.binder_findings(v, libs)
    fs += M.dead_steps(v, libs)
    fs += M.private_general(v, libs)
    fs += M.unused_declarations(v, libs)
    fs += list(extra)
    return fs


def validate(v, findings, labels_path=None):
    labels_path = labels_path or os.path.join(os.path.dirname(__file__), "labels.json")
    labels = json.load(open(labels_path, encoding="utf-8"))["labels"]
    by_cid = collections.defaultdict(list)
    for f in findings:
        by_cid[f["cid"]].append(f)
    rows = []
    for lb in labels:
        ids = resolve(v, lb)
        if not ids:
            rows.append((lb, None, [], False))
            continue
        cid = ids[0]
        fired = by_cid.get(cid, [])
        want = EXPECT.get(lb["kind"], ())
        hit = [f for f in fired if f["metric"] in want]
        partner_ok = None
        if hit and lb.get("partner"):
            partner_ok = any("partner" in f and v.name(f["partner"]).endswith(lb["partner"].split(".")[-1])
                             for f in hit)
        rows.append((lb, cid, fired, bool(hit), partner_ok))
    return rows


def print_report(v, rows):
    per = collections.defaultdict(lambda: [0, 0])
    for row in rows:
        lb, cid, fired, hit = row[:4]
        partner_ok = row[4] if len(row) > 4 else None
        tag = "HIT " if hit else ("n/a " if not EXPECT.get(lb["kind"]) else "MISS")
        if cid is None:
            tag = "??? "
        if EXPECT.get(lb["kind"]) and cid is not None:
            per[lb["kind"]][1] += 1
            per[lb["kind"]][0] += int(hit)
        extra = ""
        if partner_ok is not None:
            extra = " (named partner found)" if partner_ok else " (other partner)"
        print(f"{tag} {lb['kind']:17s} {lb['decl'][:58]:58s} {sorted({f['metric'] for f in fired})}{extra}")
    print()
    for k, (h, n) in sorted(per.items()):
        print(f"  {k:18s} {h}/{n}")
    print(f"  {'total':18s} {sum(h for h, _ in per.values())}/{sum(n for _, n in per.values())}")


if __name__ == "__main__":
    args = sys.argv[1:]
    v = View(args[0], args[1])
    report.drop_simp_view(v)
    extra = []
    if "--replace" in args:
        extra += [f for f in S.replaceable(v, args[args.index("--replace") + 1]) if not f["glue"]]
    if "--leak" in args:
        extra += [dict(r, metric="A3.api_leak") for r in S.leaks(v, args[args.index("--leak") + 1]) if r["flag"]]
    print_report(v, validate(v, all_findings(v, extra=extra)))
