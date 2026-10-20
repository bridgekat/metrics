"""Tabulate the precision checks: one row per worksheet with a result file.

    python precision.py PRECISION_DIR [PRECISION_DIR/round2 ...]
"""
import collections
import glob
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8")


def table(d):
    rows = []
    for path in sorted(glob.glob(os.path.join(d, "result-*.json"))):
        with open(path, encoding="utf-8") as h:
            data = json.load(h)
        c = collections.Counter((it.get("verdict") or "missing") for it in data["items"])
        n = len(data["items"])
        rows.append((data.get("metric", os.path.basename(path)), data.get("population"), n,
                     c["confirmed"], c["benign"], c["wrong"], c["unsure"] + c["missing"]))
    return rows


if __name__ == "__main__":
    for d in sys.argv[1:]:
        print(f"## {d}")
        print("| Metric | Findings | Sampled | Confirmed | Benign | Wrong | Unsure |")
        print("|---|---|---|---|---|---|---|")
        for m, pop, n, a, b, w, u in table(d):
            print(f"| {m} | {pop} | {n} | {a} | {b} | {w} | {u} |")
