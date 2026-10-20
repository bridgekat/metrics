"""Print the comparison tables of a report as Markdown.

    python tables.py OUT_DIR/summary.json
"""
import json
import sys

sys.stdout.reconfigure(encoding="utf-8")

ROWS = [
    ("P2.long_proof", "Proofs over 50 lines"),
    ("P1.dead_have", "Proofs with an unused step"),
    ("G1.unused_hyp", "Unused hypothesis"),
    ("G2.unused_class", "Unused class binder"),
    ("G4.unused_var", "Unused variable"),
    ("G3.normed>algebraic", "Norm assumed, algebra used"),
    ("G3.normed>topological", "Norm assumed, topology used"),
    ("G3.topological>algebraic", "Topology assumed, algebra used"),
    ("R4.clone", "Proof is a clone of another"),
    ("R4.clone_cross_module", "... of a proof in another file"),
    ("R5.subproof", "Shares a subproof with another"),
    ("R1.duplicate", "Statement duplicates another"),
    ("R1.duplicate_exact", "... exactly"),
    ("R6.reproved", "Re-proves an earlier lemma"),
    ("R6.wrapper", "Restates an earlier lemma"),
    ("R3.wrapper", "One-lemma proof"),
    ("private", "Private theorems"),
    ("A1.private_general", "Private, not about its own file"),
    ("A2.misplaced_general", "Public Mathlib-level lemma in a domain file"),
    ("A4.unused", "Referred to by nothing, unplanned"),
    ("simp", "Tagged simp"),
]


def cell(s, lib, k):
    x = s[lib]["indices"].get(k)
    if x is None:
        return "–"
    return f"{x['pct']:.2f}% [{x['lo']:.2f}, {x['hi']:.2f}]"


def main():
    s = json.load(open(sys.argv[1], encoding="utf-8"))
    libs = [l for l in ("Numlib", "NumlibSurface", "Mathlib") if l in s]
    print("| | " + " | ".join(libs) + " |")
    print("|---|" + "---|" * len(libs))
    for k, label in (("theorems", "Written theorems"), ("definitions", "Written definitions"),
                     ("modules", "Modules")):
        print(f"| {label} | " + " | ".join(str(s[l]["sizes"][k]) for l in libs) + " |")
    for k, label in (("lines", "Lines per theorem"), ("lemmas", "Lemma applications per proof"),
                     ("dag", "Proof term size (DAG nodes)")):
        print(f"| {label}: median / 90th / 99th | " + " | ".join(
            f"{s[l]['sizes'][k + '_p50']} / {s[l]['sizes'][k + '_p90']} / {s[l]['sizes'][k + '_p99']}" for l in libs) + " |")
    print("| Share of proof lines in proofs over 50 lines | " + " | ".join(
        f"{s[l]['sizes']['long_proof_line_share_pct']:.1f}%" for l in libs) + " |")
    print()
    print("| Share of written theorems | " + " | ".join(libs) + " |")
    print("|---|" + "---|" * len(libs))
    for k, label in ROWS:
        if any(k in s[l]["indices"] for l in libs):
            print(f"| {label} (`{k}`) | " + " | ".join(cell(s, l, k) for l in libs) + " |")
    for l in libs:
        for k in ("replace_coverage", "leak", "repeated_hypotheses"):
            if s[l].get(k):
                print(f"\n{l} {k}: {s[l][k]}")


if __name__ == "__main__":
    main()
