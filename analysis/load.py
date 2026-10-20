"""Load a `metrics dump` directory into plain Python structures.

Everything downstream works on `Dump`: the table of constants (`consts`), the per-declaration
records (`recs`, keyed by constant id), and the fold of compiler-generated auxiliary constants into
the user declaration they belong to (`parent`).
"""
import glob
import json
import os
import sys
from dataclasses import dataclass, field

sys.stdout.reconfigure(encoding="utf-8")


@dataclass
class Const:
    id: int
    name: str
    kind: str      # t theorem, d definition, o opaque, a axiom, i inductive, c constructor, r recursor, q quot
    mod: int
    red: str       # r reducible, s semireducible, x irreducible
    flags: str     # I instance, C class, S structure, s simp, p private, x internal, j projection, m matcher, g glue

    def has(self, f):
        return f in self.flags


@dataclass
class Dump:
    modules: list
    consts: list
    recs: dict
    by_name: dict = field(default_factory=dict)
    parent: dict = field(default_factory=dict)

    def mod_name(self, cid):
        return self.modules[self.consts[cid].mod]

    def name(self, cid):
        return self.consts[cid].name

    def lib(self, cid):
        """The library a constant belongs to: the first component of its module name."""
        return self.modules[self.consts[cid].mod].split(".", 1)[0]


def user_name(name):
    """A private name without its `_private.<module>.0.` prefix."""
    if name.startswith("_private."):
        i = name.find(".0.")
        if i >= 0:
            return name[i + 3:]
    return name


def load(d):
    modules = []
    with open(os.path.join(d, "modules.tsv"), encoding="utf-8") as f:
        for line in f:
            modules.append(line.rstrip("\n").split("\t")[1])
    consts = []
    by_name = {}
    with open(os.path.join(d, "consts.tsv"), encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            c = Const(int(p[0]), p[1], p[2], int(p[3]), p[4], p[5] if len(p) > 5 else "")
            consts.append(c)
            by_name[c.name] = c.id
    recs = {}
    for path in sorted(glob.glob(os.path.join(d, "decls.*.jsonl"))):
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                recs[r["i"]] = r
    cs = Dump(modules, consts, recs, by_name)
    # Auxiliary constants (`foo._proof_1`, `foo.match_1`, `foo._simp_3`, ...) belong to the nearest
    # enclosing name that is a constant and is not itself internal.
    for cid, r in recs.items():
        c = consts[cid]
        if not c.has("x"):
            continue
        parts = c.name.split(".")
        for k in range(len(parts) - 1, 0, -1):
            pid = by_name.get(".".join(parts[:k]))
            if pid is not None and not consts[pid].has("x") and consts[pid].mod == c.mod:
                cs.parent[cid] = pid
                break
    return cs


if __name__ == "__main__":
    cs = load(sys.argv[1])
    print(len(cs.modules), "modules,", len(cs.consts), "constants,", len(cs.recs), "records,",
          len(cs.parent), "auxiliaries with a parent")
