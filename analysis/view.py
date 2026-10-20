"""The working view of a dump: which records are hand-written declarations, who uses whom, and
the source-side facts (plans, file headers) the term-level records do not carry."""
import collections
import os
import re

from load import load, user_name

PROJECT = ("Numlib", "NumlibSurface")


class View:
    def __init__(self, data_dir, repo=None):
        self.cs = cs = load(data_dir)
        self.repo = repo
        consts = cs.consts
        self.lib = {}        # cid -> library, for records
        for cid in cs.recs:
            self.lib[cid] = cs.lib(cid)
        # A declaration is *written* when it has a source range of its own. Declarations generated
        # from another one (`to_additive`, `simps`, structure boilerplate) share that one's range:
        # per range, the first definition (else the first name) is the primary, the rest are twins.
        by_range = collections.defaultdict(list)
        for cid, r in cs.recs.items():
            if "l0" in r:
                by_range[(consts[cid].mod, r["l0"], r["l1"])].append(cid)
        self.primary = set()
        self.twin_of = {}
        for key, ids in by_range.items():
            ids.sort(key=lambda i: (consts[i].kind != "d", consts[i].kind in "cr", len(consts[i].name), consts[i].name))
            self.primary.add(ids[0])
            for i in ids[1:]:
                self.twin_of[i] = ids[0]
        # who refers to whom, among full records
        self.uses = {}
        self.users = collections.defaultdict(set)
        self.stmt_users = collections.defaultdict(set)
        for cid, r in cs.recs.items():
            if not r.get("f"):
                continue
            us = set(r.get("tc", ()))
            for k in us:
                self.stmt_users[k].add(cid)
            us.update(k for k, _ in r.get("vc", ()))
            us.discard(cid)
            self.uses[cid] = us
            for k in us:
                self.users[k].add(cid)
        self.planned = set()
        self.upstream = {}
        if repo:
            self._read_repo(repo)

    # -- source-side facts ------------------------------------------------------------------
    def _read_repo(self, repo):
        for base, _, files in os.walk(os.path.join(repo, "plans")):
            for f in files:
                if f.endswith(".toml"):
                    with open(os.path.join(base, f), encoding="utf-8") as h:
                        text = h.read()
                    # ids are relative to the plan's namespace unless written with _root_
                    ns = re.search(r'^namespace\s*=\s*"([^"]*)"', text, re.M)
                    ns = ns.group(1) + "." if ns and ns.group(1) else ""
                    for m in re.finditer(r'^id\s*=\s*"([^"]+)"', text, re.M):
                        i = m.group(1)
                        self.planned.add(i[7:] if i.startswith("_root_.") else ns + i)
        for mi, m in enumerate(self.cs.modules):
            if m.split(".", 1)[0] in PROJECT:
                path = os.path.join(repo, *m.split(".")) + ".lean"
                if os.path.exists(path):
                    with open(path, encoding="utf-8") as h:
                        self.upstream[mi] = "Upstreaming candidate" in h.read(4000)

    # -- predicates --------------------------------------------------------------------------
    def name(self, cid):
        return user_name(self.cs.consts[cid].name)

    def mod(self, cid):
        return self.cs.modules[self.cs.consts[cid].mod]

    def is_written(self, cid):
        return cid in self.primary

    def is_thm(self, cid):
        return self.cs.consts[cid].kind == "t"

    def written_theorems(self, libs):
        """Hand-written theorems with a proof term on record."""
        cs = self.cs
        return [cid for cid, r in cs.recs.items()
                if cid in self.primary and cs.consts[cid].kind == "t" and self.lib[cid] in libs
                and r.get("f") and "vd" in r]

    def written_defs(self, libs):
        cs = self.cs
        return [cid for cid, r in cs.recs.items()
                if cid in self.primary and cs.consts[cid].kind == "d" and self.lib[cid] in libs
                and r.get("f")]

    def lines(self, cid):
        r = self.cs.recs[cid]
        return r["l1"] - r["l0"] + 1

    def loc(self, cid):
        r = self.cs.recs[cid]
        return f"{self.mod(cid).replace('.', '/')}.lean:{r.get('l0', '?')}"

    def is_planned(self, cid):
        return self.name(cid) in self.planned or self.cs.consts[cid].name in self.planned


def quantiles(xs, ps=(0.5, 0.9, 0.99)):
    xs = sorted(xs)
    if not xs:
        return [None] * len(ps)
    return [xs[min(len(xs) - 1, int(p * len(xs)))] for p in ps]


def pct(a, b):
    return 100.0 * a / b if b else 0.0
