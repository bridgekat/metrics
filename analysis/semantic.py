"""The metrics that come from re-running Lean on each theorem (`metrics replace`, `metrics leak`)
rather than from reading terms: R6 (replaceable by an existing lemma) and A5 (definitional leak).
"""
import collections
import glob
import json
import os

from view import PROJECT


def _rows(d, stem):
    out = []
    for path in sorted(glob.glob(os.path.join(d, stem + ".*.jsonl"))):
        with open(path, encoding="utf-8") as f:
            for line in f:
                try:
                    out.append(json.loads(line))
                except ValueError:
                    pass  # a run that was cut short
    return out


# ---------------------------------------------------------------------------------------------
# R6
# ---------------------------------------------------------------------------------------------

def replaceable(v, d, libs=("Numlib",)):
    """R6. Theorems whose statement one earlier lemma closes (with the hypotheses in context).

    `kind` separates what the hit means:
      `reproved`: the proof does not use that lemma and has two or more lemma applications of its
                  own: an existing result was derived again.
      `wrapper`:  the proof is that lemma, or a single other lemma: a restatement.
      `other`:    the proof uses the lemma among others.
    A statement that holds by reflexivity is not reported: it is a definitional restatement, the
    ordinary shape of an API lemma.
    """
    cs = v.cs
    out = []
    for r in _rows(d, "replace"):
        cid = r["i"]
        if "hit" not in r or cid not in cs.recs or v.lib.get(cid) not in libs or cid not in v.primary:
            continue
        hit = r["hit"]
        rec = cs.recs[cid]
        ls = rec.get("ls", [])
        if hit in ls:
            kind = "wrapper" if len(ls) <= 1 else "other"
        else:
            kind = "reproved" if len(ls) >= 2 else "wrapper"
        out.append({"cid": cid, "metric": "R6.replaceable", "partner": hit, "kind": kind,
                    "dir": r.get("dir", ""), "glue": cs.consts[hit].has("g"),
                    "partner_lib": cs.lib(hit), "lemmas": len(ls), "lines": v.lines(cid)})
    return out


def replace_coverage(v, d, libs=("Numlib",)):
    """How the replaceability run ended, per theorem of `libs`: hit, by reflexivity, no candidate
    worked, or out of budget."""
    cs = v.cs
    c = collections.Counter()
    for r in _rows(d, "replace"):
        if v.lib.get(r["i"]) not in libs or r["i"] not in v.primary:
            continue
        c["hit" if "hit" in r else "rfl" if "rfl" in r else "budget" if "err" in r else "none"] += 1
    return c


# ---------------------------------------------------------------------------------------------
# A5
# ---------------------------------------------------------------------------------------------

def _owner(v, cid):
    """The written declaration an auxiliary theorem belongs to."""
    cs = v.cs
    if cid in v.primary:
        return cid
    if cid in v.twin_of:
        return v.twin_of[cid]
    name = cs.consts[cid].name
    parts = name.split(".")
    for k in range(len(parts) - 1, 0, -1):
        pid = cs.by_name.get(".".join(parts[:k]))
        if pid is not None and pid in v.primary:
            return pid
    return None


def _is_equation_lemma(unit, definition):
    """Whether `unit` is one of the lemmas Lean generates to unfold `definition`."""
    if not unit.startswith(definition + "."):
        return False
    last = unit[len(definition) + 1:]
    return last in ("eq_def", "eq_unfold") or (last.startswith("eq_") and last[3:].isdigit())


def leak_edges(v, d):
    """The outcome of the leak run as edges (theorem, definition, leaks?), auxiliary theorems
    folded into their owners. A definition's own equation lemmas are not edges."""
    cs = v.cs
    edges = {}
    no_control = set()
    for r in _rows(d, "leak"):
        unit = r["i"]
        owner = _owner(v, unit)
        if owner is None:
            continue
        if not r.get("ctl"):
            no_control.add(owner)
            continue
        leaks = set(r.get("leaks", ()))
        uname = cs.consts[unit].name
        for c in r["c"]:
            if c == owner or _is_equation_lemma(uname, cs.consts[c].name):
                continue
            key = (owner, c)
            edges[key] = edges.get(key, False) or (c in leaks)
    return edges, no_control


def leaks(v, d, libs=("Numlib",)):
    """A5. Per definition of `libs`: the theorems that mention it, and those among them whose
    proofs only check when the definition unfolds, in its own module and in others.

    `A5.leak` findings are the definitions with a leak outside their own module, or with no user
    at all that gets by without unfolding (at least three users)."""
    cs = v.cs
    edges, _ = leak_edges(v, d)
    per = collections.defaultdict(lambda: {"same": 0, "same_leak": 0, "cross": 0, "cross_leak": 0, "who": []})
    for (thm, dfn), leak in edges.items():
        if v.lib.get(dfn) not in libs:
            continue
        p = per[dfn]
        side = "same" if cs.consts[thm].mod == cs.consts[dfn].mod else "cross"
        p[side] += 1
        if leak:
            p[side + "_leak"] += 1
            if side == "cross":
                p["who"].append(thm)
    out = []
    for dfn, p in per.items():
        users = p["same"] + p["cross"]
        leaking = p["same_leak"] + p["cross_leak"]
        row = {"cid": dfn, "metric": "A5.leak", "users": users, "leaking": leaking,
               "same": p["same"], "same_leak": p["same_leak"], "cross": p["cross"],
               "cross_leak": p["cross_leak"], "examples": p["who"][:5],
               "flag": p["cross_leak"] > 0 or (users >= 3 and leaking == users)}
        out.append(row)
    return out


def leak_summary(v, d, libs=("Numlib",)):
    """Library indices of A5: the share of (theorem, definition) edges that leak, within a module
    and across modules, and the share of definitions with a cross-module leak."""
    rows = [r for r in leaks(v, d, libs)]
    s = {}
    same = sum(r["same"] for r in rows)
    cross = sum(r["cross"] for r in rows)
    s["defs_with_users"] = len(rows)
    s["edges_same"] = same
    s["edges_cross"] = cross
    s["same_leak_pct"] = 100.0 * sum(r["same_leak"] for r in rows) / same if same else 0.0
    s["cross_leak_pct"] = 100.0 * sum(r["cross_leak"] for r in rows) / cross if cross else 0.0
    s["defs_cross_leak_pct"] = 100.0 * sum(1 for r in rows if r["cross_leak"]) / len(rows) if rows else 0.0
    s["defs_all_users_leak_pct"] = (100.0 * sum(1 for r in rows if r["users"] >= 3 and r["leaking"] == r["users"])
                                    / max(1, sum(1 for r in rows if r["users"] >= 3)))
    return s
