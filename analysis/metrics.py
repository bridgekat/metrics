"""The metrics, computed from a `View`.

Every function returns *findings*: dicts with at least `cid` (the declaration), `metric`, and the
evidence the report prints. A finding is a pointer for a reviewer, not a verdict; README.md gives
each metric's definition, what it is evidence of, and its measured precision.
"""
import collections
import math

from view import PROJECT, pct, quantiles

# ---------------------------------------------------------------------------------------------
# R: reuse
# ---------------------------------------------------------------------------------------------


def is_alias_of(cs, a, b):
    """Whether `a` was declared as an alias of `b`: its proof term is the bare constant `b`."""
    r = cs.recs.get(a, {})
    return r.get("pl") == 0 and r.get("ba") == 0 and r.get("bh") == b


def statement_duplicates(v, libs=("Numlib",), pool=("Numlib", "Mathlib")):
    """R1. Theorems of `libs` whose statement is another theorem's, in three strengths:
    `exact` (same term up to binder names and universe levels), `inst` (also up to which
    instance arguments are assumed), `perm` (also up to the order of the hypotheses)."""
    cs = v.cs
    groups = {"h0": collections.defaultdict(list), "h1": collections.defaultdict(list),
              "h2": collections.defaultdict(list)}
    for cid, r in cs.recs.items():
        # a partner may be a generated declaration (the additive twin of a to_additive lemma)
        if "l0" not in r or cs.consts[cid].kind != "t" or v.lib[cid] not in pool:
            continue
        if cs.consts[cid].has("D"):
            continue  # a deprecated alias is a duplicate on its way out
        if "ch" in r and cs.consts[r["ch"]].has("C"):
            continue  # an instance in theorem form: found by resolution, not by its statement
        for k in groups:
            groups[k][r[k]].append(cid)
    out = []
    for cid, r in cs.recs.items():
        if cid not in v.primary or cs.consts[cid].kind != "t" or v.lib[cid] not in libs:
            continue
        if cs.consts[cid].has("D") or ("ch" in r and cs.consts[r["ch"]].has("C")):
            continue
        if cs.consts[cid].has("j"):
            continue  # a structure field: the restatement, if any, is reported as the accessor
        # declared with the alias command: the proof term is the bare constant
        alias = r.get("pl") == 0 and r.get("ba") == 0 and "bh" in r
        for k, strength in (("h0", "exact"), ("h1", "inst"), ("h2", "perm")):
            others = [o for o in groups[k][r[k]] if o != cid and v.twin_of.get(o) != cid
                      and not is_alias_of(cs, o, cid)]
            if others:
                # prefer a partner outside the project, then outside the module
                others.sort(key=lambda o: (v.lib[o] in PROJECT, cs.consts[o].mod == cs.consts[cid].mod, o))
                # a root-level restatement of a class field (`mul_comm` of `CommMagma.mul_comm`)
                # is how a field is exported, not a second proof
                accessor = all(cs.consts[o].has("j") for o in others)
                out.append({"cid": cid, "metric": "R1.duplicate", "strength": strength,
                            "partner": others[0], "n_partners": len(others), "alias": alias,
                            "accessor": accessor})
                break
    return out


def wrappers(v, libs=("Numlib",), max_dag_ratio=None):
    """R3. Theorems whose proof is one lemma application: the lemma sequence has length one and
    the body's head is that lemma (possibly under glue such as `Iff.mpr`)."""
    cs = v.cs
    out = []
    for cid in v.written_theorems(libs):
        r = cs.recs[cid]
        if len(r["ls"]) != 1:
            continue
        lem = r["ls"][0]
        out.append({"cid": cid, "metric": "R3.wrapper", "partner": lem,
                    "direct": r.get("bh") == lem, "vd": r["vd"], "td": r["td"],
                    "partner_lib": cs.lib(lem)})
    return out


def shingles(ls, k):
    return {tuple(ls[i:i + k]) for i in range(len(ls) - k + 1)}


def clones(v, libs=("Numlib",), pool=None, k=3, min_len=6, min_shared=4, min_contain=0.5,
           max_df=40):
    """R4. Pairs of proofs that apply the same lemmas in the same order: the lemma sequences share
    at least `min_shared` `k`-shingles, covering `min_contain` of the shorter one. Shingles
    weigh by rarity; one that more than `max_df` proofs contain proposes no pair."""
    cs = v.cs
    pool = pool or libs
    ids = [c for c in v.written_theorems(pool) if len(cs.recs[c]["ls"]) >= min_len]
    sh = {c: shingles(cs.recs[c]["ls"], k) for c in ids}
    index = collections.defaultdict(list)
    for c, s in sh.items():
        for x in s:
            index[x].append(c)
    n = len(ids)
    idf = {x: math.log(n / len(cids)) for x, cids in index.items()}
    best = {}
    for c in ids:
        if v.lib[c] not in libs:
            continue
        cand = collections.Counter()
        for x in sh[c]:
            others = index[x]
            if len(others) > max_df:
                continue
            for o in others:
                if o != c:
                    cand[o] += 1
        wc = sum(idf[x] for x in sh[c])
        top = None
        for o, shared in cand.items():
            if shared < min_shared:
                continue
            inter = sh[c] & sh[o]
            contain = len(inter) / min(len(sh[c]), len(sh[o]))
            if contain < min_contain:
                continue
            w = sum(idf[x] for x in inter) / min(wc, sum(idf[x] for x in sh[o]))
            key = (len(inter), contain)
            if top is None or key > top[0]:
                top = (key, o, w)
        if top:
            (shared, contain), o, w = top
            best[c] = {"cid": c, "metric": "R4.clone", "partner": o, "shared": shared,
                       "contain": round(contain, 2), "weighted": round(w, 2),
                       "len": len(cs.recs[c]["ls"]), "partner_len": len(cs.recs[o]["ls"]),
                       "same_module": cs.consts[c].mod == cs.consts[o].mod}
    return list(best.values())


def subtree_clones(v, libs=("Numlib",), pool=None, min_size=5, max_decls=3):
    """R5. Proofs that contain the same subproof: an identical tree of nested lemma applications,
    at least `min_size` lemmas large, occurs in two declarations, and in at most `max_decls`: a
    tree that many proofs contain is what a tactic emits, not what an author copied."""
    cs = v.cs
    pool = pool or libs
    index = collections.defaultdict(list)
    for c in v.written_theorems(pool):
        for h, sz in cs.recs[c]["fp"]:
            if sz >= min_size:
                index[h].append((c, sz))
    best = {}
    for h, occ in index.items():
        if len(occ) < 2 or len(occ) > max_decls:
            continue
        for c, sz in occ:
            if v.lib[c] not in libs:
                continue
            if c not in best or sz > best[c]["size"]:
                o = next(x for x, _ in occ if x != c)
                best[c] = {"cid": c, "metric": "R5.subproof", "partner": o, "size": sz,
                           "n_decls": len(occ),
                           "same_module": cs.consts[c].mod == cs.consts[o].mod}
    return list(best.values())


# ---------------------------------------------------------------------------------------------
# G: generality
# ---------------------------------------------------------------------------------------------

ANALYTIC = ("Mathlib.Analysis", "Mathlib.Topology", "Mathlib.MeasureTheory", "Mathlib.Probability",
            "Mathlib.Geometry")


def class_family(cs, cls):
    """A class is `normed`, `topological` (topology, measure, geometry) or `algebraic` (the rest),
    by the module that declares it."""
    m = cs.modules[cs.consts[cls].mod]
    if m.startswith("Mathlib.Analysis"):
        return "normed"
    if m.startswith(ANALYTIC):
        return "topological"
    return "algebraic"


class Binders:
    """How each declaration uses its binders, followed through calls.

    A binder that is only ever handed, as it is, to declarations that ignore it is unused; a
    class-typed binder handed to a declaration that needs less of it needs no more than that.
    """
    USE_CAP = 64
    DIRECT_CAP = 16

    def __init__(self, v):
        self.v = v
        self.cs = v.cs
        self.B = {cid: r["b"] for cid, r in v.cs.recs.items() if r.get("f") and "b" in r}
        self._unused = {}
        self._needs = {}

    def unused(self, cid, i):
        key = (cid, i)
        if key in self._unused:
            return self._unused[key]
        self._unused[key] = False  # a cycle counts as a use
        bs = self.B.get(cid)
        res = False
        if bs is not None and i < len(bs):
            _, _, _, occ_t, dc_t, occ_b, dc_b, _, direct = bs[i][:9]
            if occ_b is not None:
                if occ_t == 0 and occ_b == 0:
                    res = True
                elif occ_t == dc_t and occ_b == dc_b and len(direct) < self.DIRECT_CAP:
                    res = all(self.unused(h, k) for h, k in direct)
        self._unused[key] = res
        return res

    def needs(self, cid, i):
        """The classes a class-typed binder is consumed at, or None when unknown."""
        key = (cid, i)
        if key in self._needs:
            return self._needs[key]
        bs = self.B.get(cid)
        if bs is None or i >= len(bs) or bs[i][2] is None or bs[i][5] is None:
            self._needs[key] = None
            return None
        cls = bs[i][2]
        self._needs[key] = {cls}  # a cycle needs the class itself
        uses = bs[i][7]
        if len(uses) >= self.USE_CAP:
            return self._needs[key]
        n = len(bs)
        res = set()
        for ucls, consumer, arg, site in uses:
            if site < n and site != i and bs[site][2] is not None:
                # needed by another class binder's type: only as long as that one is needed
                if not self.overstrong(cid, site) and not self.unused(cid, site):
                    res.add(ucls)
                continue
            cb = self.B.get(consumer)
            if cb is not None and arg < len(cb) and cb[arg][2] == ucls:
                if self.unused(consumer, arg):
                    continue
                sub = self.needs(consumer, arg)
                if sub is not None and ucls not in sub:
                    res |= sub
                    continue
            res.add(ucls)
        self._needs[key] = res
        return res

    def gated(self, cid, i, seen=None):
        """Whether an unused binder is unused only because it is handed to a definition that
        ignores it: the definition takes it as a guard, and its callers must pass it on. The
        finding belongs to the definition, not to every theorem about it."""
        bs = self.B.get(cid)
        if bs is None or i >= len(bs):
            return False
        _, _, _, occ_t, _, occ_b, _, _, direct = bs[i][:9]
        if occ_t == 0 and occ_b == 0:
            return False
        seen = seen if seen is not None else set()
        if (cid, i) in seen:
            return False
        seen.add((cid, i))
        return any(self.cs.consts[h].kind != "t" or self.gated(h, k, seen) for h, k in direct)

    def overstrong(self, cid, i):
        bs = self.B[cid]
        cls = bs[i][2]
        if cls is None or bs[i][5] is None or self.unused(cid, i):
            return False
        nd = self.needs(cid, i)
        return nd is not None and cls not in nd


def binder_findings(v, libs=("Numlib",), kinds="td", binders=None):
    """G1-G4, from how a declaration uses its own binders, followed through calls.

    G1 unused hypothesis: a proposition binder that neither the proof nor the statement uses.
    G2 unused class: a class-typed binder that neither uses.
    G3 over-strong class: a class-typed binder only ever consumed at weaker classes. `drop` says
       how much weaker: `normed>algebraic`, `normed>topological`, `topological>algebraic`, or
       `same` when the weaker classes are of the binder's own family.
    G4 unused variable: any other binder that neither uses.
    `direct` is false when the binder is only unused because everything it is passed to ignores it.
    """
    cs = v.cs
    bd = binders or Binders(v)
    out = []
    for cid, r in cs.recs.items():
        if cid not in v.primary or v.lib[cid] not in libs or cs.consts[cid].kind not in kinds:
            continue
        bs = bd.B.get(cid)
        if bs is None or "pl" not in r:
            continue
        for i, b in enumerate(bs):
            info, prop, cls, occ_t, dc_t, occ_b, dc_b, uses, direct = b[:9]
            bname = b[9] if len(b) > 9 else None
            if occ_b is None:
                continue  # the proof term does not bind it: nothing to say
            if bname and bname.startswith("_"):
                continue  # named as unused on purpose
            if bd.unused(cid, i):
                if bd.gated(cid, i):
                    continue  # reported on the definition that takes it
                metric = "G2.unused_class" if cls is not None else ("G1.unused_hyp" if prop else "G4.unused_var")
                f = {"cid": cid, "metric": metric, "binder": i, "binder_name": bname,
                     "direct": occ_t == 0 and occ_b == 0}
                if cls is not None:
                    f["cls"] = cls
                out.append(f)
            elif cls is not None and bd.overstrong(cid, i):
                nd = sorted(bd.needs(cid, i))
                fam = class_family(cs, cls)
                fams = {class_family(cs, k) for k in nd}
                if fam == "normed" and fams <= {"algebraic"}:
                    drop = "normed>algebraic"
                elif fam == "normed" and "normed" not in fams:
                    drop = "normed>topological"
                elif fam == "topological" and fams <= {"algebraic"}:
                    drop = "topological>algebraic"
                else:
                    drop = "same"
                out.append({"cid": cid, "metric": "G3.overstrong_class", "binder": i,
                            "binder_name": bname, "cls": cls, "needs": nd, "drop": drop})
    return out


# ---------------------------------------------------------------------------------------------
# P: proof quality
# ---------------------------------------------------------------------------------------------

def dead_steps(v, libs=("Numlib",)):
    """P1. Proofs with a `have` whose proof the rest of the term never uses."""
    cs = v.cs
    return [{"cid": c, "metric": "P1.dead_have", "count": cs.recs[c]["dh"]}
            for c in v.written_theorems(libs) if cs.recs[c]["dh"] > 0]


def long_proofs(v, libs=("Numlib",), lines=50):
    """P2. Proofs longer than `lines` source lines (the rubric's threshold for factoring)."""
    cs = v.cs
    return [{"cid": c, "metric": "P2.long_proof", "lines": v.lines(c),
             "lemmas": len(cs.recs[c]["ls"]), "vd": cs.recs[c]["vd"]}
            for c in v.written_theorems(libs) if v.lines(c) > lines]


# ---------------------------------------------------------------------------------------------
# A: API design
# ---------------------------------------------------------------------------------------------

def private_general(v, libs=("Numlib",)):
    """A1. Private theorems that are not about their own file: the statement mentions no constant
    declared in the theorem's module (`scope` = `foreign`), or none of the project at all
    (`scope` = `mathlib`). General infrastructure hidden where nobody can find or reuse it."""
    cs = v.cs
    out = []
    for cid in v.written_theorems(libs):
        c = cs.consts[cid]
        if not c.has("p"):
            continue
        tc = cs.recs[cid].get("tc", [])
        if not tc:
            continue
        if all(cs.lib(k) not in PROJECT for k in tc):
            out.append({"cid": cid, "metric": "A1.private_general", "scope": "mathlib"})
        elif all(cs.consts[k].mod != c.mod for k in tc):
            out.append({"cid": cid, "metric": "A1.private_general", "scope": "foreign"})
    return out


def misplaced_general(v, libs=("Numlib",)):
    """A2. Public theorems whose statement mentions no constant of the project, in a file that is
    not marked as an upstreaming candidate."""
    cs = v.cs
    out = []
    for cid in v.written_theorems(libs):
        c = cs.consts[cid]
        if c.has("p") or v.upstream.get(c.mod, False):
            continue
        tc = cs.recs[cid].get("tc", [])
        if tc and all(cs.lib(k) not in PROJECT for k in tc):
            out.append({"cid": cid, "metric": "A2.misplaced_general", "consts": len(tc)})
    return out


def definition_api(v, libs=("Numlib",)):
    """A3. Per definition: how many theorems state something about it (in its own module and
    elsewhere), how many of those are simp lemmas, how many declarations use it at all, and how
    many modules other than its own realized its unfolding lemmas (`foo.eq_1`, `foo.eq_def`),
    which happens when a proof there unfolds or rewrites with the definition by name."""
    cs = v.cs
    # modules that realized an equation lemma of each definition
    eq_mods = collections.defaultdict(set)
    for c in cs.consts:
        if cs.modules[c.mod].split(".", 1)[0] not in PROJECT:
            continue
        base, _, last = c.name.rpartition(".")
        if last.startswith("eq_") and (last[3:].isdigit() or last in ("eq_def", "eq_unfold")):
            pid = cs.by_name.get(base)
            if pid is not None:
                eq_mods[pid].add(c.mod)
    out = []
    for cid in v.written_defs(libs):
        c = cs.consts[cid]
        if c.has("I") or c.red == "r":
            continue
        stmt = [u for u in v.stmt_users.get(cid, ()) if cs.consts[u].kind == "t" and u in v.primary]
        own = [u for u in stmt if cs.consts[u].mod == c.mod]
        users = v.users.get(cid, set())
        ext_users = {u for u in users if cs.consts[u].mod != c.mod}
        unfold_mods = {m for m in eq_mods.get(cid, ()) if m != c.mod}
        out.append({"cid": cid, "metric": "A3.def_api", "lemmas": len(stmt), "own_lemmas": len(own),
                    "simp": sum(1 for u in own if cs.consts[u].has("s")),
                    "users": len(users), "ext_users": len(ext_users),
                    "ext_modules": len({cs.consts[u].mod for u in ext_users}),
                    "unfold_modules": len(unfold_mods),
                    "self_unfold": c.mod in eq_mods.get(cid, ())})
    return out


def surface_reach(v, back="Numlib", surface="NumlibSurface"):
    """The declarations of the backbone that some surface declaration depends on, however far."""
    cs = v.cs
    live = set()
    stack = [c for c in cs.recs if v.lib[c] == surface]
    while stack:
        c = stack.pop()
        for k in v.uses.get(c, ()):
            k = v.twin_of.get(k, k)
            if k not in live and v.lib.get(k) == back:
                live.add(k)
                stack.append(k)
    return live


def repeated_hypotheses(v, libs=("Numlib",), min_theorems=6):
    """A7. A quantified hypothesis (one that itself starts with a binder: a property of a function
    or a family, not of a point) that many theorems spell out identically: a concept that has no
    name. One row per hypothesis, with the theorems that carry it.

    Hypotheses are compared by the hash of their type with variables identified by type, so
    `∀ x, f x ≠ ⊥` is one hypothesis whatever `f` is called."""
    cs = v.cs
    where = collections.defaultdict(list)
    for cid in v.written_theorems(libs):
        r = cs.recs[cid]
        seen = set()
        for h, m in zip(r.get("hh", ()), r.get("hm", ())):
            if len(m) < 4 or m[3] < 1 or h in seen:
                continue
            seen.add(h)
            where[h].append((cid, m[0]))
    out = []
    for h, ws in where.items():
        if len(ws) >= min_theorems:
            cid, i = ws[0]
            out.append({"cid": cid, "metric": "A7.repeated_hypothesis", "binder": i,
                        "binder_name": cs.recs[cid]["b"][i][9], "theorems": len(ws),
                        "modules": len({cs.consts[c].mod for c, _ in ws}),
                        "carriers": [c for c, _ in ws]})
    out.sort(key=lambda f: -f["theorems"])
    return out


def unused_declarations(v, libs=("Numlib",), reach=None):
    """A4. Written declarations nobody exercises.

    `A4.unused`: no other declaration of the project refers to it and no plan names it.
    `A4.unreached`: no surface declaration depends on it, even indirectly (a planned declaration
    without a consumer is one of these, as is everything that only serves unused declarations).
    """
    cs = v.cs
    reach = reach if reach is not None else surface_reach(v)
    out = []
    for cid, r in cs.recs.items():
        if cid not in v.primary or v.lib[cid] not in libs or cs.consts[cid].kind not in "td":
            continue
        c = cs.consts[cid]
        # not visible in terms, so not judged: instances, projections, syntax, and lemmas proved
        # by reflexivity (simp uses those without leaving their name in the proof)
        if c.has("I") or c.has("j") or c.has("s"):
            continue
        if c.kind == "t" and not r.get("ls") and r.get("vd", 99) <= 3:
            continue
        if "ParserDescr" in cs.consts[r["ch"]].name if "ch" in r else False:
            continue
        users = {u for u in v.users.get(cid, ()) if v.twin_of.get(u, u) != cid}
        planned = v.is_planned(cid)
        if not users and not planned:
            out.append({"cid": cid, "metric": "A4.unused", "kind": cs.consts[cid].kind,
                        "simp": cs.consts[cid].has("s")})
        elif cid not in reach:
            out.append({"cid": cid, "metric": "A4.unreached", "kind": cs.consts[cid].kind,
                        "planned": planned, "users": len(users)})
    return out


# ---------------------------------------------------------------------------------------------
# library-level summary
# ---------------------------------------------------------------------------------------------

def summary(v, libs):
    """The indices of one library: each a rate over its written theorems (or definitions)."""
    cs = v.cs
    th = v.written_theorems(libs)
    n = len(th)
    if n == 0:
        return {}
    rs = [cs.recs[c] for c in th]
    lines = [v.lines(c) for c in th]
    total_lines = sum(lines)
    s = {"theorems": n, "definitions": len(v.written_defs(libs))}
    s["lines_p50"], s["lines_p90"], s["lines_p99"] = quantiles(lines)
    s["dag_p50"], s["dag_p90"], s["dag_p99"] = quantiles([r["vd"] for r in rs])
    s["lemmas_p50"], s["lemmas_p90"], s["lemmas_p99"] = quantiles([len(r["ls"]) for r in rs])
    s["long_proofs_pct"] = pct(sum(1 for x in lines if x > 50), n)
    s["long_proof_line_share_pct"] = pct(sum(x for x in lines if x > 50), total_lines)
    s["dead_have_pct"] = pct(sum(1 for r in rs if r["dh"] > 0), n)
    ws = wrappers(v, libs)
    s["wrapper_pct"] = pct(len(ws), n)
    s["wrapper_direct_pct"] = pct(sum(1 for w in ws if w["direct"]), n)
    bf = collections.Counter()
    seen = set()
    for f in binder_findings(v, libs, kinds="t"):
        keys = [f["metric"]]
        if f["metric"] == "G3.overstrong_class" and f["drop"] != "same":
            keys.append("G3." + f["drop"])
        for k in keys:
            if (f["cid"], k) not in seen:
                seen.add((f["cid"], k))
                bf[k] += 1
    for k in ("G1.unused_hyp", "G2.unused_class", "G4.unused_var", "G3.overstrong_class",
              "G3.normed>algebraic", "G3.normed>topological", "G3.topological>algebraic"):
        s[k + "_pct"] = pct(bf[k], n)
    priv = [c for c in th if cs.consts[c].has("p")]
    s["private_pct"] = pct(len(priv), n)
    pg = private_general(v, libs)
    s["private_foreign_pct"] = pct(len(pg), n)
    s["private_mathlib_only_pct"] = pct(sum(1 for f in pg if f["scope"] == "mathlib"), n)
    s["simp_pct"] = pct(sum(1 for c in th if cs.consts[c].has("s")), n)
    used = sum(1 for c in th if v.users.get(c))
    s["used_pct"] = pct(used, n)
    # where the lemmas a proof applies come from
    own = other = 0
    for c, r in zip(th, rs):
        for k in r["ls"]:
            if cs.lib(k) in libs:
                own += 1
            else:
                other += 1
    s["own_lemma_share_pct"] = pct(own, own + other)
    return s
