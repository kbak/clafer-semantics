"""Explicit finite domains, seeded table sampling, and deterministic shrinking."""
import copy
from itertools import combinations, product
import random

from protocol import encoded
from relation import canonical, validate_candidate


def subsets(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


# [impl->req~clafer-comparison-replay~1]
def domain(core, bounds):
    """All labelled tables for n=0..sum(user scopes), fixed fresh singleton root.

    All membership subsets within per-class bounds (including unrelated overlap
    and unused ambient objects); all typed ordinary relation subsets. No semantic
    satisfaction filtering, no symmetry reduction. Root-violating tables are a
    separate fixed negative suite, not claimed members of this finite domain.
    """
    nodes = core["declarations"]
    for n in range(sum(b for u, b in bounds.items() if u != "root") + 1):
        objects = list(range(1, n + 1))
        choices = [list(s for s in subsets(objects) if len(s) <= bounds[d["uid"]]) for d in nodes]
        for memberships in product(*choices):
            extents = {"root": [0], **{d["uid"]: list(s) for d, s in zip(nodes, memberships)}}
            base = dict(objects=[0, *objects], root=0, members=[[u, o] for u, xs in extents.items() for o in xs], containment=[], references=[])
            positions = []
            for d in nodes:
                uid = d["uid"]
                if d["parent"] in extents:
                    positions.extend(("containment", uid, a, b) for a in extents[d["parent"]] for b in extents[uid])
                if d["target"]:
                    positions.extend(("references", uid, a, b) for a in extents[uid] for b in extents[d["target"]])
            for relation in subsets(positions):
                c = copy.deepcopy(base)
                for table, uid, a, b in relation: c[table].append([uid, [a, b]])
                yield canonical(c)


# [impl->req~clafer-comparison-replay~1]
def generated(core, bounds, seed, count):
    """Python Random MT19937; explicit seed, independent fair relation bits.

    Uniform n, then uniform class size and subset at that size, then Bernoulli
    tuple inclusion. This distribution is NOT uniform on all finite candidates.
    No filtering by the checker or Alloy representation.
    """
    rng = random.Random(seed)
    nodes = core["declarations"]
    for _ in range(count):
        n = rng.randrange(sum(b for u, b in bounds.items() if u != "root") + 1)
        extents = {"root": [0]}
        for d in nodes:
            uid = d["uid"]
            extents[uid] = sorted(rng.sample(range(1, n + 1), rng.randrange(min(n, bounds[uid]) + 1)))
        c = dict(objects=list(range(n + 1)), root=0, members=[[u,o] for u,xs in extents.items() for o in xs], containment=[], references=[])
        for d in nodes:
            uid = d["uid"]
            for table, source, target in (("containment",d["parent"],uid),("references",uid,d["target"])):
                # Abstract declarations use the imported 'clafer' sentinel;
                # they have no containment endpoint in the finite candidate.
                if source in extents and target in extents:
                    c[table].extend([uid,[a,b]] for a in extents[source] for b in extents[target] if rng.getrandbits(1))
        yield canonical(c)


def reductions(candidate):
    """Strictly decreasing row/object deletion order; no endpoint deduplication."""
    c = canonical(candidate)
    for obj in c["objects"]:
        if obj == c["root"]: continue
        yield canonical(dict(objects=[o for o in c["objects"] if o != obj], root=c["root"],
            members=[row for row in c["members"] if row[1] != obj],
            **{t:[row for row in c[t] if obj not in row[1]] for t in ("containment","references")}))
    for table in ("members","containment","references"):
        for i in range(len(c[table])):
            if table == "members" and c[table][i] == ["root", c["root"]]: continue
            smaller=copy.deepcopy(c); smaller[table].pop(i); yield smaller


# [impl->req~clafer-comparison-replay~1]
def shrink(candidate, core, bounds, preserves):
    """Deletion-minimal for reductions(), not a global minimum or new proof."""
    current=canonical(candidate); attempts=0
    while True:
        for smaller in reductions(current):
            try: validate_candidate(smaller, core, bounds)
            except ValueError: continue
            attempts += 1
            decision=preserves(smaller)
            if type(decision) is not bool:
                raise RuntimeError("inconclusive shrinking attempt; minimality not established")
            if decision:
                current=smaller; break
        else: return current, attempts


def batch(candidates, run, *, mode, expected=None, seed=None, limit=None):
    """Keep requested/admitted/completed denominators, including interrupted work."""
    report=dict(schema="clafer-comparison-search/1",mode=mode,seed=seed,requested=0,admitted=0,completed=0,
                categories={},exhausted=False,complete_domain=False,expected=expected,termination=None,not_run=0)
    try:
        for i,c in enumerate(candidates):
            report["requested"] += 1
            if limit is not None and i >= limit:
                report["termination"]="budget"; report["not_run"]+=1; break
            r=run(c,i)
            report["admitted"] += r["admission"]=="admitted"
            report["completed"] += r["complete"]
            report["categories"][r["category"]]=report["categories"].get(r["category"],0)+1
            if r.get("interrupted"):
                report["termination"]="interrupted";break
        else:
            report["exhausted"]=True; report["termination"]="exhausted"
    except KeyboardInterrupt:
        report["termination"]="interrupted"; report["not_run"]+=1
    report["complete_domain"]=(mode=="exhaustive" and report["exhausted"] and report["requested"]==report["completed"] and
                               (expected is None or expected==report["requested"]))
    return report
