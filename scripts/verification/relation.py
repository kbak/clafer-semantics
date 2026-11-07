"""Candidate/Alloy representation, independent of satisfaction.

The byte/AST adapters and this correspondence are reviewed external assumptions,
not Lean theorems. See docs/bounded-comparison.md.
"""
from itertools import permutations, product
import re
import time

from protocol import Rejection, check_candidate_bounds, encoded, natural, reject, unsupported


# [impl->req~clafer-alloy-representation~1]
def inventory(core, metadata):
    """Associate receipt fields by their declared owner/target, never spelling."""
    nodes = {n["uid"]: n for n in core["declarations"]}
    fields = {}
    for symbol, field in metadata["fields"].items():
        owner, target = field["owner"], field["target"]
        if field["arity"] != 2 or owner not in nodes or target not in nodes:
            unsupported("auxiliary_field", symbol)
        # In S there are no inherited fields. A reference to one's own child
        # can coexist with containment: the observation lists the reference
        # first in the pinned generator. Receipt order/capture provenance is an
        # explicit external assumption beyond #51's complete token check.
        observation = metadata.get("observations", {}).get(owner)
        candidates = []
        if nodes[owner]["target"] == target:
            candidates.append(("references", owner))
        if nodes[target]["parent"] == owner:
            candidates.append(("containment", target))
        if len(candidates) > 1:
            if observation is None:
                unsupported("ambiguous_field_role", symbol)
            declared = [f.split(":", 1)[0].strip() for f in observation["fields"]]
            candidates = [candidates[0] if declared.index(symbol) == 0 else candidates[1]]
        if len(candidates) != 1:
            unsupported("unclassified_field", symbol)
        fields[symbol] = dict(field, table=candidates[0][0], uid=candidates[0][1])
    expected = {("references", u) for u, n in nodes.items() if n["target"]}
    expected |= {("containment", u) for u, n in nodes.items() if n["parent"] in nodes}
    if {(f["table"], f["uid"]) for f in fields.values()} != expected or len(fields) != len(expected):
        reject("field_inventory")
    return nodes, fields


def validate_candidate(candidate, core, bounds):
    """Serialization/typing only; missing endpoints and semantic failures survive."""
    check_candidate_bounds(candidate, bounds)
    nodes = {n["uid"]: n for n in core["declarations"]}
    objects = candidate["objects"]
    if type(objects) is not list:
        reject("objects")
    for obj in objects:
        natural(obj, "object")
    natural(candidate["root"], "root")
    if len(set(objects)) != len(objects) or candidate["root"] not in objects:
        reject("object_identity")
    members = candidate["members"]
    if len({tuple(r) for r in members}) != len(members):
        reject("duplicate_membership")
    for uid, obj in members:
        if uid not in nodes and uid != "root":
            reject("unknown_class", uid)
        if obj not in objects:
            reject("dangling_object", obj)
    membership = set(map(tuple, members))
    for table in ("containment", "references"):
        rows = candidate[table]
        if type(rows) is not list:
            reject("relation_rows", table)
        seen = set()
        for row in rows:
            if type(row) is not list or len(row) != 2 or type(row[0]) is not str or type(row[1]) is not list or len(row[1]) != 2:
                reject("relation_row", table)
            uid, (a, b) = row
            for x in (a, b):
                natural(x, "endpoint")
                if x not in objects:
                    reject("dangling_object", x)
            if (uid, a, b) in seen:
                reject("duplicate_tuple", table)
            seen.add((uid, a, b))
            n = nodes.get(uid)
            if n is None:
                reject("unknown_class", uid)
            source, target = (n["parent"], uid) if table == "containment" else (uid, n["target"])
            if (source, a) not in membership or (target, b) not in membership:
                reject("ill_typed_endpoint", uid)


def canonical(candidate):
    return dict(objects=sorted(candidate["objects"]), root=candidate["root"],
                **{k: sorted(candidate[k]) for k in ("members", "containment", "references")})


def rename(candidate, mapping):
    return canonical(dict(objects=[mapping[o] for o in candidate["objects"]], root=mapping[candidate["root"]],
        members=[[u, mapping[o]] for u, o in candidate["members"]],
        **{k: [[u, [mapping[a], mapping[b]]] for u, (a, b) in candidate[k]] for k in ("containment", "references")}))


# [impl->req~clafer-alloy-representation~1]
def isomorphism(left, right):
    """Exact finite graph isomorphism fixing root, partitioned by all memberships.

    Each ordinary link is its tuple; derived link identities are (uid,p,h,t).
    Thus an object bijection induces the required occurrence bijections.
    """
    if len(left["objects"]) != len(right["objects"]):
        return None
    def partitions(c):
        groups = {}
        for o in c["objects"]:
            key = (o == c["root"], tuple(sorted(u for u, x in c["members"] if x == o)))
            groups.setdefault(key, []).append(o)
        return groups
    a, b = partitions(left), partitions(right)
    if set(a) != set(b) or any(len(a[k]) != len(b[k]) for k in a):
        return None
    keys = sorted(a)
    deadline = time.monotonic() + 5
    def mappings(i, mapping):
        if time.monotonic() > deadline:
            raise TimeoutError("object isomorphism search limit")
        if i == len(keys):
            yield mapping
            return
        k = keys[i]
        for choice in permutations(sorted(b[k])):
            if time.monotonic() > deadline:
                raise TimeoutError("object isomorphism search limit")
            yield from mappings(i + 1, mapping | dict(zip(sorted(a[k]), choice)))
    for mapping in mappings(0, {}):
        if rename(left, mapping) == canonical(right):
            return mapping
    return None


def occurrences(candidate):
    """Retain heads when forming pullback-composite link tokens."""
    return sorted([u, p, h, t] for u, (p, h) in candidate["containment"]
                  for v, (head, t) in candidate["references"] if u == v and h == head)


# [impl->req~clafer-alloy-representation~1]
def pin(candidate, core, metadata):
    nodes, fields = inventory(core, metadata)
    validate_candidate(candidate, core, metadata["bounds"])
    root = candidate["root"]
    objects = sorted(o for o in candidate["objects"] if o != root)
    names = {o: f"ib_obj_{i}" for i, o in enumerate(objects)}
    if set(names.values()) & (set(nodes) | set(fields)):
        unsupported("pin_variable_collision")
    clauses = []
    # These are exactly the virtual-root decoding convention, not a second
    # satisfaction definition. An incompatible candidate has no representation.
    root_members = {o for u, o in candidate["members"] if u == "root"}
    compatible = root_members == {root} and all(o != root for u, o in candidate["members"] if u != "root")
    for uid, n in nodes.items():
        if n["parent"] == "root":
            actual = {tuple(pair) for u, pair in candidate["containment"] if u == uid}
            expected = {(root, o) for u, o in candidate["members"] if u == uid}
            compatible &= actual == expected
    if not compatible:
        clauses.append("some none")
    for uid in nodes:
        members = [names[o] for u, o in candidate["members"] if u == uid and o != root]
        clauses.append(f"{uid} = ({' + '.join(sorted(members)) or 'none'})")
    for symbol, field in fields.items():
        tuples = [f"{names[a]}->{names[b]}" for u, (a, b) in candidate[field["table"]]
                  if u == field["uid"] and a != root and b != root]
        clauses.append(f"@{symbol} = ({' + '.join(sorted(tuples)) or 'none->none'})")
    body = "\n    ".join(clauses) or "no none"
    if objects:
        universe = " + ".join(sorted(nodes)) or "none"
        body = f"some disj {', '.join(names.values())}: ({universe}) | {{\n    {body}\n  }}"
    return "pred ib_candidate {\n  " + body + "\n}\n"


def range_argument(original, bounds, bitwidth):
    """Applicable only AFTER #51's complete restricted-output validation.

    Generated constraints use integer literals, #unary/#binary relations and
    comparisons. Relational +, joins and unions never increase arity past two.
    Pinning introduces no integer operations. util/integer has no invoked funcs.
    """
    natural(bitwidth, "bitwidth")
    if not 1 <= bitwidth <= 16:
        unsupported("bitwidth_profile", "supported range is 1..16")
    total = sum(v for u, v in bounds.items() if u != "root")
    literals = [int(x) for x in re.findall(r"(?<![\w'])\d+(?![\w'])", original)]
    maximum = max([1, total * total, *bounds.values(), *literals])
    if maximum > 2 ** (bitwidth - 1) - 1:
        unsupported("arithmetic_range", f"{maximum} does not fit signed {bitwidth}-bit")
    return dict(method="guarded-S-arity-at-most-two/v1", user_atom_upper=total,
                relation_tuple_upper=total * total, literals=sorted(set(literals)), maximum=maximum,
                signed_min=-(2 ** (bitwidth - 1)), signed_max=2 ** (bitwidth - 1) - 1)


# [impl->req~clafer-alloy-representation~1]
def decode(witness, core, metadata):
    nodes, fields = inventory(core, metadata)
    if set(witness["signatures"]) != set(nodes) or set(witness["fields"]) != set(fields):
        reject("witness_inventory")
    atoms = sorted({a for extent in witness["signatures"].values() for a in extent})
    labels = {a: i + 1 for i, a in enumerate(atoms)}
    c = dict(objects=list(range(len(atoms) + 1)), root=0, members=[["root", 0]], containment=[], references=[])
    for uid, extent in witness["signatures"].items():
        if len(set(extent)) != len(extent):
            reject("duplicate_witness_atom")
        for atom in extent:
            c["members"].append([uid, labels[atom]])
            if nodes[uid]["parent"] == "root":
                c["containment"].append([uid, [0, labels[atom]]])
    for symbol, rows in witness["fields"].items():
        field = fields[symbol]
        for row in rows:
            if len(row) != 2 or any(a not in labels for a in row):
                reject("witness_endpoint")
            c[field["table"]].append([field["uid"], [labels[a] for a in row]])
    validate_candidate(c, core, metadata["bounds"])
    return canonical(c)
