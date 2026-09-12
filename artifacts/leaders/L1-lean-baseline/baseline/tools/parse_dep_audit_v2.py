#!/usr/bin/env python3
"""Parse the corrected (proof-level) dependency graph and compare with v1.

Inputs : baseline/logs/dep-audit-G{1,2}.log  (L2DEP lines, allowOpaque := true)
         baseline/audit/declarations.tsv      (v1 type-level downstream counts)
         baseline/audit/named-targets-downstream.json (target list)
Outputs: baseline/audit/dep-edges-v2.tsv
         baseline/audit/downstream-use-v2.json
         baseline/audit/downstream-use-comparison.json
"""
import json
import os
import time
from collections import defaultdict, deque

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LOGS = [os.path.join(WT, f"baseline/logs/dep-audit-G{i}.log") for i in (1, 2)]


def main():
    edges = set()
    sums = {}
    for log in LOGS:
        part = os.path.basename(log).split("-")[-1].replace(".log", "")
        for line in open(log, encoding="utf-8", errors="replace"):
            if line.startswith("L2DEP\t"):
                _, u, d = line.rstrip("\n").split("\t", 2)
                edges.add((u, d))
            elif line.startswith("L2SUM\t"):
                _, k, v = line.rstrip("\n").split("\t", 2)
                sums.setdefault(part, {})[k] = v

    # v1 table
    v1 = {}
    kinds = {}
    with open(os.path.join(WT, "baseline/audit/declarations.tsv")) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for line in f:
            p = line.rstrip("\n").split("\t")
            r = dict(zip(hdr, p))
            v1[r["name"]] = r
            kinds[r["name"]] = r["kind"]

    rd = defaultdict(set)
    for u, d in edges:
        rd[d].add(u)
    cache = {}

    def downstream(target):
        if target in cache:
            return cache[target]
        seen = set()
        q = deque(rd.get(target, ()))
        while q:
            x = q.popleft()
            if x in seen:
                continue
            seen.add(x)
            q.extend(rd.get(x, ()))
        cache[target] = seen
        return seen

    names = set(v1) | {u for u, _ in edges} | {d for _, d in edges}
    counts = {n: len(downstream(n)) for n in names}

    with open(os.path.join(WT, "baseline/audit/dep-edges-v2.tsv"), "w") as f:
        f.write("user\tdep\n")
        for u, d in sorted(edges):
            f.write(f"{u}\t{d}\n")

    top = sorted(names, key=lambda n: -counts[n])[:100]
    json.dump({
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "baseline/logs/dep-audit-G{1,2}.log (L2DEP, ConstantInfo.value? with allowOpaque := true)",
        "note": "transitive dependent counts over the corrected graph (type + proof bodies for theorems/opaque)",
        "direct_edges": len(edges),
        "declarations": len(names),
        "top_downstream": [{"name": n, "count": counts[n], "module": v1.get(n, {}).get("module"),
                            "kind": kinds.get(n)} for n in top],
    }, open(os.path.join(WT, "baseline/audit/downstream-use-v2.json"), "w"), indent=1)

    targets = json.load(open(os.path.join(WT, "baseline/audit/named-targets-downstream.json")))
    rows = []
    for t in targets["targets"]:
        n = t["name"]
        v2c = counts.get(n, 0)
        v1c = t["proof_level_downstream_consumers"]
        rows.append({
            "role": t["role"], "name": n, "kind": t["kind"],
            "v1_type_level_count": v1c,
            "v2_proof_level_count": v2c,
            "delta": (v2c - v1c) if v1c is not None else None,
            "v2_consumers_sample": sorted(downstream(n))[:12],
        })
    cmp_report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "what_changed": ("v1 drivers used `ci.value?` (no allowOpaque), which is `none` for "
                         ".thmInfo/.opaqueInfo in Lean v4.34.0-rc2, so v1 edges for theorem "
                         "users were type-level only. v2 uses `ConstantInfo.value? ci "
                         "(allowOpaque := true)` and adds proof-body edges."),
        "partition_sums": sums,
        "v1_direct_edges": 40252,
        "v2_direct_edges": len(edges),
        "targets": rows,
    }
    json.dump(cmp_report, open(os.path.join(WT, "baseline/audit/downstream-use-comparison.json"), "w"), indent=1)
    print(json.dumps({"v2_direct_edges": len(edges), "v2_declarations": len(names),
                      "targets": [(r["name"], r["v1_type_level_count"], r["v2_proof_level_count"])
                                  for r in rows]}, indent=1))


if __name__ == "__main__":
    main()
