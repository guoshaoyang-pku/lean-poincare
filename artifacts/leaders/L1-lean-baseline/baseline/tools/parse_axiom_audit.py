#!/usr/bin/env python3
"""Parse the L1 grouped axiom-audit logs into machine-readable evidence.

Inputs : baseline/logs/axiom-audit-G{1,2}.log   (L1AXROW / L1MOD / L1DEP / L1SUM lines)
Outputs: baseline/audit/axiom-audit.json          full report
         baseline/audit/declarations.tsv          per-declaration enumeration
         baseline/audit/dep-edges.tsv             intra-package direct dependency edges
         baseline/audit/downstream-use.json       transitive dependent counts
"""
import json
import os
import re
import time
from collections import defaultdict, deque

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LOGS = [os.path.join(WT, "baseline/logs/axiom-audit-G1.log"),
        os.path.join(WT, "baseline/logs/axiom-audit-G2.log")]
OUT = os.path.join(WT, "baseline/audit")
APPROVED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_BAD = {
    "d12NegControlBadAxiom",
    "d12NegControlBadTheorem",
    "Poincare.D12.VolumeIBP.Audit.negativeControl",
}

# compiler-generated auxiliary declarations (not authored theorem names)
AUX_RE = re.compile(
    r"\.(eq_\d+|congr_simp|_simp_\d+(_\d+)*|_proof_\d+|match_\d+.*|_flat_ctor"
    r"|_unsafe_rec|_sizeOf.*|proof_\d+|_eq_\d+)$|\._@\.|_uniq")


def main():
    rows = {}
    all_rows = []
    mods = defaultdict(int)
    sums = defaultdict(dict)
    edges = set()
    verdicts = []
    errors = []
    for log in LOGS:
        part = os.path.basename(log).replace("axiom-audit-", "").replace(".log", "")
        if not os.path.exists(log):
            errors.append(f"missing log {log}")
            continue
        for line in open(log, encoding="utf-8", errors="replace"):
            if line.startswith("L1AXROW\t"):
                f = line.rstrip("\n").split("\t")
                if len(f) < 7:
                    errors.append(f"short row: {line[:120]}")
                    continue
                _, name, kind, module, axs, extra, internal = f[:7]
                rec = {"name": name, "kind": kind, "module": module,
                       "axioms": [a for a in axs.split(",") if a],
                       "extra": [a for a in extra.split(",") if a],
                       "internal": internal == "true", "partition": part}
                all_rows.append(rec)
                rows[name] = rec
            elif line.startswith("L1MOD\t"):
                _, m, c = line.rstrip("\n").split("\t")
                mods[m] += int(c)
            elif line.startswith("L1SUM\t"):
                _, k, v = line.rstrip("\n").split("\t", 2)
                sums[part][k] = v
            elif line.startswith("L1DEP\t"):
                _, u, d = line.rstrip("\n").split("\t", 2)
                edges.add((u, d))
            elif line.startswith("L1AXVERDICT"):
                verdicts.append(line.rstrip("\n").split("\t", 1)[-1])
        # capture compile errors / exit marker
        txt = open(log, encoding="utf-8", errors="replace").read()
        if "error:" in txt:
            errors.append(f"{part}: log contains 'error:'")

    # transitive dependents (downstream checked use)
    rd = defaultdict(set)
    for u, d in edges:
        rd[d].add(u)
    downstream = {}

    def count_downstream(target):
        seen = set()
        q = deque(rd.get(target, ()))
        while q:
            x = q.popleft()
            if x in seen:
                continue
            seen.add(x)
            q.extend(rd.get(x, ()))
        return seen

    for name in rows:
        d = count_downstream(name)
        downstream[name] = len(d)
        rows[name]["downstream_count"] = len(d)
        rows[name]["downstream_sample"] = sorted(d)[:10]

    unexpected = {n: r for n, r in rows.items() if r["extra"] and n not in EXPECTED_BAD}
    expected_seen = sorted(n for n in rows if n in EXPECTED_BAD and rows[n]["extra"])
    sorry = sorted(n for n, r in rows.items() if "sorryAx" in r["extra"])
    unsafe = sorted(n for n, r in rows.items() if r["kind"] == "unsafe_def")
    axioms = sorted(n for n, r in rows.items() if r["kind"] == "axiom")
    partial = sorted(n for n, r in rows.items() if r["kind"] == "partial_def")
    kinds = defaultdict(int)
    for r in rows.values():
        kinds[r["kind"]] += 1
    cone_hist = defaultdict(int)
    for r in rows.values():
        cone_hist[";".join(sorted(r["axioms"])) or "(none)"] += 1

    # cross-partition duplicate declaration names (the package is not import-closed)
    byname = defaultdict(set)
    for r in all_rows:
        byname[r["name"]].add(r["module"])
    dup_names = {n: sorted(ms) for n, ms in byname.items() if len(ms) > 1}
    authored_dups = {n: ms for n, ms in dup_names.items()
                     if not AUX_RE.search(n)}
    generated_dups = {n: ms for n, ms in dup_names.items() if AUX_RE.search(n)}

    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "approved_axioms": sorted(APPROVED),
        "verdicts": verdicts,
        "logs": [os.path.relpath(l, WT) for l in LOGS],
        "errors": errors,
        "summary": {
            "declarations": len(rows),
            "modules_with_declarations": len(mods),
            "kinds": dict(kinds),
            "cone_histogram": dict(cone_hist),
            "unexpected_violations": len(unexpected),
            "unexpected_violation_names": sorted(unexpected),
            "expected_negative_controls_seen": expected_seen,
            "sorry_declarations": sorry,
            "axiom_declarations": axioms,
            "unsafe_declarations": unsafe,
            "partial_declarations": partial,
            "intra_package_direct_edges": len(edges),
            "declaration_rows_sum": len(all_rows),
            "duplicate_names_across_modules": len(dup_names),
            "authored_duplicate_names": len(authored_dups),
            "generated_duplicate_names": len(generated_dups),
            "partitions": {k: dict(v) for k, v in sums.items()},
        },
        "declarations": rows,
        "duplicate_names": dup_names,
        "authored_duplicate_names": authored_dups,
        "generated_duplicate_names": generated_dups,
    }
    os.makedirs(OUT, exist_ok=True)
    json.dump(report, open(os.path.join(OUT, "axiom-audit.json"), "w"), indent=1)

    with open(os.path.join(OUT, "declarations.tsv"), "w") as f:
        f.write("name\tkind\tmodule\taxioms\textra\tinternal\tdownstream_count\n")
        for n, r in sorted(rows.items()):
            f.write(f"{n}\t{r['kind']}\t{r['module']}\t{';'.join(r['axioms'])}\t"
                    f"{';'.join(r['extra'])}\t{r['internal']}\t{r['downstream_count']}\n")
    with open(os.path.join(OUT, "dep-edges.tsv"), "w") as f:
        f.write("user\tdep\n")
        for u, d in sorted(edges):
            f.write(f"{u}\t{d}\n")
    top = sorted(rows.items(), key=lambda kv: -kv[1]["downstream_count"])[:100]
    json.dump({"generated_at": report["generated_at"],
               "top_downstream": [{"name": n, "count": r["downstream_count"],
                                   "module": r["module"], "kind": r["kind"]} for n, r in top]},
              open(os.path.join(OUT, "downstream-use.json"), "w"), indent=1)

    s = report["summary"]
    print(json.dumps({k: s[k] for k in ("declarations", "modules_with_declarations", "kinds",
                                        "unexpected_violations", "expected_negative_controls_seen",
                                        "intra_package_direct_edges")}, indent=1))
    print("cone histogram:", dict(cone_hist))
    print("errors:", errors[:5], "verdicts:", verdicts)


if __name__ == "__main__":
    main()
