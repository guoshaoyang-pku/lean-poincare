#!/usr/bin/env python3
"""Named-target downstream-use / checked-use export for the L1 baseline.

Reads the generated declaration table and greps the authored tree for `#check`
probes, then records for each named blocker / main-chain target:
  kind, module, axiom cone, proof-level downstream consumer count (from the
  dependency graph), and the `#check` sites that mention it ("checked use").

Output: baseline/audit/named-targets-downstream.json (machine-readable),
        baseline/logs/named-targets-downstream.txt (human summary).
"""
import json
import os
import re
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REL = os.path.join(WT, "release")

TARGETS = [
    ("A1", "Poincare.Longrun.Evolution.perelmanF_step_lt"),
    ("A1", "Poincare.Longrun.Evolution.gibbsTerm_strictAnti"),
    ("A1", "Poincare.Longrun.Evolution.gibbsTerm_step_lt"),
    ("A1-sharp", "D4Audit.perelmanF_step_lt_of_one_le"),
    ("A1-sharp", "Poincare.D7.EvolutionSharp.perelmanF_step_lt_of_one_le"),
    ("A1-sharp", "D4Audit.gibbsTerm_strictAnti_of_one_le"),
    ("A1-sharp", "Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_of_one_le"),
    ("main-chain", "Poincare.D7.HeatKernel.HeatKernelData"),
    ("main-chain", "Poincare.D12.SemanticLedger.not_initialCondition_gaussian"),
    ("main-chain", "Poincare.D10.HeatKernelEuclidean.heat_equation"),
    ("main-chain", "Poincare.D7.Recognition.stage6Target_of_certificates"),
    ("neg-control", "d12NegControlBadAxiom"),
    ("neg-control", "d12NegControlBadTheorem"),
    ("neg-control", "Poincare.D12.VolumeIBP.Audit.negativeControl"),
]


def main():
    decls = {}
    with open(os.path.join(WT, "baseline/audit/declarations.tsv")) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for line in f:
            p = line.rstrip("\n").split("\t")
            decls[p[0]] = dict(zip(hdr, p))

    checks = []  # (#check sites)
    for dirpath, dirnames, filenames in os.walk(REL):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(dirpath, fn)
            for i, line in enumerate(open(p, encoding="utf-8", errors="replace"), 1):
                s = line.strip()
                if s.startswith("#check"):
                    checks.append((os.path.relpath(p, REL), i, s))

    def mentions(name):
        out = []
        pat = re.compile(r"(?<![A-Za-z0-9_.'])" + re.escape(name) + r"(?![A-Za-z0-9_.'])")
        for path, ln, s in checks:
            if pat.search(s):
                out.append({"file": path, "line": ln, "text": s[:160]})
        return out

    rows = []
    for role, name in TARGETS:
        d = decls.get(name)
        rows.append({
            "role": role,
            "name": name,
            "found_in_release": d is not None,
            "kind": d["kind"] if d else None,
            "module": d["module"] if d else None,
            "axiom_cone": d["axioms"] if d else None,
            "type_level_downstream_consumers_v1": int(d["downstream_count"]) if d else None,
            "downstream_metric": "v1 type-level graph (dep-edges.tsv); see limitation",
            "check_sites": mentions(name),
        })

    # Corrected (proof-level) counts, if the v2 dependency rebuild has been parsed.
    cmp_path = os.path.join(WT, "baseline/audit/downstream-use-comparison.json")
    limitation = ("v1 `downstream_count` comes from dep-edges.tsv, whose drivers used "
                  "`ci.value?` without `allowOpaque := true`; in Lean v4.34.0-rc2 that is "
                  "`none` for theorems, so v1 edges for theorem users are type-level only. "
                  "The corrected proof-level counts are in "
                  "baseline/audit/downstream-use-comparison.json (v2 graph).")
    if os.path.exists(cmp_path):
        cmp = json.load(open(cmp_path))
        v2 = {t["name"]: t for t in cmp["targets"]}
        for r in rows:
            t = v2.get(r["name"])
            if t:
                r["proof_level_downstream_consumers_v2"] = t["v2_proof_level_count"]
                r["proof_level_consumers_v2_sample"] = t["v2_consumers_sample"]

    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "source": "baseline/audit/declarations.tsv (kernel-enumerated) + #check scan of release/",
        "limitation": limitation,
        "note": ("`#check` mentions are checked-use evidence, not proof-level use; "
                 "`proof_level_downstream_consumers` is the TRANSITIVE count over the v1 "
                 "graph and `proof_level_downstream_consumers_v2` over the corrected v2 "
                 "graph (type + proof bodies)."),
        "targets": rows,
    }
    out = os.path.join(WT, "baseline/audit/named-targets-downstream.json")
    json.dump(report, open(out, "w"), indent=1)
    lines = ["name\trole\tkind\tv1_typelevel\tv2_prooflevel\t#check_sites\tfound"]
    for r in rows:
        lines.append(f"{r['name']}\t{r['role']}\t{r['kind']}"
                     f"\t{r['type_level_downstream_consumers_v1']}"
                     f"\t{r.get('proof_level_downstream_consumers_v2', 'n/a')}"
                     f"\t{len(r['check_sites'])}\t{r['found_in_release']}")
    txt = os.path.join(WT, "baseline/logs/named-targets-downstream.txt")
    open(txt, "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))
    absent = [r["name"] for r in rows if not r["found_in_release"]]
    if absent:
        print("NOT FOUND:", absent)


if __name__ == "__main__":
    main()
