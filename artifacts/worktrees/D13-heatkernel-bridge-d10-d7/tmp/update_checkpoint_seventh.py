#!/usr/bin/env python3
"""Final seventh-invocation checkpoint update."""
import json, re, re

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7"
P = WT + "/checkpoint.json"
d = json.load(open(P))

summary = {}
for line in open(WT + "/logs/d13_seventh_final_summary.txt"):
    for k, v in re.findall(r"([A-Za-z_][A-Za-z0-9_]*)=(\S+)", line):
        summary[k] = v
buildlog = open(WT + "/logs/d13_seventh_final_build.log").read()
m = re.search(r"Build completed successfully \((\d+) jobs\)", buildlog)
jobs = m.group(1) if m else "?"

d["updated_at"] = "2026-09-11T18:10:00+08:00"
d["elapsed_hours_this_invocation"] = 0.75
d["elapsed_hours_cumulative"] = 4.8
d["status"] = (
 "SEVENTH INVOCATION — COMPLETE, ALL GATES GREEN. Baseline re-verified from the 16 sixth-invocation hashes "
 "(sha256sum -c all OK; build exit 0, 9192 jobs, D6AUDIT PASS, AxiomAudit 188/188; logs/d13_seventh_baseline_build.log). "
 "NEW FILES: release/Poincare/D13/HeatKernelBridge/DataRefutation.lean (35 named declarations + 2 IsFiniteMeasure "
 "instances) and release/Poincare/D7/HeatKernel/DataStatus.lean (5 declarations); AxiomAudit extended 188 -> 228; "
 "All.lean docstring updated. FINDING: the two sixth-invocation statement-level repairs "
 "HeatKernelExistenceStatementPDE and HeatKernelDataExistenceStatement are FALSE as written — the two-point closed "
 "Riemannian spacetime (Bool, volume = dirac true + dirac false, laplacian = 0, timeDerivative = 0, discrete metric, "
 "dim 0) satisfies IsClosedRiemannianManifold and AnnihilatesConstants and admits no PDE-predicate kernel and no "
 "strictly positive legacy datum (delta = 0 forces time-constancy; the Dirac field then kills the off-diagonal value; "
 "contradiction with positivity). The bare legacy interface IS inhabited on the same spacetime by the identity kernel "
 "with C_lo = 0, failing strict positivity exactly off the diagonal, so the statements fail on their positivity "
 "clauses. POSITIVE COUNTERPART: the corrected-domain existence statement on the honest flat Euclidean family "
 "(operator pinned) is PROVED (flatCorrectedDomainExistence_proved); correctedDomain_is_exact_scope records the exact "
 "scope. FINAL GATES (logs/d13_seventh_final_*): build exit 0 (%s jobs), D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck "
 "PASS 228/228, semantic transcripts %s files exit 0, per-file %s/%s, worktree %s/%s, forbidden 0 hard / 0 soft, "
 "negcontrol PASS, diff vs D12 %s expected lines, upstream PASS, 18 hashes recorded and re-verified. "
 "exact_blockers_closed = []; D7-HEAT-KERNEL-EXISTENCE remains OPEN with its schematic statement-level targets removed "
 "as false; results .md/.json updated (§19)."
) % (jobs, summary.get("semantic_files"), summary.get("perfile_total"), summary.get("perfile_total"),
     summary.get("worktree_total"), summary.get("worktree_total"), summary.get("diff_lines"))

d["milestones"]["seventh_invocation_final_gates"] = (
 "DONE (17:42-18:0x+08:00): authoritative final suite (logs/d13_seventh_final_*): build exit 0 (%s jobs), D6AUDIT PASS, "
 "D13HeatKernelBridgeAxiomCheck PASS 228/228, semantic transcripts %s files exit 0 (0 failures), per-file %s/%s, "
 "worktree %s/%s, forbidden 0 hard / 0 soft (D13 11 files, D7/HeatKernel 13 files), negcontrol PASS, diff vs "
 "D12-heat-domain-repair %s expected new-file lines, upstream snapshot PASS, 18 hashes recorded; 18/18 re-verified "
 "with sha256sum -c after all writes."
) % (jobs, summary.get("semantic_files"), summary.get("perfile_total"), summary.get("perfile_total"),
     summary.get("worktree_total"), summary.get("worktree_total"), summary.get("diff_lines"))

d["gates"]["seventh_final"] = (
 "build exit 0 (%s jobs, D6AUDIT PASS, AxiomAudit PASS 228/228); semantic %s files exit 0; per-file %s/%s; worktree "
 "%s/%s; forbidden 0 hard / 0 soft; negcontrol PASS; diff %s expected lines; upstream PASS; 18 hashes "
 "(logs/d13_seventh_final_*)"
) % (jobs, summary.get("semantic_files"), summary.get("perfile_total"), summary.get("perfile_total"),
     summary.get("worktree_total"), summary.get("worktree_total"), summary.get("diff_lines"))

d["dependency_requests"] = [
 "STATEMENT TARGET (resolved in the negative; do not revive): HeatKernelExistenceStatement, "
 "HeatKernelExistenceStatementV1, HeatKernelExistenceStatementPDE and HeatKernelDataExistenceStatement are all FALSE "
 "as formalized (fifth and seventh invocations). Use the corrected-domain flat statement "
 "(FlatCorrectedDomainExistence) as the proved model target.",
 "RIEMANNIAN INTERFACE (critical path): a metric-based Laplacian (Laplace-Beltrami) with the parabolic maximum "
 "principle and compact-manifold volume/distance data, so that an existence statement can be stated over a hypothesis "
 "class that pins the operator; the schematic interface cannot express self-adjointness/dissipativity soundly "
 "(LaplacianSymmetryRefutation) and cannot exclude the zero operator (DataRefutation).",
 "MANIFOLD-SIDE TASKS over that interface: heat-kernel existence (parametrix, parabolic regularity, Gaussian bounds, "
 "spectral theory) — the honest remaining content of D7-HEAT-KERNEL-EXISTENCE.",
 "D12-heat-semigroup-analysis / D13-deturck-shorttime-producer: consume flatHeatKernelDataV1_integrable / "
 "flatHeatKernelDataV1_cc; do not consume the refuted schematic statement-level targets.",
 "COMPACT FINITE-MEASURE DOWNSTREAM USERS: use toHeatKernelData_of_integrableClass / toHeatKernelData_of_ccClass and "
 "exists_v1_iff_exists_legacy to upgrade corrected-domain data to the legacy D7 type.",
 "INDEPENDENT SEMANTIC ACCEPTANCE of the 14 authored modules by a fresh reviewer (hash-pinned, "
 "logs/d13_seventh_final_hashes.txt): the v1 bridge interface and transport, the compact upgrade, the predicate "
 "semantics, the PDE repair, the two snapshot statement-level refutations, the statement-level repair package, the "
 "self-adjointness refutation, the seventh-invocation data-level refutation with its degenerate model and flat "
 "positive counterpart, and the four D7 consumers.",
]

json.dump(d, open(P, "w"), indent=1, ensure_ascii=False)
open(P, "a").write("\n")
print("checkpoint finalized")
