#!/usr/bin/env python3
"""Seventh-invocation update of longrun/results/D13-heatkernel-bridge-d10-d7.json."""
import json, re, re, sys, datetime

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7"
P = WT + "/longrun/results/D13-heatkernel-bridge-d10-d7.json"
d = json.load(open(P))
new_decls = json.load(open(WT + "/tmp/d13_seventh_new_decls.json"))

# --- gate numbers from the summary/logs -------------------------------------------------
summary = {}
for line in open(WT + "/logs/d13_seventh_final_summary.txt"):
    for k, v in re.findall(r"([A-Za-z_][A-Za-z0-9_]*)=(\S+)", line):
        summary[k] = v
hash_lines = open(WT + "/logs/d13_seventh_final_hashes.txt").read().strip().split("\n")

d["generated_utc"] = "2026-09-11T09:45:00Z"
d["elapsed_hours"] = round(4.05 + 0.62, 2)
d["elapsed_hours_this_invocation"] = 0.62
d["module"] = ("HeatKernelBridge (Poincare.D13.HeatKernelBridge, incl. the PredicateSemantics, "
    "PDERepair, StatementRefutation, GeometricRepair, LaplacianSymmetryRefutation and DataRefutation "
    "companions) + D7 consumers Poincare.D7.HeatKernel.V1Interface, StatementStatus, RepairStatus and DataStatus")

d["verdict"] = (
 "TASK_DONE (requests independent acceptance; no named blocker closed). The LONG_PLAN HeatKernelBridge "
 "module transports D10 HeatKernelEuclidean to the D7 HeatKernelData interface on the D12 corrected "
 "admissible-test-function domain; the D11 core inhabits the corrected-domain interface in every dimension "
 "(both admissible classes); compact finite-measure corrected-domain data upgrade to genuine legacy "
 "HeatKernelData with the upgrade a left inverse of the embedding; D7 modules consume the bridge. "
 "228/228 declarations in the approved axiom cone, all gates exit 0. Sixth invocation: the statement-level "
 "repair package (constant annihilation, the adversarial refutation of the Laplacian-only repair, the "
 "snapshot/PDE incomparability theorem, the data-level repaired statement, the refuted self-adjointness axiom). "
 "SEVENTH INVOCATION (this run): the two statement-level repairs of the sixth invocation are themselves FALSE "
 "as written. The two-point closed Riemannian spacetime (volume delta_true + delta_false, laplacian = 0, "
 "timeDerivative = 0, discrete metric, dim 0) satisfies IsClosedRiemannianManifold and AnnihilatesConstants, "
 "yet admits no PDE-predicate kernel and no strictly positive legacy datum: with delta = 0 the heat-equation "
 "field forces time-constancy while the Dirac field at a source point against the indicator of the other point "
 "forces the off-diagonal value to vanish. The failure is exactly the positivity clause: the identity kernel "
 "(twoPointDegenerateData) inhabits the rest of the legacy interface with C_lo = 0. Hence HeatKernelDataExistenceStatement "
 "(and HeatKernelExistenceStatementPDE) cannot be the honest target: the hypothesis class must pin the operator to a "
 "genuine geometric Laplacian, not just require delta 1 = 0. Positive counterpart: the corrected-domain existence "
 "statement restricted to the honest flat Euclidean family (operator pinned) IS PROVED "
 "(flatCorrectedDomainExistence_proved); correctedDomain_is_exact_scope records the exact scope. New D7 consumer "
 "Poincare.D7.HeatKernel.DataStatus (5 declarations) records the finding at the D7 level. No named blocker is claimed "
 "closed; D7-HEAT-KERNEL-EXISTENCE remains open, now with its schematic statement-level targets removed as false."
)

d["proved_declarations"] = d["proved_declarations"] + new_decls

d["expanded_hypotheses"]["data_refutation"] = (
 "*D13 DataRefutation (seventh invocation).* `twoPointSpacetime` (M = Bool, volume = Measure.dirac true + "
 "Measure.dirac false, laplacian = 0, timeDerivative = 0, dist x y = if x = y then 0 else 1, dim = 0) with "
 "`isClosedRiemannianManifold_twoPointSpacetime` (finite => compact; the two atoms give positive measure on every "
 "nonempty set; finite measure; discrete metric axioms) and `isAnnihilatesConstants_twoPointSpacetime` (laplacian = 0). "
 "Refutation schemas assume only: S.laplacian = 0, a unit atom at p (integral of every function vanishing off p equals "
 "its value at p, `integral_twoPointVolume_eq_of_support`), p != y, and (for the predicate level) that the indicator "
 "of p is in the admissible class (`continuousIntegrableClass_twoPoint_indicator`: continuous by discreteness, "
 "integrable by boundedness on a finite measure) or (data level) that it is continuous. No Gaussian bound, no semigroup, "
 "no symmetry is used; `eq_of_hasDerivAt_zero_of_pos` is the only analytic input (a function with vanishing derivative "
 "on (0,inf) is constant there, from `IsOpen.is_const_of_fderiv_eq_zero`)."
)
d["expanded_hypotheses"]["degenerate_model"] = (
 "*D13 DataRefutation, exact failure mode.* `twoPointDegenerateData : HeatKernelData Bool` with kernel "
 "`twoPointIdentityKernel x y t = if x = y then 1 else 0`, C_up = 1, c_up = 1, C_lo = 0, c_lo = 1, laplacian = 0, "
 "dim = 0. It satisfies every field of the legacy interface (nonnegativity, Gaussian upper bound, Gaussian lower bound "
 "with the zero constant, symmetry, the semigroup law against the two-atom measure, normalization, the heat equation "
 "with the zero Laplacian, and the full initial Dirac condition against EVERY continuous test function), and fails "
 "strict positivity exactly off the diagonal (`twoPointDegenerateData_not_strictly_positive`). `twoPoint_data_scope` "
 "packages: the two hypotheses hold, the degenerate datum matches volume/laplacian with C_lo = 0, it is not strictly "
 "positive, and no strictly positive matching datum exists."
)
d["expanded_hypotheses"]["flat_corrected_statement"] = (
 "*D13 DataRefutation, positive counterpart.* `FlatCorrectedDomainExistence` = for every n there is a "
 "`HeatKernelDataV1 (EuclideanSpace R (Fin n))` that is an integrable-class variant, everywhere strictly positive at "
 "positive times, and whose kernel is the explicit D10 `gaussianKernel n t (x - y)`. Proved "
 "(`flatCorrectedDomainExistence_proved`) by `flatHeatKernelDataV1_integrable` + `flatKernel_pos` + "
 "`flatHeatKernelDataV1_integrable_kernel_eq_gaussian`. `correctedDomain_is_exact_scope` conjoins it with the two "
 "statement refutations."
)

d["semantic_class"]["seventh_invocation_refutations"] = (
 "proved theorem / counterexample (general, universe-polymorphic conditional schemas plus universe-0 statement "
 "refutations): the two-point closed Riemannian spacetime with the zero Laplacian satisfies the repaired hypothesis "
 "class and admits no PDE kernel and no strictly positive legacy datum; the failure is localised to the positivity / "
 "positive-lower-constant clauses by the degenerate identity-kernel model (model class). The general schemas are "
 "conditional interfaces (they assume the unit-atom integral identity and the admissibility of the indicator), the "
 "concrete two-point instantiations discharge those hypotheses by proof, not by assumption."
)
d["semantic_class"]["seventh_invocation_positive"] = (
 "proved theorem: `flatCorrectedDomainExistence_proved` proves the corrected-domain existence statement on the honest "
 "flat Euclidean family (operator, measure and distance pinned), where the D10 transport supplies the witness; this is "
 "the scope in which an existence statement over this bridge is true. No manifold-side existence is claimed."
)

d["remaining_blockers"] = [
 "D7-HEAT-KERNEL-EXISTENCE (manifold heat-kernel existence: parametrix/Levi, Duhamel, short-time existence) — OPEN. "
 "The snapshot predicate-level statements are refuted (fifth invocation) and the sixth-invocation statement-level "
 "repairs over the schematic interface are ALSO refuted (seventh invocation: the two-point spacetime with delta = 0 "
 "satisfies the whole hypothesis class and admits no strictly positive datum). The remaining honest content is over a "
 "genuinely geometric interface (metric Laplacian with the maximum principle); the corrected-domain flat existence "
 "statement IS proved (FlatCorrectedDomainExistence).",
 "B-D7-PARABOLIC-REGULARITY (Schauder estimates, Hölder spaces, smoothness of weak solutions) — OPEN",
 "B-D7-SOBOLEV-EMBEDDING (Sobolev spaces on manifolds, embedding, Rellich–Kondrachov) — OPEN",
 "B-D7-SPECTRAL-THEOREM (Laplace–Beltrami spectral theorem, eigenfunction expansion, Hille–Yosida) — OPEN",
 "B-D7-DIRAC-DELTA (distribution theory; currently only continuous-test-function limits) — OPEN",
 "B-D7-GAUSSIAN-BOUNDS (Li–Yau, heat-kernel estimates on manifolds) — OPEN",
 "B-D7-MAXIMUM-PRINCIPLE (parabolic maximum principle, positivity/uniqueness) — OPEN",
 "Riemannian-metric/Laplace–Beltrami formalization (a metric theory pinning laplacian to the geometric operator; "
 "mathlib at the pinned revision has RiemannianMetric bundles but no Laplace–Beltrami operator) — OPEN, and now "
 "REQUIRED: the seventh invocation proves that no hypothesis of the form 'closed + delta 1 = 0' over the schematic "
 "interface can support a true universally quantified existence statement (the zero operator is admitted).",
 "Sound statement of the classical integration-by-parts/dissipativity conditions over the schematic interface (the "
 "all-functions Bochner-integral forms are false for the honest packaged flat Laplacian — proved in "
 "LaplacianSymmetryRefutation.lean) — OPEN interface obligation",
]

d["axiom_evidence"]["seventh_invocation"] = {
 "declaration_count": 228,
 "check": "D13HeatKernelBridgeAxiomCheck: PASS — all 228 declarations of the D13 heat-kernel bridge depend only on "
          "[propext, Classical.choice, Quot.sound] (release build, logs/d13_seventh_final_build.log)",
 "new_declarations": len(new_decls),
 "note": "AxiomAudit.lean extended with import Poincare.D13.HeatKernelBridge.DataRefutation and "
         "import Poincare.D7.HeatKernel.DataStatus plus 40 new #print axioms lines and 40 new entries in "
         "bridgeAuditedDeclarations; the fail-closed run_cmd re-check aborts the build on any axiom outside the cone.",
}

d["compile_evidence"].append({
 "command": "lake build",
 "cwd": "release/",
 "exit": 0,
 "note": "seventh-invocation baseline on the frozen sixth-invocation artifact: Build completed successfully (9192 jobs), "
         "D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 188/188 (logs/d13_seventh_baseline_build.log); the 16 "
         "recorded hashes re-verified byte-identical with sha256sum -c logs/d13_sixth_final_hashes.txt",
})
d["compile_evidence"].append({
 "command": "bash tmp/d13_seventh_gates.sh d13_seventh_final",
 "cwd": "worktree root",
 "exit": 0,
 "note": "seventh-invocation final suite: semantic transcripts %s files exit 0, build exit 0 (%s jobs, axiom audit "
         "PASS 228/228), per-file %s/%s, worktree %s/%s, forbidden 0/0, negcontrol PASS, diff %s expected lines, "
         "upstream PASS, %s hashes (logs/d13_seventh_final_*)"
         % (summary.get("semantic_files"), re.search(r"\((\d+) jobs\)", open(WT + "/logs/d13_seventh_final_build.log").read()).group(1),
            summary.get("perfile_total"), summary.get("perfile_total"), summary.get("worktree_total"),
            summary.get("worktree_total"), summary.get("diff_lines"), summary.get("hashes_recorded")),
})
d["compile_evidence"].append({
 "command": "lake env lean tmp/d13_semantic_checks_g_datarefutation.lean",
 "cwd": "worktree root",
 "exit": 0,
 "note": "seventh-invocation #check/#print axioms transcript for DataRefutation and the D7 consumer DataStatus "
         "(two-point model, refutations, general schemas, degenerate model, flat corrected-domain statement)",
})

d["source_hashes"] = {}
for line in hash_lines:
    h, _, path = line.partition("  ")
    d["source_hashes"][path.strip()] = h.strip()

d["next_dependency_requests"] = [
 "STATEMENT TARGET (resolved in the negative; do not revive): HeatKernelExistenceStatement, "
 "HeatKernelExistenceStatementV1, HeatKernelExistenceStatementPDE and HeatKernelDataExistenceStatement are all FALSE "
 "as formalized — the first two by the identity-Laplacian one-point datum (fifth invocation), the latter two by the "
 "zero-Laplacian two-point datum (seventh invocation). No universally quantified existence statement over the "
 "schematic HeatSpacetime with hypotheses 'closed + delta 1 = 0' can be true.",
 "RIEMANNIAN INTERFACE (now the critical path): provide a metric-based Laplacian (Laplace–Beltrami) with the "
 "parabolic maximum principle, plus compact-manifold volume/distance data, so that an existence statement can be "
 "stated over a hypothesis class that pins the operator; the schematic Bochner-integral interface cannot express "
 "self-adjointness/dissipativity soundly (LaplacianSymmetryRefutation) and cannot exclude the zero operator "
 "(DataRefutation).",
 "MANIFOLD-SIDE TASKS over that interface: existence of the heat kernel (parametrix, parabolic regularity, Gaussian "
 "bounds, spectral theory) — the honest remaining content of D7-HEAT-KERNEL-EXISTENCE. The flat case over the "
 "corrected domain is done (FlatCorrectedDomainExistence); the compact finite-measure upgrade to legacy data is done "
 "(exists_v1_iff_exists_legacy).",
 "D12-heat-semigroup-analysis / D13-deturck-shorttime-producer: consume flatHeatKernelDataV1_integrable / "
 "flatHeatKernelDataV1_cc as the checked corrected-domain model datum; do NOT consume the refuted schematic "
 "statement-level targets.",
 "COMPACT FINITE-MEASURE DOWNSTREAM USERS: use toHeatKernelData_of_integrableClass / toHeatKernelData_of_ccClass "
 "(and exists_v1_iff_exists_legacy) to upgrade corrected-domain data to the legacy D7 type.",
 "INDEPENDENT SEMANTIC ACCEPTANCE of the 14 authored modules by a fresh reviewer (hash-pinned, "
 "logs/d13_seventh_final_hashes.txt): the v1 bridge interface and transport, the compact upgrade, the predicate "
 "semantics, the PDE repair, the two snapshot statement-level refutations, the statement-level repair package, the "
 "self-adjointness refutation, the seventh-invocation data-level refutation with its degenerate model and flat "
 "positive counterpart, and the four D7 consumers.",
]

d["seventh_invocation"] = {
 "when_utc": "2026-09-11T09:39Z-… (17:39-… +08:00), elapsed ≈ 0.55 h",
 "what": "DataRefutation.lean (35 named declarations + 2 instances; AxiomAudit grows from 188 to 228) and the new D7 "
         "consumer DataStatus.lean (5 declarations); results card §19.",
 "context": "The sixth invocation replaced the refuted snapshot statements by HeatKernelExistenceStatementPDE / "
            "HeatKernelDataExistenceStatement over 'IsClosedRiemannianManifold ∧ AnnihilatesConstants' and called the "
            "data-level form the honest target. This invocation proves both repaired statements false as written.",
 "baseline_hashes_match": "16/16 sha256sum -c OK on logs/d13_sixth_final_hashes.txt (byte-identical); build exit 0 "
                           "(9192 jobs, D6AUDIT PASS, AxiomAudit PASS 188/188)",
 "findings": [
  "The two-point closed Riemannian spacetime (Bool, volume delta_true + delta_false, laplacian = 0, timeDerivative = 0, "
  "discrete metric, dim 0) satisfies the whole sixth-invocation hypothesis class (IsClosedRiemannianManifold + "
  "AnnihilatesConstants) and admits NO PDE-predicate kernel and NO strictly positive legacy datum.",
  "Mechanism (proved): with the zero Laplacian the heat-equation field forces the kernel to be constant in time "
  "(eq_of_hasDerivAt_zero_of_pos), while the Dirac field at source y against the indicator of the other point p forces "
  "K p y t -> 0; strict positivity at t = 1 gives the contradiction. General schemas + universe-polymorphic conditional "
  "refutations + universe-0 statement refutations.",
  "Exact failure mode: the identity kernel twoPointDegenerateData inhabits every other field of the legacy interface "
  "(including the full initial Dirac condition for all continuous test functions) with C_lo = 0 and fails strict "
  "positivity exactly off the diagonal; so the statements fail on their positivity / positive-lower-constant clauses.",
  "Consequence: no universally quantified existence statement over the schematic HeatSpacetime with hypotheses "
  "'closed + delta 1 = 0' can be true; the hypothesis class must pin the operator (elliptic/geometric Laplacian).",
  "Positive counterpart: the corrected-domain existence statement restricted to the honest flat Euclidean family "
  "(operator, measure, distance pinned) IS PROVED (FlatCorrectedDomainExistence); correctedDomain_is_exact_scope "
  "records the scope.",
  "D7-level consumption: DataStatus.lean records not_exists_heatKernelData_strictlyPositive_twoPoint, "
  "data_interface_inhabited_with_zero_lower_constant, data_level_target_refuted, "
  "corrected_domain_flat_statement_survives and data_status_summary.",
 ],
 "new_file": "release/Poincare/D13/HeatKernelBridge/DataRefutation.lean (35 named declarations + 2 IsFiniteMeasure "
             "instances, audited) and release/Poincare/D7/HeatKernel/DataStatus.lean (5 declarations, audited); "
             "AxiomAudit.lean extended to 228 declarations; All.lean docstring updated.",
 "gates": ("semantic transcripts %s files exit 0; build exit 0; axiom audit PASS 228/228; per-file %s/%s; "
           "worktree %s/%s; forbidden 0/0; negcontrol PASS; diff vs D12 %s expected lines; upstream PASS; "
           "%s hashes recorded (logs/d13_seventh_final_*)")
           % (summary.get("semantic_files"), summary.get("perfile_total"), summary.get("perfile_total"),
              summary.get("worktree_total"), summary.get("worktree_total"), summary.get("diff_lines"),
              summary.get("hashes_recorded")),
}

json.dump(d, open(P, "w"), indent=1, ensure_ascii=False)
open(P, "a").write("\n")
print("wrote", P)
print("proved_declarations:", len(d["proved_declarations"]))
print("source_hashes:", len(d["source_hashes"]))
