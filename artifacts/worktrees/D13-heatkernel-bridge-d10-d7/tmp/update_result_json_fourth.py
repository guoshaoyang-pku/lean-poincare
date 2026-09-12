#!/usr/bin/env python3
"""Fourth-invocation update of the D13 result JSON (PDERepair companion + final gates)."""
import json
from pathlib import Path

P = Path("longrun/results/D13-heatkernel-bridge-d10-d7.json")
d = json.loads(P.read_text())

d["generated_utc"] = "2026-09-11T07:05:00Z"
d["elapsed_hours"] = 1.7
d["elapsed_hours_this_invocation"] = 0.3
d["module"] = ("HeatKernelBridge (Poincare.D13.HeatKernelBridge, incl. the PredicateSemantics and "
               "PDERepair companions) + D7 consumer Poincare.D7.HeatKernel.V1Interface")

d["verdict"] = (
    "TASK_DONE (requests independent acceptance; no named blocker closed): the LONG_PLAN "
    "HeatKernelBridge module transports D10 HeatKernelEuclidean to the D7 HeatKernelData interface "
    "on the D12 corrected admissible-test-function domain; the D11 core inhabits the corrected-domain "
    "interface in every dimension (both admissible classes); compact finite-measure corrected-domain "
    "data upgrade to genuine legacy HeatKernelData with the upgrade a left inverse of the embedding; "
    "a new D7 module consumes the bridge and proves the blocked D7 existence statement equivalent to "
    "its corrected-domain restatement. 108/108 declarations in the approved axiom cone, all gates "
    "exit 0. Third invocation added the machine-checked PredicateSemantics companion: the D7 "
    "predicate's heat-equation field is a snapshot operator identity, not the PDE, and the honest "
    "flat Euclidean spacetime does not satisfy it for the D10 kernel in positive dimension. Fourth "
    "invocation re-verified the frozen artifact from byte-identical hashes and added the matching "
    "checked repair candidate PDERepair: the versioned predicate IsHeatKernelPDE (v2) with the genuine "
    "HasDerivAt PDE field, a transport from HeatKernelDataV1 data to it, and the theorem that the D10 "
    "kernel inhabits it on the honest flat spacetime in every dimension on both classes while "
    "refuting the snapshot predicate; no existence statement is introduced for the repaired predicate "
    "and no blocker is claimed closed."
)

pde_decls = [
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.v2",
        "kind": "def",
        "type": "\u2115 := 2",
        "semantic_class": "model-interface-v2"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE",
        "kind": "structure",
        "type": "(S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M \u2192 M \u2192 \u211d \u2192 \u211d) \u2192 Prop \u2014 positive, solvesPDE : HasDerivAt (fun s => K x y s) (S.laplacian (fun z => K z y t) x) t, normalized, dirac_limitFor on C",
        "semantic_class": "model-interface-v2"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.solvesPDE_hasDerivAt",
        "kind": "theorem",
        "type": "IsHeatKernelPDE S C K \u2192 \u2200 x y {t}, 0 < t \u2192 HasDerivAt (fun s => K x y s) (S.laplacian (fun z => K z y t) x) t",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime",
        "kind": "def",
        "type": "HeatKernelDataV1 X \u2192 HeatSpacetime X (core volume/laplacian/dist/dim; timeDerivative := 0, unused by IsHeatKernelPDE)",
        "semantic_class": "model-interface-v2"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_volume",
        "kind": "theorem",
        "type": "D.toHeatSpacetime.volume = D.volume",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_laplacian",
        "kind": "theorem",
        "type": "D.toHeatSpacetime.laplacian = D.laplacian",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_timeDerivative",
        "kind": "theorem",
        "type": "D.toHeatSpacetime.timeDerivative = 0",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dist",
        "kind": "theorem",
        "type": "D.toHeatSpacetime.dist = D.dist",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dim",
        "kind": "theorem",
        "type": "D.toHeatSpacetime.dim = D.dim",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_pos_of_dist_le_one",
        "kind": "theorem",
        "type": "0 < D.C_lo \u2192 0 < t \u2192 D.dist x y \u2264 1 \u2192 0 < D.kernel x y t (near-diagonal positivity from the Gaussian lower bound; everywhere-positivity is not implied)",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1",
        "kind": "theorem",
        "type": "D : HeatKernelDataV1 X \u2192 ((\u2200 x y t, 0 < t \u2192 0 < D.kernel x y t)) \u2192 (C : AdmissibleTestClass X D.volume) \u2192 (\u2200 f, C.cls f \u2192 D.testClass.cls f) \u2192 IsHeatKernelPDE D.toHeatSpacetime C D.kernel",
        "semantic_class": "genuine-general (transport; positivity is an explicit expanded hypothesis)"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_integrableClass",
        "kind": "theorem",
        "type": "D : HeatKernelDataV1 X \u2192 ((...positivity...)) \u2192 D.IsIntegrableClassVariant \u2192 IsHeatKernelPDE D.toHeatSpacetime (continuousIntegrableClass D.volume) D.kernel",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_ccClass",
        "kind": "theorem",
        "type": "D : HeatKernelDataV1 X \u2192 ((...positivity...)) \u2192 D.IsIntegrableClassVariant \u2192 [IsFiniteMeasureOnCompacts D.volume] \u2192 IsHeatKernelPDE D.toHeatSpacetime (continuousCompactSupportClass D.volume) D.kernel",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.flatHeatSpacetime_eq_toHeatSpacetime",
        "kind": "theorem",
        "type": "flatHeatSpacetime n = (flatHeatKernelDataV1_integrable n).toHeatSpacetime",
        "semantic_class": "genuine-general"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_integrable",
        "kind": "theorem",
        "type": "\u2200 n, IsHeatKernelPDE (flatHeatSpacetime n) (continuousIntegrableClass (flatHeatSpacetime n).volume) (flatKernel n)",
        "semantic_class": "model \u2014 explicit D10 Euclidean model, unconditional in n"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_cc",
        "kind": "theorem",
        "type": "\u2200 n, IsHeatKernelPDE (flatHeatSpacetime n) (continuousCompactSupportClass volume) (flatKernel n)",
        "semantic_class": "model \u2014 explicit D10 Euclidean model, unconditional in n"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.flat_pde_repaired_scope",
        "kind": "theorem",
        "type": "\u2200 n, 0 < n \u2192 IsHeatKernelPDE (flatHeatSpacetime n) (continuousIntegrableClass ...) (flatKernel n) \u2227 \u00ac IsHeatKernelV1 (flatHeatSpacetime n) (continuousIntegrableClass ...) (flatKernel n)",
        "semantic_class": "model + negative result, unconditional for every positive n"
    },
    {
        "name": "Poincare.D13.HeatKernelBridge.not_forall_isHeatKernelPDE_imp_isHeatKernelV1",
        "kind": "theorem",
        "type": "\u00ac (\u2200 (M : Type) [TopologicalSpace M] [MeasurableSpace M] (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M \u2192 M \u2192 \u211d \u2192 \u211d), IsHeatKernelPDE S C K \u2192 IsHeatKernelV1 S C K)",
        "semantic_class": "negative result, genuine-general (repair is a genuine statement change)"
    },
]
d["proved_declarations"].extend(pde_decls)

d["semantic_class"]["pde_repair"] = (
    "PDERepair.lean (18 declarations, fourth invocation): the versioned predicate IsHeatKernelPDE (v2) "
    "with the genuine HasDerivAt heat-equation field; the spacetime attached to a bridge datum; the "
    "near-diagonal positivity transfer; the predicate-level transport of HeatKernelDataV1 data with "
    "everywhere-positivity as an explicit expanded hypothesis; the D10 flat inhabitant on both classes "
    "in every dimension; and the checked non-implication from the repaired to the snapshot predicate. "
    "Model/interface definitions plus genuine-general transport; no existence statement and no closure."
)
d["semantic_class"]["statement_only"] = (
    "HeatKernelExistenceStatementV1 (state-only Prop, exactly like the legacy HeatKernelExistenceStatement "
    "it reduces to; not proved). No existence statement is introduced for IsHeatKernelPDE because the "
    "schematic HeatSpacetime does not constrain laplacian to be the Laplace-Beltrami operator."
)

d["expanded_hypotheses"]["pde_repair"] = [
    "IsHeatKernelPDE.of_dataV1: everywhere-positivity (forall x y t, 0 < t -> 0 < D.kernel x y t) is an explicit hypothesis because the core's Gaussian lower bound gives positivity only for dist x y <= 1 (kernel_pos_of_dist_le_one); for the flat model it is discharged by the proved explicit Gaussian fact flatKernel_pos",
    "IsHeatKernelPDE.of_dataV1: class inclusion (forall f, C.cls f -> D.testClass.cls f), discharged definitionally for the integrable class and via C_c subset integrable for the C_c class (requires [IsFiniteMeasureOnCompacts])",
    "flat_isHeatKernelPDE_*: no hypotheses beyond n : Nat",
    "no repaired existence statement is assumed or stated: IsClosedRiemannianManifold constrains volume and distance but not the laplacian, so a manifold existence Prop over HeatSpacetime would not be the PDE theorem",
]

d["source_hashes"] = {
    "release/Poincare/D13/HeatKernelBridge/Basic.lean": "96328402d9633274536400a91b75a8194f932609afc2f6dcbccea0e2d2474d63",
    "release/Poincare/D13/HeatKernelBridge/EuclideanTransport.lean": "1bc54d6d38c6a6ccbb90c74e8dd023774fd2fb2e1ad4858fe395351abb555598",
    "release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean": "c93915ba64fbd1a56dbf6b21e32f7baede95a43be5f6a98192050f3786cbc6fb",
    "release/Poincare/D13/HeatKernelBridge/All.lean": "65fccc50ef07fab81cc1cf03c1788d12cdf6c7983a39c8a405669a90ed36b863",
    "release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean": "ef5d789ee795810081fc8771a944b1dfc01dc1fa29b248fbac7347044500118f",
    "release/Poincare/D13/HeatKernelBridge/PDERepair.lean": "bdaaf609ed5bec6055f90dafb356f7585a30d8d1e5683f237ae99bf976a99d0e",
    "release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean": "740a6bf881ff3df08c4e0853863dc1af34af4c7f55dd1f13e92cfec583aab259",
    "release/Poincare/D7/HeatKernel/V1Interface.lean": "8d5fa5b5a7dfdc728ccc0f288f48153e02a9b1b852679055af2813f44d6b86e8",
    "lakefile.toml": "b56f13927f2c63a07221b0fde9a31d20d42f99b80e90d4330aa7c06de6c642fa",
    "lake-manifest.json": "cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0",
    "lean-toolchain": "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
}
d["source_hashes_note"] = (
    "Fourth-invocation hashes. The ten third-invocation hashes were re-computed byte-identical before "
    "any change (logs/d13_fourth_baseline_hashes.txt); All.lean (docstring) and AxiomAudit.lean (108 "
    "declarations) changed afterwards and PDERepair.lean is new; the other five authored files are "
    "unchanged from the third invocation."
)

d["compile_evidence"].extend([
    {
        "command": "lake env lean tmp/d13_pde_repair_checks.lean",
        "cwd": "worktree root",
        "exit": 0,
        "note": "fourth invocation semantic #check transcript of the new declarations (logs/d13_final_semantic_checks.out)"
    },
    {
        "command": "lake build",
        "cwd": "release/",
        "exit": 0,
        "note": "fourth invocation final: Build completed successfully (9187 jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS (108 decls) (logs/d13_final_build.log)"
    },
    {
        "command": "lake env lean <file> for each of the 8 authored files",
        "cwd": "worktree root",
        "exit": "8/8 0",
        "note": "fourth invocation final per-file gate (logs/d13_final_perfile.txt)"
    },
    {
        "command": "lake env lean <file> for every .lean in the worktree (.lake/.git/.dshpkg/third_party excluded)",
        "cwd": "worktree root",
        "exit": "307/307 0",
        "note": "fourth invocation final worktree gate (logs/d13_final_gate_raw.txt)"
    },
    {
        "command": "lake build",
        "cwd": "release/",
        "exit": 0,
        "note": "fourth invocation baseline (pre-change): Build completed successfully (9186 jobs), D6AUDIT PASS (logs/d13_fourth_build.log)"
    },
    {
        "command": "lake env lean <file> for each of the 7 pre-existing authored files + all worktree .lean",
        "cwd": "worktree root",
        "exit": "7/7 and 305/305 0",
        "note": "fourth invocation baseline per-file and worktree gates (logs/d13_fourth_perfile.txt, logs/d13_fourth_gate_raw.txt)"
    },
    {
        "command": "python3 input/d5-tools/scan_forbidden.py release/Poincare/D13/HeatKernelBridge",
        "exit": 0,
        "note": "fourth invocation final: 0 hard / 0 soft, 7 files"
    },
    {
        "command": "python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/HeatKernel",
        "exit": 0,
        "note": "fourth invocation final: 0 hard / 0 soft, 10 files"
    },
    {
        "command": "diff -rq vs D12-heat-domain-repair/release/Poincare (fourth invocation)",
        "exit": 1,
        "note": "only differences: D13/ (7 files) and D7/HeatKernel/V1Interface.lean; no builder file modified (logs/d13_final_diff.txt)"
    },
    {
        "command": "python3 tmp/verify_frenzymath_snapshot.py",
        "exit": 0,
        "note": "fourth invocation: all seven checks true, commit bb91a091 (logs/d13_final_upstream.out)"
    },
])

d["axiom_evidence"].update({
    "check": "D13HeatKernelBridgeAxiomCheck: PASS \u2014 all 108 declarations of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]",
    "breakdown": "108/108 in the approved cone (2 with no axioms: HeatKernelDataV1.v1 and IsHeatKernelPDE.v2; 106 with subsets of {propext, Classical.choice, Quot.sound})",
    "log": "logs/d13_final_build.log and logs/d13_final_axiom_audit.out (fourth invocation); logs/d13_axiom_audit_third.out (third, 90); logs/d13_axiom_audit_verify.out (second, 74)",
    "coverage_check": "all declarations of the 8 authored source files are in the 108-entry audit list and in the 108 #print axioms transcripts",
    "fourth_run": "PASS \u2014 D13HeatKernelBridgeAxiomCheck: all 108 declarations depend only on [propext, Classical.choice, Quot.sound] (logs/d13_final_axiom_audit.out)",
})

d["next_dependency_requests"] = [
    "Independent acceptance of this card: fresh rebuild of the 8 authored modules from the recorded fourth-invocation hashes, re-run of the fail-closed axiom check and negative control, semantic review of HeatKernelDataV1 / heatKernelExistenceStatement_iff_v1 / the compact upgrade hypotheses / the PredicateSemantics findings / the IsHeatKernelPDE v2 repair candidate",
    "D12-heat-semigroup-analysis / D13-deturck-shorttime-producer: consume flatHeatKernelDataV1_integrable / flatHeatKernelDataV1_cc as the checked corrected-domain model datum",
    "Manifold-side tasks closing D7-HEAT-KERNEL-EXISTENCE should target the data-level form (genuine HasDerivAt heat equation, as in HeatKernelDataV1) or the versioned predicate IsHeatKernelPDE (PDERepair.lean), which states that equation at the D7 predicate level and is inhabited by the D10 kernel in every dimension; the snapshot solves field of IsHeatKernel/IsHeatKernelV1 is not the PDE (PredicateSemantics.lean)",
    "Compact finite-measure downstream users: consume toHeatKernelData_of_integrableClass / toHeatKernelData_of_ccClass to upgrade corrected-domain data to the legacy D7 type",
    "Statement-repair adoption (v2): a future statement-level task should define the existence statement over an enriched HeatSpacetime whose laplacian is pinned to the Laplace-Beltrami operator of a Riemannian metric, and drop or document the unused timeDerivative snapshot field; this card deliberately does not state an existence Prop over the schematic HeatSpacetime",
]

d["legacy_policy"] = (
    "No D7/D10/D11/D12 source edited; versioning by naming + tags. Fourth invocation adds only "
    "release/Poincare/D13/HeatKernelBridge/PDERepair.lean (new) and small edits to the task's own "
    "All.lean (docstring) and AxiomAudit.lean (108 declarations); verified by diff -rq."
)

d["blocker_notes"] = (
    "The named blocker D7-HEAT-KERNEL-EXISTENCE is NOT claimed closed and exact_blockers_closed is []. "
    "The bridge delivers the corrected-domain interface, the D10 model inhabitant in every dimension, "
    "the compact finite-measure upgrade to the legacy type, the D7 statement-level equivalence, and "
    "(fourth invocation) a checked versioned predicate repair IsHeatKernelPDE (v2) with the genuine "
    "HasDerivAt PDE field, inhabited by the D10 kernel on the honest flat spacetime in every dimension. "
    "The manifold existence question (parametrix, parabolic regularity, Sobolev, spectral theory, Dirac "
    "delta, Gaussian bounds, maximum principle) remains open; no existence statement is introduced for "
    "the repaired predicate because HeatSpacetime does not constrain the laplacian."
)

d["fourth_invocation"] = {
    "when_utc": "2026-09-11T06:52:00Z",
    "what": ("fourth invocation of the same task: no completed work restarted. (a) Baseline re-verification "
             "of the frozen third-invocation artifact from byte-identical hashes. (b) One new companion "
             "release/Poincare/D13/HeatKernelBridge/PDERepair.lean (18 audited declarations) plus docstring "
             "extension of All.lean and AxiomAudit.lean extension to 108 declarations; no legacy source edited."),
    "new_file": "release/Poincare/D13/HeatKernelBridge/PDERepair.lean (292 lines, 18 audited declarations)",
    "extended_files": ["release/Poincare/D13/HeatKernelBridge/All.lean (docstring only)",
                       "release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean (90 -> 108 declarations, fourth downstream example)"],
    "baseline_hashes_match": True,
    "baseline_gates": ("build exit 0 (9186 jobs, D6AUDIT PASS); per-file 7/7; worktree 305/305; forbidden 0/0; "
                       "negative control PASS; diff only D13/ + V1Interface; upstream snapshot PASS"),
    "release_build": "exit 0 \u2014 Build completed successfully (9187 jobs), D6AUDIT PASS, axiom check PASS 108/108 (logs/d13_final_build.log)",
    "per_file_gate": "8/8 authored files exit 0 (logs/d13_final_perfile.txt)",
    "worktree_gate": "307/307 exit 0, 0 failures (logs/d13_final_gate_raw.txt)",
    "axiom_audit": "exit 0 \u2014 D13HeatKernelBridgeAxiomCheck: PASS 108/108 in {propext, Classical.choice, Quot.sound} (logs/d13_final_axiom_audit.out)",
    "forbidden_scan": "0 hard / 0 soft / 0 matches (logs/d13_final_forbidden_{d13,d7}.json)",
    "negcontrol": "PASS \u2014 detects sorryAx and the native_decide axiom (logs/d13_final_negcontrol.out)",
    "source_integrity": "diff -rq: only 'Only in release/Poincare: D13' and 'Only in release/Poincare/D7/HeatKernel: V1Interface.lean'; no builder source modified (logs/d13_final_diff.txt)",
    "upstream_snapshot": "tmp/verify_frenzymath_snapshot.py exit 0, commit bb91a091f0b968f8bbe8d861e025a88d82b161be, seven checks true (logs/d13_final_upstream.out)",
    "pde_repair_finding": ("the versioned IsHeatKernelPDE (v2) replaces the snapshot solves field by the genuine "
                           "pointwise HasDerivAt PDE field of the D11 core; the D10 kernel inhabits it on the honest "
                           "flat spacetime in every dimension on both admissible classes (flat_isHeatKernelPDE_integrable, "
                           "flat_isHeatKernelPDE_cc), while refuting the snapshot predicate in positive dimension "
                           "(flat_pde_repaired_scope); the repaired predicate does not imply the snapshot predicate "
                           "(not_forall_isHeatKernelPDE_imp_isHeatKernelV1). Model result only; no existence statement, "
                           "no blocker closure."),
    "not_a_closure": "exact_blockers_closed remains [] and D7-HEAT-KERNEL-EXISTENCE remains open",
}

P.write_text(json.dumps(d, indent=1, ensure_ascii=False) + "\n")
print("declarations:", len(d["proved_declarations"]))
print("source_hashes:", len(d["source_hashes"]))
print("compile_evidence:", len(d["compile_evidence"]))
print("json valid:", bool(json.loads(P.read_text())))
