#!/usr/bin/env python3
"""Patch tmp/update_result_json_sixth.py for the LaplacianSymmetryRefutation companion (sixth invocation)."""
p = 'tmp/update_result_json_sixth.py'
s = open(p).read()

def rep(a, b):
    global s
    assert s.count(a) == 1, ('MISS ' + a[:70])
    s = s.replace(a, b)

rep("'StatementRefutation and GeometricRepair companions) + D7 consumers Poincare.D7.HeatKernel.V1Interface, '",
    "'StatementRefutation, GeometricRepair and LaplacianSymmetryRefutation companions) + D7 consumers '\n"
    "               'Poincare.D7.HeatKernel.V1Interface, '")

rep("'OPEN (parametrix/parabolic regularity/Gaussian bounds/spectral theory absent from mathlib at the pinned revision).')",
    "'OPEN (parametrix/parabolic regularity/Gaussian bounds/spectral theory absent from mathlib at the pinned "
    "revision). The sixth invocation also adds LaplacianSymmetryRefutation.lean (11 declarations): the naive formal "
    "self-adjointness axiom is FALSE for the honest flat packaged Laplacian (u = 1, v = log cosh give "
    "∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v), so the classical integration-by-parts identity cannot be adjoined as a "
    "field of a repaired schematic interface.')")

rep(""" entry('Poincare.D7.HeatKernel.snapshot_refuted_data_exists_adversarialTimeDerivative', 'theorem', 'repaired hypotheses ∧ no IsHeatKernel witness ∧ ∃ matching HeatKernelData', 'D7 consumer, proved (contrast theorem)'),
]""",
""" entry('Poincare.D7.HeatKernel.snapshot_refuted_data_exists_adversarialTimeDerivative', 'theorem', 'repaired hypotheses ∧ no IsHeatKernel witness ∧ ∃ matching HeatKernelData', 'D7 consumer, proved (contrast theorem)'),
 entry(G+'hasDerivAt_tanh_real', 'theorem', 'HasDerivAt Real.tanh (1 - tanh x ^ 2) x', 'real analysis, proved'),
 entry(G+'tanh_eq_one_sub', 'theorem', 'tanh x = 1 - 2 / (exp (2x) + 1)', 'real analysis, proved'),
 entry(G+'tendsto_tanh_atTop_real', 'theorem', 'Tendsto Real.tanh atTop (𝓝 1)', 'real analysis, proved'),
 entry(G+'tendsto_tanh_atBot_real', 'theorem', 'Tendsto Real.tanh atBot (𝓝 (-1))', 'real analysis, proved'),
 entry(G+'flatLineSpacetime', 'def', 'HeatSpacetime ℝ with Lebesgue volume, packaged Laplacian, Euclidean distance, dim 1', 'model (honest 1D flat operator)'),
 entry(G+'hasDerivAt_log_cosh', 'theorem', 'HasDerivAt (fun y => log (cosh y)) (tanh x) x', 'real analysis, proved'),
 entry(G+'contDiff_log_cosh', 'theorem', 'ContDiff ℝ 2 (fun x => Real.log (Real.cosh x))', 'real analysis, proved'),
 entry(G+'laplacian_log_cosh', 'theorem', 'laplacianLinearMap ℝ (log ∘ cosh) = fun x => 1 - tanh x ^ 2', 'proved theorem (packaged flat Laplacian)'),
 entry(G+'integrable_one_sub_tanh_sq', 'theorem', 'Integrable (fun x : ℝ => 1 - tanh x ^ 2)', 'real analysis, proved'),
 entry(G+'integral_one_sub_tanh_sq', 'theorem', '∫ x : ℝ, (1 - tanh x ^ 2) = 2', 'real analysis, proved'),
 entry(G+'not_forall_laplacian_symmetric_flatLine', 'theorem', '¬ (∀ u v : ℝ → ℝ, ∫ u · Δv = ∫ Δu · v) for the honest flat packaged Laplacian', 'negative result, counterexample (interface diagnosis)'),
]""")
rep('assert len(new) == 51, len(new)', 'assert len(new) == 62, len(new)')

rep("""d['expanded_hypotheses']['repaired_statements'] = (""",
"""d['expanded_hypotheses']['laplacian_symmetry_refutation'] = (
 'LaplacianSymmetryRefutation.lean has no hypotheses beyond the definitions: hasDerivAt_tanh_real is unconditional, '
 'integral_one_sub_tanh_sq is the unconditional whole-line FTC evaluation, and '
 'not_forall_laplacian_symmetric_flatLine negates the universally quantified identity by evaluating it at u = 1 and '
 'v = log ∘ cosh. Integrability of 1 - tanh² is obtained from integrableOn_Ioi_deriv_of_nonneg plus the reflection '
 'substitution, not assumed.')
d['expanded_hypotheses']['repaired_statements'] = (""")

rep("""d['semantic_class']['d7_repair_status'] = (""",
"""d['semantic_class']['laplacian_symmetry_refutation'] = (
 'LaplacianSymmetryRefutation.lean (sixth invocation, companion note 5, 11 declarations): the naive all-functions '
 'Bochner-integral form of formal self-adjointness is FALSE for the honest 1-dimensional flat packaged Laplacian '
 '(u = 1, v = log ∘ cosh: ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v). This is a proved counterexample at the interface, '
 'replacing the earlier informal remark; it shows that the schematic interface cannot be repaired by adjoining the '
 'classical integration-by-parts identity as a field.')
d['semantic_class']['d7_repair_status'] = (""")

rep("d['axiom_evidence']['declaration_count'] = 177", "d['axiom_evidence']['declaration_count'] = 188")
rep("'D13HeatKernelBridgeAxiomCheck: PASS — all 177 declarations of the D13 heat-kernel '",
    "'D13HeatKernelBridgeAxiomCheck: PASS — all 188 declarations of the D13 heat-kernel '")
rep("""d['axiom_evidence']['breakdown'] = ('126 fifth-invocation declarations + 47 GeometricRepair declarations + 4 '
 'RepairStatus declarations = 177, each re-checked with Lean.collectAxioms in a fail-closed run_cmd '
 '(logs/d13_sixth_final_build.log, AxiomAudit.lean line 480)')""",
"""d['axiom_evidence']['breakdown'] = ('126 fifth-invocation declarations + 47 GeometricRepair declarations + 11 '
 'LaplacianSymmetryRefutation declarations + 4 RepairStatus declarations = 188, each re-checked with '
 'Lean.collectAxioms in a fail-closed run_cmd (logs/d13_sixth_final_build.log, AxiomAudit.lean line 503)')""")
rep("d['axiom_evidence']['sixth_invocation'] = ('The audit list in AxiomAudit.lean was extended by 51 entries;",
    "d['axiom_evidence']['sixth_invocation'] = ('The audit list in AxiomAudit.lean was extended by 62 entries;")

rep('"note": "sixth-invocation final suite: semantic transcripts 5 files exit 0, per-file 11/11, worktree 317/317, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 14 hashes (logs/d13_sixth_final_*)"',
    '"note": "sixth-invocation final suite: semantic transcripts 6 files exit 0, per-file 12/12, worktree 319/319, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 16 hashes (logs/d13_sixth_final_*)"')
rep('"note": "sixth-invocation final artifact: Build completed successfully (9191 jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS 177/177 (logs/d13_sixth_final_build.log)"',
    '"note": "sixth-invocation final artifact: Build completed successfully (9192 jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS 188/188 (logs/d13_sixth_final_build.log)"')
rep(""" {"command": "lake env lean tmp/d13_semantic_checks_e_d7_repair.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for the D7 consumer RepairStatus"},""",
""" {"command": "lake env lean tmp/d13_semantic_checks_e_d7_repair.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for the D7 consumer RepairStatus"},
 {"command": "lake env lean tmp/d13_semantic_checks_f_symmetry.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for LaplacianSymmetryRefutation (tanh calculus, Δ(log∘cosh), ∫(1-tanh²)=2, the refuted self-adjointness axiom)"},""")

rep('"what": ("Statement-level repair package: GeometricRepair.lean (47 declarations) + D7 consumer RepairStatus.lean "\n          "(4 declarations); AxiomAudit extended from 126 to 177 declarations; results card §18."),',
    '"what": ("Statement-level repair package: GeometricRepair.lean (47 declarations) + LaplacianSymmetryRefutation.lean "\n          "(11 declarations) + D7 consumer RepairStatus.lean (4 declarations); AxiomAudit extended from 126 to 188 "\n          "declarations; results card §18."),')
rep('"new_file": "release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean (47 declarations, audited)",',
    '"new_file": "release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean (47 declarations, audited) and release/Poincare/D13/HeatKernelBridge/LaplacianSymmetryRefutation.lean (11 declarations, audited)",')
rep('"D7-level consumption: on the adversarial datum the legacy IsHeatKernel has no witness while a matching genuine HeatKernelData exists (RepairStatus.lean).",',
    '"D7-level consumption: on the adversarial datum the legacy IsHeatKernel has no witness while a matching genuine HeatKernelData exists (RepairStatus.lean).",\n'
    '  "The naive formal self-adjointness axiom is FALSE for the honest 1-dimensional flat packaged Laplacian (LaplacianSymmetryRefutation.lean): u = 1 and v = log ∘ cosh give ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v, so the classical integration-by-parts identity cannot be adjoined as a field of the schematic interface.",')
rep('"final_gates": ("build 9191 jobs exit 0, D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 177/177, per-file 11/11, "\n                 "worktree 317/317, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 14 hashes "\n                 "(logs/d13_sixth_final_*)"),',
    '"final_gates": ("build 9192 jobs exit 0, D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 188/188, per-file 12/12, "\n                 "worktree 319/319, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 16 hashes "\n                 "(logs/d13_sixth_final_*)"),')
rep("d['source_hashes_note'] = ('Sixth-invocation hashes (logs/d13_sixth_final_hashes.txt): the 14 recorded hashes of the 12 '",
    "d['source_hashes_note'] = ('Sixth-invocation hashes (logs/d13_sixth_final_hashes.txt): the 16 recorded hashes of the 13 '")
rep('"when_utc": "2026-09-11T08:38Z-09:20Z (16:38-17:20 +08:00), elapsed ≈ 1.0 h",',
    '"when_utc": "2026-09-11T08:38Z-09:35Z (16:38-17:35 +08:00), elapsed ≈ 1.0 h",')
rep('"The naive self-adjointness/dissipativity axioms are not soundly stateable over the interface: their all-functions Bochner-integral forms are false for the honest packaged flat Laplacian (informal remark: u = 1, v = log cosh on ℝ gives ∫1·Δv = 2 ≠ 0 = ∫Δ1·v); the C_c/C² forms need a smooth normed structure the interface lacks.",',
    '"The naive self-adjointness axiom is FALSE for the honest 1-dimensional flat packaged Laplacian (LaplacianSymmetryRefutation.lean, PROVED: u = 1, v = log ∘ cosh give ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v); the C_c/C² forms of self-adjointness/dissipativity need a smooth normed structure the interface lacks, so the repair cannot proceed by adjoining such fields.",')

open(p, 'w').write(s)
print('patch applied to updater script')
