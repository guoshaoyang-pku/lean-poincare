#!/usr/bin/env python3
"""Sixth-invocation update of longrun/results/D13-heatkernel-bridge-d10-d7.json.

Idempotent: declaration entries are appended only if absent; scalar/dict fields are overwritten.
Run from the worktree root:  python3 tmp/update_result_json_sixth.py
"""
import json

P = 'longrun/results/D13-heatkernel-bridge-d10-d7.json'
d = json.load(open(P))

# ---------------------------------------------------------------- scalars
d['module'] = ('HeatKernelBridge (Poincare.D13.HeatKernelBridge, incl. the PredicateSemantics, PDERepair, '
               'StatementRefutation, GeometricRepair and LaplacianSymmetryRefutation companions) + D7 consumers '
               'Poincare.D7.HeatKernel.V1Interface, '
               'Poincare.D7.HeatKernel.StatementStatus and Poincare.D7.HeatKernel.RepairStatus')
d['generated_utc'] = '2026-09-11T09:20:00Z'
d['elapsed_hours'] = 4.05
d['elapsed_hours_this_invocation'] = 1.0
d['verdict'] = ('TASK_DONE (requests independent acceptance; no named blocker closed). The LONG_PLAN HeatKernelBridge '
 'module transports D10 HeatKernelEuclidean to the D7 HeatKernelData interface on the D12 corrected '
 'admissible-test-function domain; the D11 core inhabits the corrected-domain interface in every dimension (both '
 'admissible classes); compact finite-measure corrected-domain data upgrade to genuine legacy HeatKernelData with the '
 'upgrade a left inverse of the embedding; D7 modules consume the bridge (V1Interface: statement equivalence; '
 'StatementStatus: refutation transport; RepairStatus: the repaired-hypothesis datum refutes the legacy predicate '
 'while carrying a genuine HeatKernelData). 188/188 declarations in the approved axiom cone, all gates exit 0. Third '
 'invocation: PredicateSemantics — the D7 heat-equation field is a snapshot operator identity, not the PDE. Fourth '
 'invocation: PDERepair — versioned predicate IsHeatKernelPDE (v2) with the genuine HasDerivAt field, inhabited by the '
 'D10 kernel on the honest flat spacetime in every dimension, while refuting the snapshot predicate. Fifth invocation: '
 'StatementRefutation/StatementStatus — the D7 predicate-level existence statements are FALSE as formalized '
 '(IsClosedRiemannianManifold leaves laplacian/timeDerivative free; the one-point counterexample forces K = 0), plus '
 'the compact-scope existential equivalence exists_v1_iff_exists_legacy. Sixth invocation: GeometricRepair/RepairStatus '
 '— the statement-level repair package: (i) AnnihilatesConstants (Δ1 = 0) is the one sound geometric necessary '
 'condition expressible over the schematic interface; it excludes the refuting datum, is strictly stronger than the '
 'closed-manifold predicate, and holds for the honest flat Laplacian; (ii) a SECOND, independent statement-level '
 'refutation: the adversarial one-point spacetime (Δ = 0, ∂_t = id) satisfies the repaired hypotheses and admits no '
 'snapshot kernel, so no Laplacian-only repair can work; (iii) the time-rescaling theorem shows the snapshot and PDE '
 'predicates are INCOMPARABLE (a rescaled D10 kernel inhabits the former, fails the latter), so the heat-equation '
 'field must be replaced; (iv) the statement-level repaired interface HeatKernelExistenceStatementPDE / '
 'HeatKernelDataExistenceStatement (def … : Prop, stated not proved) is non-vacuous, has model inhabitants including '
 'on the adversarial datum, and the data-level form implies the predicate-level one. D7-HEAT-KERNEL-EXISTENCE remains '
 'OPEN (parametrix/parabolic regularity/Gaussian bounds/spectral theory absent from mathlib at the pinned revision). The sixth invocation also adds LaplacianSymmetryRefutation.lean (11 declarations): the naive formal self-adjointness axiom is FALSE for the honest flat packaged Laplacian (u = 1, v = log cosh give ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v), so the classical integration-by-parts identity cannot be adjoined as a field of a repaired schematic interface.')
d['blocker_notes'] = ('The named blocker D7-HEAT-KERNEL-EXISTENCE is NOT claimed closed and exact_blockers_closed is []. '
 'The bridge delivers the corrected-domain interface, the D10 model inhabitant in every dimension, the compact '
 'finite-measure upgrade to the legacy type, the D7 statement-level equivalence, a checked versioned predicate repair '
 'IsHeatKernelPDE (v2) with the genuine HasDerivAt PDE field (inhabited by the D10 kernel on the honest flat spacetime '
 'in every dimension), the compact-scope existential equivalence exists_v1_iff_exists_legacy, and (sixth invocation) '
 'the full statement-level repair package: the sound constant-annihilation condition excluding the refuting datum, a '
 'second independent statement-level refutation (the adversarial datum Δ = 0, ∂_t = id satisfies the repaired '
 'hypotheses and admits no snapshot kernel), the snapshot/PDE incomparability theorem, and the data-level repaired '
 'statement with model inhabitants. The D7 predicate-level existence statements are FALSE as formalized (two '
 'independent counterexamples), so the manifold existence question cannot be discharged against them: the honest '
 'target is the data-level PDE interface. The analytic gap (parametrix, parabolic regularity, Sobolev, spectral '
 'theory, Dirac delta, Gaussian bounds, maximum principle) remains open.')
d['legacy_policy'] = ('No D7/D10/D11/D12 source edited; versioning by naming + tags. The sixth invocation adds only '
 'release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean (new) and release/Poincare/D7/HeatKernel/RepairStatus.lean '
 '(new), plus docstring updates in the task\'s own All.lean and the AxiomAudit.lean extension to 177 declarations; '
 'verified by diff -rq.')
d['source_hashes_note'] = ('Sixth-invocation hashes (logs/d13_sixth_final_hashes.txt): the 16 recorded hashes of the 13 '
 'authored Lean files and the 3 build-config files, taken on the frozen final artifact before the final gate run. The '
 'fifth-invocation hashes were re-computed byte-identical before any sixth-invocation write '
 '(sha256sum -c logs/d13_fifth_final_hashes.txt: 13/13 OK).')

# ---------------------------------------------------------------- source hashes
hashes = {}
for line in open('logs/d13_sixth_final_hashes.txt'):
    line = line.strip()
    if line:
        h, f = line.split(None, 1)
        hashes[f] = h
d['source_hashes'] = hashes

# ---------------------------------------------------------------- declarations (idempotent)
G = 'Poincare.D13.HeatKernelBridge.'
def entry(name, kind, typ, sem):
    return {"name": name, "kind": kind, "type": typ, "semantic_class": sem}

new = [
 entry(G+'AnnihilatesConstants', 'structure', '(S : HeatSpacetime M) : Prop with field laplacian_one : S.laplacian 1 = 0', 'proved-interface predicate (sound geometric condition)'),
 entry(G+'AnnihilatesConstants.laplacian_one_apply', 'theorem', 'AnnihilatesConstants S → ∀ x, S.laplacian 1 x = 0', 'proved theorem'),
 entry(G+'not_isAnnihilatesConstants_refutingSpacetime', 'theorem', '¬ AnnihilatesConstants refutingSpacetime', 'counterexample exclusion, proved'),
 entry(G+'exists_isClosedRiemannianManifold_not_isAnnihilatesConstants', 'theorem', '∃ S : HeatSpacetime PUnit, IsClosedRiemannianManifold S ∧ ¬ AnnihilatesConstants S', 'strictness of the repair hypothesis, proved'),
 entry(G+'punitDiracSpacetime', 'def', 'HeatSpacetime PUnit with volume = Dirac, laplacian = 0, timeDerivative = 0, dist = 0, dim = 0', 'model'),
 entry(G+'punitDiracSpacetime_volume', 'theorem', 'punitDiracSpacetime.volume = Measure.dirac PUnit.unit', 'model field lemma'),
 entry(G+'punitDiracSpacetime_laplacian', 'theorem', 'punitDiracSpacetime.laplacian = 0', 'model field lemma'),
 entry(G+'punitDiracSpacetime_timeDerivative', 'theorem', 'punitDiracSpacetime.timeDerivative = 0', 'model field lemma'),
 entry(G+'punitDiracSpacetime_dist', 'theorem', 'punitDiracSpacetime.dist x y = 0', 'model field lemma'),
 entry(G+'punitDiracSpacetime_dim', 'theorem', 'punitDiracSpacetime.dim = 0', 'model field lemma'),
 entry(G+'punitDiracSpacetime_isClosedRiemannianManifold', 'theorem', 'IsClosedRiemannianManifold punitDiracSpacetime', 'model certificate, proved'),
 entry(G+'isAnnihilatesConstants_punitDiracSpacetime', 'theorem', 'AnnihilatesConstants punitDiracSpacetime', 'model satisfies the repair condition, proved'),
 entry(G+'flatHeatSpacetime_laplacian_one', 'theorem', '(flatHeatSpacetime n).laplacian 1 = 0 for every n', 'honest flat operator check, proved'),
 entry(G+'adversarialTimeDerivativeSpacetime', 'def', 'HeatSpacetime PUnit with volume = Dirac, laplacian = 0, timeDerivative = LinearMap.id, dist = 0, dim = 0', 'model/counterexample'),
 entry(G+'adversarialTimeDerivativeSpacetime_volume', 'theorem', 'adversarialTimeDerivativeSpacetime.volume = Measure.dirac PUnit.unit', 'counterexample lemma'),
 entry(G+'adversarialTimeDerivativeSpacetime_laplacian', 'theorem', 'adversarialTimeDerivativeSpacetime.laplacian = 0', 'counterexample lemma'),
 entry(G+'adversarialTimeDerivativeSpacetime_timeDerivative', 'theorem', 'adversarialTimeDerivativeSpacetime.timeDerivative = LinearMap.id', 'counterexample lemma'),
 entry(G+'adversarialTimeDerivativeSpacetime_heatOperator', 'theorem', '∀ u, adversarialTimeDerivativeSpacetime.heatOperator u = u', 'counterexample lemma, proved'),
 entry(G+'adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold', 'theorem', 'IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime', 'counterexample certificate'),
 entry(G+'isAnnihilatesConstants_adversarialTimeDerivativeSpacetime', 'theorem', 'AnnihilatesConstants adversarialTimeDerivativeSpacetime', 'counterexample certificate (repaired hypotheses hold)'),
 entry(G+'not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime', 'theorem', '¬ ∃ K, IsHeatKernelV1 adversarialTimeDerivativeSpacetime C K', 'negative result, unconditional'),
 entry(G+'not_isHeatKernel_of_laplacian_zero_timeDerivative_id', 'theorem', '[Nonempty M] → S.laplacian = 0 → S.timeDerivative = LinearMap.id → ¬ IsHeatKernel S K', 'negative result, general schema'),
 entry(G+'not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id', 'theorem', 'same for IsHeatKernelV1 with an arbitrary admissible class', 'negative result, general schema'),
 entry(G+'not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting', 'theorem', 'universe-polymorphic conditional refutation of the constant-annihilating snapshot statement', 'negative result, universe-polymorphic'),
 entry(G+'not_forall_annihilatesConstants_implies_exists_snapshot_kernel', 'theorem', '¬ (∀ M S, IsClosedRiemannianManifold S → AnnihilatesConstants S → ∃ K, IsHeatKernelV1 S C K)', 'negative result, unconditional (universe 0)'),
 entry(G+'flatSnapshotSpacetime', 'def', 'HeatSpacetime (EuclideanSpace ℝ (Fin n)) with timeDerivative := laplacian', 'model'),
 entry(G+'flatSnapshotSpacetime_volume', 'theorem', '(flatSnapshotSpacetime n).volume = volume', 'model field lemma'),
 entry(G+'flatSnapshotSpacetime_laplacian', 'theorem', '(flatSnapshotSpacetime n).laplacian = (flatHeatKernelCore n).laplacian', 'model field lemma'),
 entry(G+'flatSnapshotSpacetime_timeDerivative', 'theorem', '(flatSnapshotSpacetime n).timeDerivative = (flatHeatKernelCore n).laplacian', 'model field lemma'),
 entry(G+'flatSnapshotSpacetime_dist', 'theorem', '(flatSnapshotSpacetime n).dist x y = ‖x - y‖', 'model field lemma'),
 entry(G+'flatSnapshotSpacetime_dim', 'theorem', '(flatSnapshotSpacetime n).dim = (n : ℝ)', 'model field lemma'),
 entry(G+'flatSnapshotSpacetime_heatOperator_eq_zero', 'theorem', '∀ u, (flatSnapshotSpacetime n).heatOperator u = 0', 'vacuity of the snapshot field under timeDerivative = laplacian, proved'),
 entry(G+'flatKernelRescaled', 'def', 'fun x y t => flatKernel n x y (c * t)', 'counterexample kernel'),
 entry(G+'flatKernelRescaled_isHeatKernelV1', 'theorem', '0 < c → IsHeatKernelV1 (flatSnapshotSpacetime n) C (flatKernelRescaled n c)', 'counterexample, proved'),
 entry(G+'flatKernel_laplacian_snapshot_ne_zero_of_pos', 'theorem', '0 < n → 0 < t → (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 t) 0 ≠ 0', 'proved theorem'),
 entry(G+'flatKernelRescaled_not_isHeatKernelPDE', 'theorem', '0 < n → ¬ IsHeatKernelPDE (flatSnapshotSpacetime n) C (flatKernelRescaled n 2)', 'counterexample, proved'),
 entry(G+'not_forall_isHeatKernelV1_imp_isHeatKernelPDE', 'theorem', '¬ (∀ M S C K, IsHeatKernelV1 S C K → IsHeatKernelPDE S C K)', 'negative result (predicate incomparability, forward)'),
 entry(G+'snapshot_pde_predicates_incomparable', 'theorem', 'both non-implications between IsHeatKernelPDE and IsHeatKernelV1', 'negative result, proved'),
 entry(G+'HeatKernelExistenceStatementPDE', 'def', '∀ M S, IsClosedRiemannianManifold S → AnnihilatesConstants S → ∀ y₀, ∃ K, IsHeatKernelPDE S C K', 'statement-only (repaired interface, stated not proved)'),
 entry(G+'HeatKernelDataExistenceStatement', 'def', '∀ M S, IsClosedRiemannianManifold S → AnnihilatesConstants S → ∀ y₀, ∃ D : HeatKernelData M matching volume/dist/dim/laplacian, positive, 0 < D.C_lo', 'statement-only (honest data-level target, stated not proved)'),
 entry(G+'heatKernelDataExistenceStatement_implies_pde', 'theorem', 'HeatKernelDataExistenceStatement.{u} → HeatKernelExistenceStatementPDE.{u}', 'conditional interface, proved'),
 entry(G+'exists_isHeatKernelPDE_of_punit_dirac_zero', 'theorem', 'S.volume = Dirac → S.laplacian = 0 → ∃ K, IsHeatKernelPDE S C K on PUnit', 'model witness, proved'),
 entry(G+'heatKernelExistenceStatementPDE_conclusion_punit', 'theorem', '∃ K, IsHeatKernelPDE punitDiracSpacetime C K', 'model, proved'),
 entry(G+'heatKernelExistenceStatementPDE_conclusion_adversarial', 'theorem', '∃ K, IsHeatKernelPDE adversarialTimeDerivativeSpacetime C K', 'model, proved (repaired conclusion on the refuting datum)'),
 entry(G+'heatKernelDataExistenceStatement_conclusion_punit', 'theorem', '∃ D : HeatKernelData PUnit matching punitDiracSpacetime, positive, 0 < D.C_lo', 'model, proved'),
 entry(G+'heatKernelDataExistenceStatement_conclusion_adversarial', 'theorem', '∃ D : HeatKernelData PUnit matching adversarialTimeDerivativeSpacetime, positive, 0 < D.C_lo', 'model, proved (data conclusion on the refuting datum)'),
 entry(G+'not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime', 'theorem', '¬ (IsClosedRiemannianManifold refutingSpacetime ∧ AnnihilatesConstants refutingSpacetime)', 'negative result, proved'),
 entry('Poincare.D7.HeatKernel.adversarial_datum_repaired_hypotheses', 'theorem', 'IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime ∧ AnnihilatesConstants adversarialTimeDerivativeSpacetime', 'D7 consumer, proved'),
 entry('Poincare.D7.HeatKernel.not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime', 'theorem', '¬ ∃ K, IsHeatKernel adversarialTimeDerivativeSpacetime K', 'D7 consumer, negative result'),
 entry('Poincare.D7.HeatKernel.exists_heatKernelData_adversarialTimeDerivativeSpacetime', 'theorem', '∃ D : HeatKernelData PUnit matching adversarialTimeDerivativeSpacetime, positive, 0 < D.C_lo', 'D7 consumer, model'),
 entry('Poincare.D7.HeatKernel.snapshot_refuted_data_exists_adversarialTimeDerivative', 'theorem', 'repaired hypotheses ∧ no IsHeatKernel witness ∧ ∃ matching HeatKernelData', 'D7 consumer, proved (contrast theorem)'),
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
]
assert len(new) == 62, len(new)
have = {e['name'] for e in d['proved_declarations']}
d['proved_declarations'] = d['proved_declarations'] + [e for e in new if e['name'] not in have]

# ---------------------------------------------------------------- expanded hypotheses
d['expanded_hypotheses']['geometric_repair'] = ('AnnihilatesConstants S := S.laplacian 1 = 0 is a Lean-level Prop '
 'with no typeclass content; its hypotheses are expanded to the field equality itself. The model theorems have no '
 'hypotheses beyond the definitions; the honest-flat check uses the D11 packaged Δ via '
 'laplacianLinearMap_apply_of_contDiff and mathlib laplacian_const. The refutation schemata assume only '
 '[Nonempty M], S.laplacian = 0 and S.timeDerivative = LinearMap.id.')
d['expanded_hypotheses']['time_rescaling'] = ('flatKernelRescaled_isHeatKernelV1 assumes 0 < c only; '
 'flatKernelRescaled_not_isHeatKernelPDE assumes 0 < n; the chain-rule failure is at x = y = 0, t = 1 with the '
 'derivative 2·ΔK(·,0,2) computed from flatHeatKernelCore_heatEquation and the diagonal value '
 'ΔK(0,0,2) = K(0,0,2)·(-n/4) from laplacian_gaussianKernel.')
d['expanded_hypotheses']['laplacian_symmetry_refutation'] = (
 'LaplacianSymmetryRefutation.lean has no hypotheses beyond the definitions: hasDerivAt_tanh_real is unconditional, '
 'integral_one_sub_tanh_sq is the unconditional whole-line FTC evaluation, and '
 'not_forall_laplacian_symmetric_flatLine negates the universally quantified identity by evaluating it at u = 1 and '
 'v = log ∘ cosh. Integrability of 1 - tanh² is obtained from integrableOn_Ioi_deriv_of_nonneg plus the reflection '
 'substitution, not assumed.')
d['expanded_hypotheses']['repaired_statements'] = ('HeatKernelExistenceStatementPDE / HeatKernelDataExistenceStatement '
 'are def … : Prop (statement-only, not assumed anywhere); heatKernelDataExistenceStatement_implies_pde has the '
 'statement as its only hypothesis and needs no positivity of C_lo (the data statement carries kernel positivity '
 'explicitly).')

# ---------------------------------------------------------------- semantic classes
d['semantic_class']['geometric_repair'] = ('GeometricRepair.lean (sixth invocation, 47 declarations): the sound '
 'constant-annihilation condition AnnihilatesConstants (proved-interface predicate), its counterexample exclusion and '
 'strictness (proved), its zero-dimensional and adversarial models (model), the honest flat operator check (proved), '
 'the second statement-level refutation (negative result, general and universe-polymorphic), the time-rescaling '
 'counterexample and the snapshot/PDE incomparability (proved), and the statement-only repaired interface '
 'HeatKernelExistenceStatementPDE / HeatKernelDataExistenceStatement with conditional implication and model '
 'inhabitants. The self-adjointness/dissipativity formulation is an INFORMAL REMARK in the module docstring '
 '(unformalized), explicitly distinguished from the checked constant-annihilation condition.')
d['semantic_class']['laplacian_symmetry_refutation'] = (
 'LaplacianSymmetryRefutation.lean (sixth invocation, companion note 5, 11 declarations): the naive all-functions '
 'Bochner-integral form of formal self-adjointness is FALSE for the honest 1-dimensional flat packaged Laplacian '
 '(u = 1, v = log ∘ cosh: ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v). This is a proved counterexample at the interface, '
 'replacing the earlier informal remark; it shows that the schematic interface cannot be repaired by adjoining the '
 'classical integration-by-parts identity as a field.')
d['semantic_class']['d7_repair_status'] = ('Poincare.D7.HeatKernel.RepairStatus (sixth invocation, 4 declarations): '
 'D7-level consumption of the repair; on one closed Riemannian datum satisfying the constant-annihilation condition '
 'the legacy IsHeatKernel has no witness while a matching genuine HeatKernelData exists — the D7-level statement that '
 'the repair must replace the heat-equation field.')

# ---------------------------------------------------------------- blockers and requests
d['remaining_blockers'] = [
 'D7-HEAT-KERNEL-EXISTENCE (manifold heat-kernel existence: parametrix/Levi, Duhamel, short-time existence) — OPEN, and by §17/§18 not closable against the snapshot statement (two independent refutations); the honest target is the data-level statement HeatKernelDataExistenceStatement',
 'B-D7-PARABOLIC-REGULARITY (Schauder estimates, Hölder spaces, smoothness of weak solutions) — OPEN',
 'B-D7-SOBOLEV-EMBEDDING (Sobolev spaces on manifolds, embedding, Rellich–Kondrachov) — OPEN',
 'B-D7-SPECTRAL-THEOREM (Laplace–Beltrami spectral theorem, eigenfunction expansion, Hille–Yosida) — OPEN',
 'B-D7-DIRAC-DELTA (distribution theory; currently only continuous-test-function limits) — OPEN',
 'B-D7-GAUSSIAN-BOUNDS (Li–Yau, heat-kernel estimates on manifolds) — OPEN',
 'B-D7-MAXIMUM-PRINCIPLE (parabolic maximum principle, positivity/uniqueness) — OPEN',
 'Riemannian-metric/Laplace–Beltrami formalization (a metric theory pinning laplacian to the geometric operator; mathlib at the pinned revision has RiemannianMetric bundles but no Laplace–Beltrami operator) — OPEN, and now known to be necessary for any statement-level repair beyond AnnihilatesConstants',
 'Sound statement of the classical integration-by-parts/dissipativity conditions over the schematic interface (the all-functions Bochner-integral forms are false for the honest packaged flat Laplacian — informal remark, §18.2) — OPEN interface obligation',
]
d['next_dependency_requests'] = [
 'STATEMENT REPAIR (resolved in direction; still blocking D7-HEAT-KERNEL-EXISTENCE): the D7 predicate-level existence statements are refuted twice over — (i) the original counterexample (laplacian = id, ∂_t = 0) and (ii) the sixth-invocation adversarial datum (Δ = 0, ∂_t = id) which satisfies the constant-annihilation condition. The snapshot field is moreover incomparable with the PDE field, so no hypothesis on the operators can repair it. Do not attempt to prove HeatKernelExistenceStatement / HeatKernelExistenceStatementV1. Use HeatKernelExistenceStatementPDE / HeatKernelDataExistenceStatement instead.',
 'MANIFOLD-SIDE TASKS: attack the data-level statement HeatKernelDataExistenceStatement (genuine HasDerivAt heat equation, Gaussian bounds, positivity, Dirac) over a genuinely geometric interface; this is the honest remaining mathematical content of the named blocker.',
 'RIEMANNIAN INTERFACE: provide a metric-based Laplacian (Laplace–Beltrami) and the compact-manifold volume/distance data, so that the hypothesis class of HeatKernelDataExistenceStatement can be narrowed from AnnihilatesConstants to a true geometric pinning; note that the classical integration-by-parts/dissipativity identities cannot be stated soundly with the schematic Bochner integral.',
 'D12-heat-semigroup-analysis / D13-deturck-shorttime-producer: consume flatHeatKernelDataV1_integrable / flatHeatKernelDataV1_cc as the checked corrected-domain model datum.',
 'COMPACT FINITE-MEASURE DOWNSTREAM USERS: use toHeatKernelData_of_integrableClass / toHeatKernelData_of_ccClass (and exists_v1_iff_exists_legacy) to upgrade corrected-domain data to the legacy D7 type.',
 'INDEPENDENT SEMANTIC ACCEPTANCE of the 12 authored modules by a fresh reviewer (hash-pinned, logs/d13_sixth_final_hashes.txt): the v1 bridge interface and transport, the compact upgrade, the predicate semantics, the PDE repair, the two statement-level refutations, the statement-level repair package (constant annihilation, adversarial refutation, incomparability, repaired statements), and the three D7 consumers.',
]

# ---------------------------------------------------------------- evidence
d['compile_evidence'] = [e for e in d['compile_evidence']
                         if e.get('note', '').find('sixth-invocation') < 0] + [
 {"command": "bash tmp/d13_sixth_gates.sh d13_sixth_baseline", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation baseline on the frozen fifth-invocation artifact: 13/13 hashes OK, build 9189 jobs exit 0, AxiomAudit PASS 126/126, per-file 10/10, worktree 313/313, forbidden 0/0, negcontrol PASS, diff 3 lines, upstream PASS"},
 {"command": "lake build", "cwd": "release/", "exit": 0,
  "note": "sixth-invocation final artifact: Build completed successfully (9192 jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS 188/188 (logs/d13_sixth_final_build.log)"},
 {"command": "bash tmp/d13_sixth_gates.sh d13_sixth_final", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation final suite: semantic transcripts 6 files exit 0, per-file 12/12, worktree 319/319, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 16 hashes (logs/d13_sixth_final_*)"},
 {"command": "lake env lean tmp/d13_semantic_checks_d_geometric.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for GeometricRepair (constant annihilation, refutations, time rescaling, repaired statements)"},
 {"command": "lake env lean tmp/d13_semantic_checks_e_d7_repair.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for the D7 consumer RepairStatus"},
 {"command": "lake env lean tmp/d13_semantic_checks_f_symmetry.lean", "cwd": "worktree root", "exit": 0,
  "note": "sixth-invocation #check/#print axioms transcript for LaplacianSymmetryRefutation (tanh calculus, Δ(log∘cosh), ∫(1-tanh²)=2, the refuted self-adjointness axiom)"},
]
d['axiom_evidence']['declaration_count'] = 188
d['axiom_evidence']['check'] = ('D13HeatKernelBridgeAxiomCheck: PASS — all 188 declarations of the D13 heat-kernel '
 'bridge depend only on [propext, Classical.choice, Quot.sound]')
d['axiom_evidence']['breakdown'] = ('126 fifth-invocation declarations + 47 GeometricRepair declarations + 11 '
 'LaplacianSymmetryRefutation declarations + 4 RepairStatus declarations = 188, each re-checked with '
 'Lean.collectAxioms in a fail-closed run_cmd (logs/d13_sixth_final_build.log, AxiomAudit.lean line 503)')
d['axiom_evidence']['sixth_invocation'] = ('The audit list in AxiomAudit.lean was extended by 62 entries; the '
 'programmatic re-check aborts the build on any axiom outside {propext, Classical.choice, Quot.sound}. Negative '
 'control still PASS (the predicate detects sorryAx and the native_decide axiom).')

# ---------------------------------------------------------------- invocation record
d['sixth_invocation'] = {
 "when_utc": "2026-09-11T08:38Z-09:26Z (16:38-17:26 +08:00), elapsed ≈ 0.8 h",
 "what": ("Statement-level repair package: GeometricRepair.lean (47 declarations) + LaplacianSymmetryRefutation.lean "
          "(11 declarations) + D7 consumer RepairStatus.lean (4 declarations); AxiomAudit extended from 126 to 188 "
          "declarations; results card §18."),
 "context": ("The fifth invocation proved the D7 predicate-level existence statements false as formalized and left "
             "the repair direction open. The sixth invocation determines exactly how far the statement can be "
             "repaired without a metric theory."),
 "baseline_hashes_match": "13/13 sha256sum -c OK on logs/d13_fifth_final_hashes.txt (byte-identical)",
 "baseline_gates": ("build 9189 jobs exit 0, D6AUDIT PASS, AxiomAudit PASS 126/126, per-file 10/10, worktree "
                    "313/313, forbidden 0/0, negcontrol PASS, diff 3 lines, upstream PASS "
                    "(logs/d13_sixth_baseline_*)"),
 "findings": [
  "The one sound geometric necessary condition expressible over the schematic interface is AnnihilatesConstants (Δ1 = 0); it excludes the refuting spacetime and holds for the honest flat D10 Laplacian.",
  "The naive self-adjointness axiom is FALSE for the honest 1-dimensional flat packaged Laplacian (LaplacianSymmetryRefutation.lean, PROVED: u = 1, v = log ∘ cosh give ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v); the C_c/C² forms of self-adjointness/dissipativity need a smooth normed structure the interface lacks, so the repair cannot proceed by adjoining such fields.",
  "Second, independent statement-level refutation: the adversarial one-point spacetime (Δ = 0, ∂_t = id) satisfies IsClosedRiemannianManifold ∧ AnnihilatesConstants and admits no snapshot kernel; the Laplacian-only repair of D7-HEAT-KERNEL-EXISTENCE is dead (proved for the legacy and corrected-domain predicates, general and universe-polymorphic).",
  "Pinning timeDerivative := laplacian makes the solves field vacuous; the time-rescaled D10 kernel then inhabits the snapshot predicate but fails the PDE, so the snapshot and PDE predicates are incomparable and the heat-equation field must be replaced, not constrained.",
  "The statement-level repaired interface (HeatKernelExistenceStatementPDE / HeatKernelDataExistenceStatement) is stated, not proved, and is non-vacuous: its conclusions hold on the zero-dimensional model and on the adversarial datum; the data-level form implies the predicate-level one.",
  "D7-level consumption: on the adversarial datum the legacy IsHeatKernel has no witness while a matching genuine HeatKernelData exists (RepairStatus.lean).",
  "The naive formal self-adjointness axiom is FALSE for the honest 1-dimensional flat packaged Laplacian (LaplacianSymmetryRefutation.lean): u = 1 and v = log ∘ cosh give ∫1·Δv = ∫(1 - tanh²) = 2 ≠ 0 = ∫Δ1·v, so the classical integration-by-parts identity cannot be adjoined as a field of the schematic interface.",
 ],
 "new_file": "release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean (47 declarations, audited) and release/Poincare/D13/HeatKernelBridge/LaplacianSymmetryRefutation.lean (11 declarations, audited)",
 "new_d7_file": "release/Poincare/D7/HeatKernel/RepairStatus.lean (4 declarations, audited)",
 "extended_files": "release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean (list extended to 177) and a docstring update in All.lean",
 "final_gates": ("build 9192 jobs exit 0, D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 188/188, per-file 12/12, "
                 "worktree 319/319, forbidden 0/0, negcontrol PASS, diff 4 expected lines, upstream PASS, 16 hashes "
                 "(logs/d13_sixth_final_*)"),
 "exact_blockers_closed": [],
}

json.dump(d, open(P, 'w'), indent=1, ensure_ascii=False)
print('json updated; declarations:', len(d['proved_declarations']))
