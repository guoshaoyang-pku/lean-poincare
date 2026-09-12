/-
Pass-5 independent acceptance probe (2026-09-12, continuation invocation) for the task
`L4-child-sturm-zero-interlacing`.

This probe was written from scratch for this pass.  It neither imports nor reuses
`tmp/gs_independent_probe.lean` (pass 4), `tmp/acceptance_probe_r3*.lean` (pass 3) or
`tmp/acceptance_probe_r2.lean` (pass 2).  Its purpose is to exercise the delivered theorems
on data chosen here, to exhibit a single term satisfying *all* hypotheses of the strict-gap
interlacing theorem at once (non-vacuity by construction), and to re-derive the required
acceptance items:

  * P5-1 — the literal acceptance branch is refuted and the exact first zero of `sin` is `π`;
  * P5-2 — the offered sharper two-curvature interlacing (`k₁ = 1` sin vs `k₂ = 1/2` model),
    including the explicit witness `π` and the first-zero ordering;
  * P5-3 — the infinite interlacing at `n = 1`, with the explicit zero `3π`;
  * P5-4 — zero counting with the acceptance normalization `u 0 = 0`, `u' 0 = 1` on the model
    `jacobiSol 2` against `K = 1`, plus the closed form `firstPositiveZero = π/√2`;
  * P5-5 — horizon form and attainment on fresh data `K = 9`, `k = 10`, horizon `H = 2`;
  * P5-6 — the equality case `k ≡ K = 5` producing the endpoint zero;
  * P5-7 — the Wronskian consumption at the fresh point `π/4`;
  * P5-8 — a hypothesis-satisfiability bundle: every hypothesis of `exists_zero_of_curvature_lt`
    holds simultaneously on the acceptance data, together with an explicit interior zero;
  * P5-9 — the cross-check against `conjugate_point_bound` on fresh equality-case data
    (`k ≡ K = 1`, `u = sin`, `T = π/2`), through the engine route and the leader route.

The `#print axioms` and `#print` lines at the end are parsed by `tools/acceptance_pass5.py`.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- (P5-1) The literal acceptance branch is refuted, and the first positive zero of `sin` is
exactly `π` (not `< π`). -/
theorem p5_literal_branch_refuted :
    (¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0) ∧ firstPositiveZero Real.sin = Real.pi :=
  ⟨sin_no_zero_in_Ioo_zero_pi, firstPositiveZero_sin⟩

/-- (P5-2) The offered sharper alternative: `sin` (`k₁ = 1`) interlaces with the constructed
`k₂ = 1/2` model, with the explicit zero `π` strictly between the model's zeros `0` and
`π/√(1/2)`, and the first-zero ordering. -/
theorem p5_sharper_interlacing :
    (∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), Real.sin c = 0) ∧
      Real.pi ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) ∧
      firstPositiveZero Real.sin < firstPositiveZero (jacobiSol (1 / 2)) :=
  ⟨sin_zero_interlaces_half_model.1, sin_zero_interlaces_half_model.2,
    firstPositiveZero_sin_lt_half_model⟩

/-- (P5-3) The infinite interlacing at `n = 1`: `sin` has a zero in `(2π, 4π)`, and the
explicit witness `3π` is exhibited. -/
theorem p5_infinite_interlacing_n1 :
    (∃ c ∈ Ioo (2 * Real.pi) (4 * Real.pi), Real.sin c = 0) ∧
      Real.sin (3 * Real.pi) = 0 ∧ 3 * Real.pi ∈ Ioo (2 * Real.pi) (4 * Real.pi) := by
  have hA : (2 : ℝ) * ((1 : ℤ) : ℝ) * Real.pi = 2 * Real.pi := by norm_num
  have hB : (2 : ℝ) * (((1 : ℤ) : ℝ) + 1) * Real.pi = 4 * Real.pi := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc, hcz⟩ := sin_interlaces_half_model_all (1 : ℤ)
    rw [hA, hB] at hc
    exact ⟨c, hc, hcz⟩
  · rw [Real.sin_eq_zero_iff]
    exact ⟨3, by push_cast; ring⟩
  · have h := (sin_zero_in_half_model_interval (1 : ℤ)).1
    rw [hA, hB] at h
    norm_num at h
    exact h

/-- (P5-4) Zero counting with the acceptance normalization: the model `jacobiSol 2` with
`u 0 = 0`, `u' 0 = 1` and `k = 2 ≥ K = 1` has a zero in `(0, π/√1]`; its first positive zero
is at most `π/√1`, and in closed form exactly `π/√2`. -/
theorem p5_zero_counting_normalized :
    (∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 1), jacobiSol 2 c = 0) ∧
      firstPositiveZero (jacobiSol 2) ≤ Real.pi / Real.sqrt 1 ∧
      firstPositiveZero (jacobiSol 2) = Real.pi / Real.sqrt 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  refine ⟨?_, ?_, firstPositiveZero_modelJacobiSol h2⟩
  · exact exists_jacobi_zero_on_Ioc_pi_sqrt_normalized (K := 1) (k := fun _ : ℝ => 2)
      (u := jacobiSol 2) (du := jacobiDeriv 2) (ddu := fun t => -(2 * jacobiSol 2 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 2 _) (jacobiSol_zero 2)
      (jacobiDeriv_zero 2)
  · exact firstPositiveZero_le_pi_sqrt (K := 1) (k := fun _ : ℝ => 2)
      (u := jacobiSol 2) (du := jacobiDeriv 2) (ddu := fun t => -(2 * jacobiSol 2 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 2 _) (jacobiSol_zero 2)

/-- (P5-5) Horizon form and attainment on fresh data: `K = 9`, `k = 10`, horizon `H = 2`.
The first positive zero is at most `π/3`, and it is a genuine positive zero of `jacobiSol 10`. -/
theorem p5_horizon_and_attainment :
    firstPositiveZero (jacobiSol 10) ≤ Real.pi / Real.sqrt 9 ∧
      jacobiSol 10 (firstPositiveZero (jacobiSol 10)) = 0 ∧
      0 < firstPositiveZero (jacobiSol 10) := by
  have hpi9 : Real.pi / Real.sqrt 9 ≤ 2 := by
    have hsqrt9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsqrt9]
    linarith [Real.pi_lt_four]
  have hle : firstPositiveZero (jacobiSol 10) ≤ Real.pi / Real.sqrt 9 :=
    firstPositiveZero_le_pi_sqrt_of_horizon (K := 9) (H := 2) (k := fun _ : ℝ => 10)
      (u := jacobiSol 10) (du := jacobiDeriv 10) (ddu := fun t => -(10 * jacobiSol 10 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 10 2)
      (jacobiSol_zero 10) hpi9
  have hmem := firstPositiveZero_mem_of_normalized (K := 9) (k := fun _ : ℝ => 10)
    (u := jacobiSol 10) (du := jacobiDeriv 10) (ddu := fun t => -(10 * jacobiSol 10 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 10 _) (jacobiSol_zero 10)
    (jacobiDeriv_zero 10)
  exact ⟨hle, hmem.1, hmem.2.1⟩

/-- (P5-6) The equality case `k ≡ K = 5`: the endpoint `π/√5` is a zero of `jacobiSol 5`, and
the closed-interval zero count holds for the model. -/
theorem p5_equality_case_five :
    jacobiSol 5 (Real.pi / Real.sqrt 5) = 0 ∧
      (∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 5), jacobiSol 5 c = 0) := by
  have h5 : (0 : ℝ) < 5 := by norm_num
  refine ⟨modelJacobiSol_firstZero h5, ?_⟩
  exact exists_jacobi_zero_on_Ioc_pi_sqrt (K := 5) (k := fun _ : ℝ => 5)
    (u := jacobiSol 5) (du := jacobiDeriv 5) (ddu := fun t => -(5 * jacobiSol 5 t))
    h5 (fun _ _ => le_rfl) (modelJacobiSolutionOn 5 _) (jacobiSol_zero 5)

/-- (P5-7) Wronskian consumption at the fresh point `π/4`: the antitone value inequality
`W (π/4) ≤ W 0` and the explicit strictly negative derivative `W' (π/4) = −π√2/8`. -/
theorem p5_wronskian_consequences :
    wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1) (Real.pi / 4)
        ≤ wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1) 0 ∧
      deriv (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) (Real.pi / 4)
        = -(Real.pi * Real.sqrt 2 / 8) := by
  constructor
  · exact wronskian_sin_linear_antitoneOn (left_mem_Icc.mpr Real.pi_pos.le)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  · rw [wronskian_deriv_sin_linear ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      Real.sin_pi_div_four]
    ring

/-- (P5-8) **Hypothesis-satisfiability bundle.**  Every hypothesis of the strict-gap
interlacing theorem `exists_zero_of_curvature_lt` holds simultaneously on the acceptance
data (`k₁ = 1`, `u₁ = sin`; `k₂ = 1/2`, `u₂ = jacobiSol (1/2)` on `(0, π/√(1/2))`), and an
explicit interior zero `c = π` of `u₁` is produced.  This is a non-vacuity certificate for
the theorem's hypothesis list, not merely for its conclusion. -/
theorem p5_hypotheses_satisfiable :
    ∃ (k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ) (a b c : ℝ),
      a < b ∧ (∀ t ∈ Icc a b, k₂ t ≤ k₁ t) ∧
        JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b ∧ JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b ∧
        u₁ a = 0 ∧ u₂ a = 0 ∧ u₂ b = 0 ∧
        (∀ t ∈ Ioo a b, 0 < u₂ t) ∧ HasDerivAtR u₂ (du₂ b) b ∧
        (∃ t ∈ Ioo a b, k₂ t < k₁ t) ∧ c ∈ Ioo a b ∧ u₁ c = 0 := by
  have hK₂ : (0 : ℝ) < 1 / 2 := by norm_num
  have hb : 0 < Real.pi / Real.sqrt (1 / 2) := div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK₂)
  refine ⟨fun _ : ℝ => 1, fun _ : ℝ => 1 / 2, Real.sin, Real.cos, fun t => -Real.sin t,
    jacobiSol (1 / 2), jacobiDeriv (1 / 2), fun t => -((1 / 2) * jacobiSol (1 / 2) t),
    0, Real.pi / Real.sqrt (1 / 2), Real.pi, hb, fun _ _ => by norm_num,
    sinJacobiSolutionOn 0 _, modelJacobiSolutionOn (1 / 2) _, Real.sin_zero,
    jacobiSol_zero (1 / 2), modelJacobiSol_firstZero hK₂, modelJacobiSol_pos hK₂,
    hasDerivAt_jacobiSol (1 / 2) _, ?_, sin_zero_interlaces_half_model.2, Real.sin_pi⟩
  exact ⟨Real.pi / Real.sqrt (1 / 2) / 2, ⟨by linarith, by linarith⟩, by norm_num⟩

/-- (P5-9) Cross-check on fresh equality-case data `k ≡ K = 1`, `u = sin`, `T = π/2`: the
engine route gives `π/2 ≤ π/√1`. -/
theorem p5_cross_check_sin_engine : Real.pi / 2 ≤ Real.pi / Real.sqrt 1 := by
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < Real.sin t := by
    intro t ht
    exact Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_of_le_of_lt ht.2 (by linarith [Real.pi_pos]))
  exact no_positive_solution_past_pi_sqrt (K := 1) (k := fun _ : ℝ => 1)
    (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (T := Real.pi / 2) (by linarith [Real.pi_pos]) (sinJacobiSolutionOn 0 (Real.pi / 2))
    Real.sin_zero hpos (by norm_num) (fun t _ => le_rfl)

/-- (P5-9b) The identical proposition through the leader's theorem with its full quantitative
hypothesis list (`B = 1`, `t₀ = 1/4`): both routes agree. -/
theorem p5_cross_check_sin_leader : Real.pi / 2 ≤ Real.pi / Real.sqrt 1 := by
  have hpos : ∀ t ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < Real.sin t := by
    intro t ht
    exact Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_of_le_of_lt ht.2 (by linarith [Real.pi_pos]))
  refine conjugate_point_bound_cross_check (K := 1) (k := fun _ : ℝ => 1)
    (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (T := Real.pi / 2) (B := 1) (t₀ := 1 / 4)
    (by linarith [Real.pi_pos]) (by norm_num) (by norm_num) (by linarith [Real.pi_gt_three])
    (by norm_num) (sinJacobiSolutionOn 0 (Real.pi / 2)) ?_ ?_ Real.sin_zero (by simp)
    hpos (by norm_num) (fun t _ => le_rfl) ?_
  · exact Real.continuous_sin.neg.continuousOn
  · intro t _
    rw [abs_neg]
    exact Real.abs_sin_le_one t
  · rw [Real.sqrt_one, max_eq_right (by linarith [Real.pi_gt_three])]
    nlinarith [Real.pi_lt_four]

end Poincare.L4.GeodesicComparison

/-! ## Axiom cones of the probe declarations -/

#print axioms Poincare.L4.GeodesicComparison.p5_literal_branch_refuted
#print axioms Poincare.L4.GeodesicComparison.p5_sharper_interlacing
#print axioms Poincare.L4.GeodesicComparison.p5_infinite_interlacing_n1
#print axioms Poincare.L4.GeodesicComparison.p5_zero_counting_normalized
#print axioms Poincare.L4.GeodesicComparison.p5_horizon_and_attainment
#print axioms Poincare.L4.GeodesicComparison.p5_equality_case_five
#print axioms Poincare.L4.GeodesicComparison.p5_wronskian_consequences
#print axioms Poincare.L4.GeodesicComparison.p5_hypotheses_satisfiable
#print axioms Poincare.L4.GeodesicComparison.p5_cross_check_sin_engine
#print axioms Poincare.L4.GeodesicComparison.p5_cross_check_sin_leader

/-! ## Proof-term provenance of the engine consumption

`#print` of the deliverable's engine-consuming declarations; `tools/acceptance_pass5.py`
checks that the printed proof terms actually mention the D12 engine declarations. -/

#print Poincare.L4.GeodesicComparison.exists_zero_of_curvature_lt
#print Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt
#print Poincare.L4.GeodesicComparison.sturm_dichotomy_of_interior_bound
#print Poincare.L4.GeodesicComparison.eq_zero_at_pi_sqrt_of_curvature_eq
#print Poincare.L4.GeodesicComparison.wronskian_sin_linear_antitoneOn
#print Poincare.L4.GeodesicComparison.wronskian_deriv_sin_linear
#print Poincare.L4.GeodesicComparison.no_positive_solution_past_pi_sqrt
