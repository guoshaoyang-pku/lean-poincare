/-
Independent acceptance probe (second invocation, 2026-09-12) for the task
`L4-child-sturm-zero-interlacing`.

Written from scratch against the frozen deliverable modules; it does not import or reuse
`tmp/acceptance_probe_r2.lean` or `tmp/acceptance_probe_r3*.lean`.  Every statement below is
an instance on data chosen by this probe, exercising the three required acceptance items:

  * GS1/GS1b — two-curvature zero interlacing (`exists_zero_of_curvature_lt`) on the pair
    (`jacobiSol 3`, `jacobiSolShift (1/4) 0`), which is not one of the deliverable's examples;
  * GS2/GS2b/GS2c/GS2d — the first-positive-zero bound and its horizon/attainment forms on
    `jacobiSol 5` against `K = 2` and `K = 4`;
  * GS3 — the equality-case endpoint zero (`eq_zero_at_pi_sqrt_of_curvature_eq`);
  * GS4/GS4b — the Wronskian monotonicity/derivative consumption at the fresh point `π/3`;
  * GS5/GS5b — the refutation of the literal acceptance branch (prior art, reused by name);
  * GS6 — the leader cross-check `conjugate_point_bound` on fresh data (`k = 3`, `K = 1`,
    `T = 3/2`), through the engine route, the leader theorem and the cross-check wrapper.

Compilation of this file is the evidence.  `#print axioms` lines at the end are parsed by
`tools/gs_independent_check.py`.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- (GS1) `jacobiSol 3` (curvature `3`) vanishes at `π/√3`, and that point lies strictly
inside `(0, π/√(1/4)) = (0, 2π)`, the interval spanned by the consecutive zeros `0`, `2π` of
the `k = 1/4` model. -/
theorem gs1_interlacing_instance :
    jacobiSol 3 (Real.pi / Real.sqrt 3) = 0 ∧
      Real.pi / Real.sqrt 3 ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 4)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos h3
  have hq : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨modelJacobiSol_firstZero h3, ⟨div_pos Real.pi_pos hs3, ?_⟩⟩
  rw [hq]
  have hlt : Real.pi / Real.sqrt 3 < Real.pi / (1 / 2) := by
    refine div_lt_div_of_pos_left Real.pi_pos (by norm_num) ?_
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  simpa using hlt

/-- (GS1b) The engine wrapper `exists_zero_of_curvature_lt` instantiated on the same fresh
pair: the *shifted* `k = 1/4` model data on `(0, 2π)` forces a zero of `jacobiSol 3`. -/
theorem gs1b_engine_route :
    ∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 4)), jacobiSol 3 c = 0 := by
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num
  have hb : 0 < Real.pi / Real.sqrt (1 / 4) := div_pos Real.pi_pos (Real.sqrt_pos_of_pos h4)
  have hstrict : ∃ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 4)), (1 / 4 : ℝ) < 3 :=
    ⟨Real.pi / Real.sqrt (1 / 4) / 2, ⟨by linarith, by linarith⟩, by norm_num⟩
  have hu2a : jacobiSolShift (1 / 4) 0 0 = 0 := by simp [jacobiSolShift, jacobiSol_zero]
  have hu2b : jacobiSolShift (1 / 4) 0 (Real.pi / Real.sqrt (1 / 4)) = 0 := by
    simp only [jacobiSolShift, Function.comp_apply, sub_zero]
    exact modelJacobiSol_firstZero h4
  refine exists_zero_of_curvature_lt (k₁ := fun _ : ℝ => 3) (k₂ := fun _ : ℝ => 1 / 4)
    (u₁ := jacobiSol 3) (du₁ := jacobiDeriv 3) (ddu₁ := fun t => -(3 * jacobiSol 3 t))
    (u₂ := jacobiSolShift (1 / 4) 0) (du₂ := jacobiDerivShift (1 / 4) 0)
    (ddu₂ := fun t => -((1 / 4) * jacobiSolShift (1 / 4) 0 t))
    (a := 0) (b := Real.pi / Real.sqrt (1 / 4))
    hb (fun _ _ => by norm_num) (modelJacobiSolutionOn 3 _)
    (jacobiSolShift_jacobiSolutionOn (1 / 4) 0 _) (jacobiSol_zero 3) hu2a hu2b
    (fun t ht => jacobiSolShift_pos h4 t (by simpa using ht))
    (hasDerivAt_jacobiSolShift (1 / 4) 0 _) hstrict

/-- (GS2) First-positive-zero bound on fresh data: with `K = 2` and `k = 5 ≥ K`,
`firstPositiveZero (jacobiSol 5) ≤ π/√2`. -/
theorem gs2_first_zero_bound :
    firstPositiveZero (jacobiSol 5) ≤ Real.pi / Real.sqrt 2 :=
  firstPositiveZero_le_pi_sqrt (K := 2) (k := fun _ : ℝ => 5)
    (u := jacobiSol 5) (du := jacobiDeriv 5) (ddu := fun t => -(5 * jacobiSol 5 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 5 _) (jacobiSol_zero 5)

/-- (GS2b) Closed form of (GS2): `firstPositiveZero (jacobiSol 5) = π/√5`, so the bound reads
`π/√5 ≤ π/√2`. -/
theorem gs2b_closed_form :
    Real.pi / Real.sqrt 5 ≤ Real.pi / Real.sqrt 2 := by
  have h := gs2_first_zero_bound
  rwa [firstPositiveZero_modelJacobiSol (show (0 : ℝ) < 5 by norm_num)] at h

/-- (GS2c) Horizon form on fresh data: horizon `H = 2 ≥ π/√4 = π/2`, curvature `k = 5 ≥ K = 4`,
so `firstPositiveZero (jacobiSol 5) ≤ π/2`. -/
theorem gs2c_horizon_instance :
    firstPositiveZero (jacobiSol 5) ≤ Real.pi / Real.sqrt 4 := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hH : Real.pi / Real.sqrt 4 ≤ 2 := by
    rw [hsqrt4]
    linarith [Real.pi_lt_four]
  exact firstPositiveZero_le_pi_sqrt_of_horizon (K := 4) (H := 2)
    (k := fun _ : ℝ => 5) (u := jacobiSol 5) (du := jacobiDeriv 5)
    (ddu := fun t => -(5 * jacobiSol 5 t)) (by norm_num) (fun _ _ => by norm_num)
    (modelJacobiSolutionOn 5 2) (jacobiSol_zero 5) hH

/-- (GS2d) Attainment on fresh data: for `jacobiSol 5` with `u 0 = 0`, `u' 0 = 1`, the point
`firstPositiveZero (jacobiSol 5)` is a genuine positive zero, not an unattained infimum. -/
theorem gs2d_attainment :
    jacobiSol 5 (firstPositiveZero (jacobiSol 5)) = 0 ∧
      0 < firstPositiveZero (jacobiSol 5) := by
  have h := firstPositiveZero_mem_of_normalized (K := 4) (k := fun _ : ℝ => 5)
    (u := jacobiSol 5) (du := jacobiDeriv 5) (ddu := fun t => -(5 * jacobiSol 5 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 5 _)
    (jacobiSol_zero 5) (jacobiDeriv_zero 5)
  exact ⟨h.1, h.2.1⟩

/-- (GS3) Equality case on fresh data: `k ≡ 3 = K` and `u 0 = 0` force the endpoint zero
`u (π/√3) = 0` through the Wronskian-constancy argument. -/
theorem gs3_equality_case :
    jacobiSol 3 (Real.pi / Real.sqrt 3) = 0 :=
  eq_zero_at_pi_sqrt_of_curvature_eq (K := 3) (k := fun _ : ℝ => 3)
    (u := jacobiSol 3) (du := jacobiDeriv 3) (ddu := fun t => -(3 * jacobiSol 3 t))
    (by norm_num) (modelJacobiSolutionOn 3 _) (jacobiSol_zero 3) (fun _ _ => rfl)

/-- (GS4) Wronskian with explicit data at the fresh point `π/3`: `t·cos t ≤ sin t`. -/
theorem gs4_mul_cos_le_sin :
    (Real.pi / 3) * Real.cos (Real.pi / 3) ≤ Real.sin (Real.pi / 3) :=
  mul_cos_le_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- (GS4b) The concrete Wronskian derivative at `π/3` is `−π√3/6 < 0`. -/
theorem gs4b_wronskian_deriv_value :
    deriv (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) (Real.pi / 3)
      = -(Real.pi * Real.sqrt 3 / 6) := by
  rw [wronskian_deriv_sin_linear ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
    Real.sin_pi_div_three]
  ring

/-- (GS5) The literal acceptance branch is false: `sin` has no zero in `(0,π)` (prior art,
reused by name). -/
theorem gs5_literal_branch_false : ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0 :=
  sin_no_zero_in_Ioo_zero_pi

/-- (GS5b) Consequently the first positive zero of `sin` is exactly `π`, not `< π`. -/
theorem gs5b_sin_first_zero : firstPositiveZero Real.sin = Real.pi := firstPositiveZero_sin

/-- (GS6 auxiliary) Positivity of `jacobiSol 3` on `(0, 3/2]`: `√3 · (3/2) < π`. -/
theorem gs6_pos : ∀ t ∈ Ioc (0 : ℝ) (3 / 2), 0 < jacobiSol 3 t := by
  intro t ht
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs3_lt : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have h1 : Real.sqrt 3 * t ≤ Real.sqrt 3 * (3 / 2) :=
    mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg 3)
  have h2 : Real.sqrt 3 * (3 / 2) < Real.pi := by nlinarith [hs3_lt, Real.pi_gt_three]
  rw [jacobiSol_of_pos h3]
  exact jacobiSolSphere_pos h3 ht.1 (lt_of_le_of_lt h1 h2)

/-- (GS6) Engine route on fresh leader-style data: `k = 3`, `K = 1`, `T = 3/2` gives
`3/2 ≤ π`. -/
theorem gs6_engine_route : (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 :=
  no_positive_solution_past_pi_sqrt (K := 1) (k := fun _ : ℝ => 3)
    (u := jacobiSol 3) (du := jacobiDeriv 3) (ddu := fun t => -(3 * jacobiSol 3 t))
    (by norm_num) (modelJacobiSolutionOn 3 (3 / 2)) (jacobiSol_zero 3) gs6_pos
    (by norm_num) (fun _ _ => by norm_num)

/-- (GS6b) The same proposition through `conjugate_point_bound_via_engine`, with the full
quantitative hypothesis list of the leader theorem supplied (`B = 3`, `t₀ = 1/6`). -/
theorem gs6b_engine_route_full : (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  refine conjugate_point_bound_via_engine (K := 1) (k := fun _ : ℝ => 3)
    (u := jacobiSol 3) (du := jacobiDeriv 3) (ddu := fun t => -(3 * jacobiSol 3 t))
    (T := 3 / 2) (B := 3) (t₀ := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (modelJacobiSolutionOn 3 (3 / 2)) ?_ ?_ (jacobiSol_zero 3) (jacobiDeriv_zero 3) gs6_pos
    (by norm_num) (fun _ _ => by norm_num) ?_
  · exact ((continuous_const.mul (continuous_jacobiSol 3)).neg).continuousOn
  · intro t _
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos h3
    rw [abs_neg, abs_mul, abs_of_pos h3]
    have hs : |jacobiSol 3 t| ≤ 1 := by
      rw [jacobiSol_of_pos h3, jacobiSolSphere, abs_div, abs_of_pos hsqrt3pos]
      have h1 : |Real.sin (Real.sqrt 3 * t)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      rw [div_le_iff₀ hsqrt3pos]
      nlinarith [h1, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    nlinarith
  · norm_num [Real.sqrt_one]

/-- (GS6c) The already-proved leader theorem `conjugate_point_bound` invoked on the identical
data: both routes establish the same inequality. -/
theorem gs6c_leader_route : (3 / 2 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  refine conjugate_point_bound_cross_check (K := 1) (k := fun _ : ℝ => 3)
    (u := jacobiSol 3) (du := jacobiDeriv 3) (ddu := fun t => -(3 * jacobiSol 3 t))
    (T := 3 / 2) (B := 3) (t₀ := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (modelJacobiSolutionOn 3 (3 / 2)) ?_ ?_ (jacobiSol_zero 3) (jacobiDeriv_zero 3) gs6_pos
    (by norm_num) (fun _ _ => by norm_num) ?_
  · exact ((continuous_const.mul (continuous_jacobiSol 3)).neg).continuousOn
  · intro t _
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos h3
    rw [abs_neg, abs_mul, abs_of_pos h3]
    have hs : |jacobiSol 3 t| ≤ 1 := by
      rw [jacobiSol_of_pos h3, jacobiSolSphere, abs_div, abs_of_pos hsqrt3pos]
      have h1 : |Real.sin (Real.sqrt 3 * t)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      rw [div_le_iff₀ hsqrt3pos]
      nlinarith [h1, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    nlinarith
  · norm_num [Real.sqrt_one]

end Poincare.L4.GeodesicComparison

/-! ## Axiom cones of the probe declarations -/

#print axioms Poincare.L4.GeodesicComparison.gs1_interlacing_instance
#print axioms Poincare.L4.GeodesicComparison.gs1b_engine_route
#print axioms Poincare.L4.GeodesicComparison.gs2_first_zero_bound
#print axioms Poincare.L4.GeodesicComparison.gs2b_closed_form
#print axioms Poincare.L4.GeodesicComparison.gs2c_horizon_instance
#print axioms Poincare.L4.GeodesicComparison.gs2d_attainment
#print axioms Poincare.L4.GeodesicComparison.gs3_equality_case
#print axioms Poincare.L4.GeodesicComparison.gs4_mul_cos_le_sin
#print axioms Poincare.L4.GeodesicComparison.gs4b_wronskian_deriv_value
#print axioms Poincare.L4.GeodesicComparison.gs5_literal_branch_false
#print axioms Poincare.L4.GeodesicComparison.gs5b_sin_first_zero
#print axioms Poincare.L4.GeodesicComparison.gs6_pos
#print axioms Poincare.L4.GeodesicComparison.gs6_engine_route
#print axioms Poincare.L4.GeodesicComparison.gs6b_engine_route_full
#print axioms Poincare.L4.GeodesicComparison.gs6c_leader_route
