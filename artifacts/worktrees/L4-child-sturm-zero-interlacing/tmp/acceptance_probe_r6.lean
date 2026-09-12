/-
Pass-6 independent acceptance probe (2026-09-12, continuation invocation) for the task
`L4-child-sturm-zero-interlacing`.

Written from scratch for this pass; it neither imports nor reuses the pass-1/2/3/4/5 probes.
It exercises the delivered theorems on data chosen here, and adds two checks the earlier
passes do not perform:

  * a **machine-checked non-restatement witness**: the raw D12 engine is invoked on the
    acceptance data, yielding its two-sided alternative `A ∨ B`; the probe then proves `¬B`,
    and the delivered strict-gap theorem supplies `A`.  So on this data the delivered
    statement is strictly more informative than the engine's own conclusion — not a
    restatement of it — and this is established by terms, not by prose;
  * a **statement-level (type) comparison** surface: `#check @...` lines for the delivered
    theorems, the engine theorems and the prior art are parsed by
    `tools/acceptance_pass6.py`, which requires that the delivered types differ from the
    engine/prior-art types, that the engine's disjunctive conclusion does not survive into
    the delivered strict-gap statement, and that the engine-derived positivity bound carries
    strictly fewer hypotheses (arrow count) than the leader's `conjugate_point_bound`.

Fresh constructed data used here (not used by earlier probes):
  * negative shift `a = -3` with `(k₁,k₂) = (9,4)`, interlacing on `(-3, -3+π/√4)`;
  * zero counting at `(K,k) = (4,9)`, with the first zero `π/3` strictly inside `(0,π/2]`;
  * horizon form at `H = 3` and attainment on `jacobiSol 9`;
  * interior-bound form at `(K,k) = (16,25)`;
  * equality case `k ≡ K = 7`;
  * Wronskian data `(k₁,u₁) = (9, jacobiSol 9)`, `(k₂,u₂) = (4, jacobiSol 4)` on `[0,π/6]`.

The `#check`, `#print axioms` and `#print` lines at the end are parsed by the pass-6 driver.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- (P6-1) Status of the literal acceptance data `(k₁,u₁) = (1,sin)`, `(k₂,u₂) = (0,t)`:
`sin` has no zero in `(0,π)` (prior art, reused by name), its first positive zero is exactly
`π`, and the linear model is zero-free at every positive point and on `(0,π]`. -/
theorem p6_literal_branch_status :
    (¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0) ∧
      firstPositiveZero Real.sin = Real.pi ∧
      (∀ b : ℝ, 0 < b → (fun t : ℝ => t) b ≠ 0) ∧
      (∀ t ∈ Ioc (0 : ℝ) Real.pi, (fun t : ℝ => t) t ≠ 0) :=
  ⟨sin_no_zero_in_Ioo_zero_pi, firstPositiveZero_sin,
    fun b hb => linear_model_no_second_zero (b := b) hb,
    fun _ ht => ne_of_gt ht.1⟩

/-- (P6-2) **Two-curvature interlacing on a negative shifted interval.**  On
`(-3, -3 + π/√4)` the lower-curvature shifted model `jacobiSolShift 4 (-3)` has the endpoint
zeros `-3` and `-3 + π/√4` and is positive in between, while the higher-curvature shifted
model `jacobiSolShift 9 (-3)` has the explicit zero `-3 + π/√9` strictly inside. -/
theorem p6_negative_shift_interlacing :
    (∃ c ∈ Ioo (-3 : ℝ) (-3 + Real.pi / Real.sqrt 4), jacobiSolShift 9 (-3) c = 0) ∧
      jacobiSolShift 9 (-3) (-3 + Real.pi / Real.sqrt 9) = 0 ∧
      (-3 + Real.pi / Real.sqrt 9) ∈ Ioo (-3 : ℝ) (-3 + Real.pi / Real.sqrt 4) := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hpi4 : 0 < Real.pi / Real.sqrt 4 :=
    div_pos Real.pi_pos (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 4))
  have hspan : (-3 : ℝ) < -3 + Real.pi / Real.sqrt 4 := by linarith
  have hpi8 : -3 + Real.pi / 8 < -3 + Real.pi / Real.sqrt 4 := by
    have : Real.pi / 8 < Real.pi / Real.sqrt 4 := by
      rw [hsqrt4]
      linarith [Real.pi_pos]
    linarith
  have hpi9pos : 0 < Real.pi / Real.sqrt 9 :=
    div_pos Real.pi_pos (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 9))
  have hu1a : jacobiSolShift 9 (-3) (-3) = 0 := by
    show jacobiSol 9 ((-3 : ℝ) - (-3)) = 0
    rw [sub_self]
    exact jacobiSol_zero 9
  have hu2a : jacobiSolShift 4 (-3) (-3) = 0 := by
    show jacobiSol 4 ((-3 : ℝ) - (-3)) = 0
    rw [sub_self]
    exact jacobiSol_zero 4
  have hu2b : jacobiSolShift 4 (-3) (-3 + Real.pi / Real.sqrt 4) = 0 := by
    show jacobiSol 4 ((-3 + Real.pi / Real.sqrt 4) - (-3)) = 0
    rw [show (-3 + Real.pi / Real.sqrt 4) - (-3) = Real.pi / Real.sqrt 4 by ring]
    exact modelJacobiSol_firstZero (by norm_num : (0 : ℝ) < 4)
  refine ⟨?_, ?_, ?_⟩
  · exact exists_zero_of_curvature_lt (k₁ := fun _ : ℝ => 9) (k₂ := fun _ : ℝ => 4)
      (u₁ := jacobiSolShift 9 (-3)) (du₁ := jacobiDerivShift 9 (-3))
      (ddu₁ := fun t => -(9 * jacobiSolShift 9 (-3) t))
      (u₂ := jacobiSolShift 4 (-3)) (du₂ := jacobiDerivShift 4 (-3))
      (ddu₂ := fun t => -(4 * jacobiSolShift 4 (-3) t))
      (a := -3) (b := -3 + Real.pi / Real.sqrt 4)
      hspan (fun _ _ => by norm_num)
      (jacobiSolShift_jacobiSolutionOn 9 (-3) _)
      (jacobiSolShift_jacobiSolutionOn 4 (-3) _)
      hu1a hu2a hu2b (jacobiSolShift_pos (K := 4) (a := -3) (by norm_num))
      (hasDerivAt_jacobiSolShift 4 (-3) _)
      ⟨-3 + Real.pi / 8, ⟨by linarith [Real.pi_pos], hpi8⟩, by norm_num⟩
  · show jacobiSol 9 ((-3 + Real.pi / Real.sqrt 9) - (-3)) = 0
    rw [show (-3 + Real.pi / Real.sqrt 9) - (-3) = Real.pi / Real.sqrt 9 by ring]
    exact modelJacobiSol_firstZero (by norm_num : (0 : ℝ) < 9)
  · constructor
    · linarith [hpi9pos]
    · have h49 : Real.sqrt 4 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hpos4 : 0 < Real.sqrt 4 := Real.sqrt_pos_of_pos (by norm_num)
      rw [add_lt_add_iff_left]
      exact div_lt_div_of_pos_left Real.pi_pos hpos4 h49

/-- (P6-3) **Zero counting at `(K,k) = (4,9)`.**  `jacobiSol 9` (`u 0 = 0`, `u' 0 = 1`) has a
zero in `(0, π/√4]`; its first positive zero obeys the bound `π/√4`, and in closed form it is
`π/√9 = π/3`, strictly inside the window. -/
theorem p6_zero_count_strict_inside :
    (∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 4), jacobiSol 9 c = 0) ∧
      firstPositiveZero (jacobiSol 9) ≤ Real.pi / Real.sqrt 4 ∧
      firstPositiveZero (jacobiSol 9) = Real.pi / Real.sqrt 9 :=
  ⟨exists_jacobi_zero_on_Ioc_pi_sqrt (K := 4) (k := fun _ : ℝ => 9)
      (u := jacobiSol 9) (du := jacobiDeriv 9) (ddu := fun t => -(9 * jacobiSol 9 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 9 _) (jacobiSol_zero 9),
    firstPositiveZero_le_pi_sqrt (K := 4) (k := fun _ : ℝ => 9)
      (u := jacobiSol 9) (du := jacobiDeriv 9) (ddu := fun t => -(9 * jacobiSol 9 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 9 _) (jacobiSol_zero 9),
    firstPositiveZero_modelJacobiSol (by norm_num : (0 : ℝ) < 9)⟩

/-- (P6-4) **Horizon form and attainment**: with data given only up to `H = 3 ≥ π/√4`, the
first positive zero of `jacobiSol 9` is at most `π/√4`, and it is a genuine zero (attained,
positive). -/
theorem p6_horizon_attainment :
    firstPositiveZero (jacobiSol 9) ≤ Real.pi / Real.sqrt 4 ∧
      jacobiSol 9 (firstPositiveZero (jacobiSol 9)) = 0 ∧
      0 < firstPositiveZero (jacobiSol 9) := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hH : Real.pi / Real.sqrt 4 ≤ 3 := by
    rw [hsqrt4]
    linarith [Real.pi_lt_four]
  have hle := firstPositiveZero_le_pi_sqrt_of_horizon (K := 4) (H := 3)
    (k := fun _ : ℝ => 9) (u := jacobiSol 9) (du := jacobiDeriv 9)
    (ddu := fun t => -(9 * jacobiSol 9 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 9 3) (jacobiSol_zero 9) hH
  have hmem := firstPositiveZero_mem_of_normalized (K := 4) (k := fun _ : ℝ => 9)
    (u := jacobiSol 9) (du := jacobiDeriv 9) (ddu := fun t => -(9 * jacobiSol 9 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 9 _) (jacobiSol_zero 9)
    (jacobiDeriv_zero 9)
  exact ⟨hle, hmem.1, hmem.2.1⟩

/-- (P6-5) **Interior-bound form at `(K,k) = (16,25)`**: the curvature hypothesis is needed
only on the open interval `(0, π/√16)`, and both the zero and the first-zero bound hold. -/
theorem p6_interior_bound_K16 :
    (∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 16), jacobiSol 25 c = 0) ∧
      firstPositiveZero (jacobiSol 25) ≤ Real.pi / Real.sqrt 16 :=
  ⟨exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound (K := 16) (k := fun _ : ℝ => 25)
      (u := jacobiSol 25) (du := jacobiDeriv 25) (ddu := fun t => -(25 * jacobiSol 25 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 25 _) (jacobiSol_zero 25),
    firstPositiveZero_le_pi_sqrt_of_interior_bound (K := 16) (k := fun _ : ℝ => 25)
      (u := jacobiSol 25) (du := jacobiDeriv 25) (ddu := fun t => -(25 * jacobiSol 25 t))
      (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 25 _) (jacobiSol_zero 25)⟩

/-- (P6-6) **Equality case `k ≡ K = 7`**: the endpoint `π/√7` is a zero, and it is counted by
the closed-interval zero-counting corollary. -/
theorem p6_equality_K7 :
    jacobiSol 7 (Real.pi / Real.sqrt 7) = 0 ∧
      (∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 7), jacobiSol 7 c = 0) :=
  ⟨modelJacobiSol_firstZero (by norm_num : (0 : ℝ) < 7),
    exists_jacobi_zero_on_Ioc_pi_sqrt (K := 7) (k := fun _ : ℝ => 7)
      (u := jacobiSol 7) (du := jacobiDeriv 7) (ddu := fun t => -(7 * jacobiSol 7 t))
      (by norm_num) (fun _ _ => le_rfl) (modelJacobiSolutionOn 7 _) (jacobiSol_zero 7)⟩

/-- (P6-7) **Wronskian consumption with fresh explicit data** `(k₁,u₁) = (9, jacobiSol 9)`,
`(k₂,u₂) = (4, jacobiSol 4)` on `[0, π/6]`: the Wronskian is antitone, hence
`W (π/6) ≤ W 0`, and `wronskian_deriv` gives the explicit value
`W' (π/12) = −5·u₁(π/12)·u₂(π/12)`. -/
theorem p6_wronskian_fresh_data :
    AntitoneOn (wronskian (jacobiSol 9) (jacobiDeriv 9) (jacobiSol 4) (jacobiDeriv 4))
        (Icc (0 : ℝ) (Real.pi / 6)) ∧
      wronskian (jacobiSol 9) (jacobiDeriv 9) (jacobiSol 4) (jacobiDeriv 4) (Real.pi / 6) ≤
        wronskian (jacobiSol 9) (jacobiDeriv 9) (jacobiSol 4) (jacobiDeriv 4) 0 ∧
      deriv (wronskian (jacobiSol 9) (jacobiDeriv 9) (jacobiSol 4) (jacobiDeriv 4))
          (Real.pi / 12)
        = -(5 * (jacobiSol 9 (Real.pi / 12) * jacobiSol 4 (Real.pi / 12))) := by
  have hsqrt9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hanti : AntitoneOn
      (wronskian (jacobiSol 9) (jacobiDeriv 9) (jacobiSol 4) (jacobiDeriv 4))
      (Icc (0 : ℝ) (Real.pi / 6)) := by
    refine wronskian_antitoneOn_of_le (by linarith [Real.pi_pos]) (fun _ _ => by norm_num) ?_
      (modelJacobiSolutionOn 9 _) (modelJacobiSolutionOn 4 _)
    intro t ht
    have ht9 : t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt 9) := by
      refine ⟨ht.1, ?_⟩
      have : Real.pi / 6 < Real.pi / Real.sqrt 9 := by
        rw [hsqrt9]
        linarith [Real.pi_pos]
      exact lt_of_lt_of_le ht.2 this.le
    have ht4 : t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt 4) := by
      refine ⟨ht.1, ?_⟩
      have : Real.pi / 6 < Real.pi / Real.sqrt 4 := by
        rw [hsqrt4]
        linarith [Real.pi_pos]
      exact lt_of_lt_of_le ht.2 this.le
    exact mul_nonneg (modelJacobiSol_pos (by norm_num : (0 : ℝ) < 9) t ht9).le
      (modelJacobiSol_pos (by norm_num : (0 : ℝ) < 4) t ht4).le
  refine ⟨hanti, ?_, ?_⟩
  · exact hanti (left_mem_Icc.mpr (by linarith [Real.pi_pos]))
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith [Real.pi_pos])
  · rw [wronskian_deriv (modelJacobiSolutionOn 9 _) (modelJacobiSolutionOn 4 _)
      (show Real.pi / 12 ∈ Ioo (0 : ℝ) (Real.pi / 6) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)]
    ring

/-- (P6-8) **Non-restatement witness (machine-checked).**  The raw D12 engine
`sturm_zero_comparison`, invoked directly (not through any deliverable wrapper) on the
acceptance data `(k₁,u₁) = (1,sin)`, `(k₂,u₂) = (1/2, jacobiSol (1/2))` on
`(0, π/√(1/2))`, yields its two-sided conclusion `A ∨ B` (`A` = interior zero of `sin`,
`B` = the curvatures agree on the interval).  The probe proves `¬B` by exhibiting the point
`π/4` in the interval where `1 ≠ 1/2`, and the delivered `sin_zero_interlaces_half_model`
supplies `A`.  Hence on this data the delivered theorem strictly improves the engine's own
conclusion rather than restating it. -/
theorem p6_engine_vs_delivered_strictness :
    ((∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), Real.sin c = 0) ∨
        (∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) → (1 : ℝ) = 1 / 2)) ∧
      (∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), Real.sin c = 0) ∧
      ¬ (∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) → (1 : ℝ) = 1 / 2) := by
  have hK₂ : (0 : ℝ) < 1 / 2 := by norm_num
  have hz : 0 < Real.pi / Real.sqrt (1 / 2) :=
    div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK₂)
  have hraw : (∃ c ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)), Real.sin c = 0) ∨
      (∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) → (1 : ℝ) = 1 / 2) :=
    sturm_zero_comparison hz (fun _ _ => by norm_num)
      (sinJacobiSolutionOn 0 _) (modelJacobiSolutionOn (1 / 2) _)
      Real.sin_zero (jacobiSol_zero (1 / 2)) (modelJacobiSol_firstZero hK₂)
      (modelJacobiSol_pos hK₂) (hasDerivAt_jacobiSol (1 / 2) _)
  have hnotB : ¬ (∀ ⦃t : ℝ⦄, t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) →
      (1 : ℝ) = 1 / 2) := by
    intro h
    have hmem : Real.pi / 4 ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 2)) :=
      ⟨by linarith [Real.pi_pos],
        by linarith [sin_zero_interlaces_half_model.2.2, Real.pi_pos]⟩
    have := h hmem
    norm_num at this
  exact ⟨hraw, sin_zero_interlaces_half_model.1, hnotB⟩

end Poincare.L4.GeodesicComparison

/-! ## Axiom cones of the probe declarations -/

#print axioms Poincare.L4.GeodesicComparison.p6_literal_branch_status
#print axioms Poincare.L4.GeodesicComparison.p6_negative_shift_interlacing
#print axioms Poincare.L4.GeodesicComparison.p6_zero_count_strict_inside
#print axioms Poincare.L4.GeodesicComparison.p6_horizon_attainment
#print axioms Poincare.L4.GeodesicComparison.p6_interior_bound_K16
#print axioms Poincare.L4.GeodesicComparison.p6_equality_K7
#print axioms Poincare.L4.GeodesicComparison.p6_wronskian_fresh_data
#print axioms Poincare.L4.GeodesicComparison.p6_engine_vs_delivered_strictness

/-! ## Statement-level comparison surface (parsed by `tools/acceptance_pass6.py`)

Each `#check @name` line prints the fully elaborated type.  The pass-6 driver requires:
delivered type ≠ engine type; the engine's disjunctive conclusion does not appear in the
delivered strict-gap statement; the zero-counting type differs from the prior-art type; the
engine-derived positivity bound carries strictly fewer top-level hypotheses (arrows) than the
leader's `conjugate_point_bound`. -/

#check @Poincare.L4.GeodesicComparison.exists_zero_of_curvature_lt
#check @Poincare.D12.ComparisonGeodesics.sturm_zero_comparison
#check @Poincare.L4.GeodesicComparison.firstPositiveZero_le_pi_sqrt
#check @Poincare.L4.GeodesicComparison.exists_jacobi_zero_on_Ioc_pi_sqrt
#check @Poincare.L4.GeodesicComparison.exists_jacobi_zero_before_pi_sqrt
#check @Poincare.L4.GeodesicComparison.no_positive_solution_past_pi_sqrt
#check @Poincare.L4.GeodesicComparison.conjugate_point_bound
#check @Poincare.L4.GeodesicComparison.wronskian_sin_linear_antitoneOn
#check @Poincare.D12.ComparisonGeodesics.wronskian_antitoneOn_of_le
