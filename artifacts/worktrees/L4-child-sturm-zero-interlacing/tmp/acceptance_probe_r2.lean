/-
Independent acceptance probe, acceptance pass 2 (r2) for
`L4-child-sturm-zero-interlacing`.

This file is **not** part of the release deliverable.  It is a second, independent probe run
after the one in `tmp/independent_acceptance_probe.lean`; every theorem below exercises a
delivered theorem on data the deliverable never uses, and every proof is written here.

Probes:
* `probe2_sin_no_zero_in_Ioo_zero_pi` — the literal acceptance branch "the first positive
  zero of `sin` is `< π`" is refuted, re-derived here **from Mathlib alone** (via
  `Real.sin_pos_of_pos_of_lt_pi`), independently of the deliverable's import of the prior-art
  `SturmZeroCount.sin_no_zero_in_Ioo_zero_pi`.
* `probe2_zero_counting_needs_curvature_bound` — the hypothesis `K ≤ k` of the zero-counting
  corollary is necessary: with `k = 0`, `u = t` has no zero in the horizon `(0, π]`.
* `probe2_interlacing_shifted` — the general two-curvature interlacing on a shifted,
  non-zero interval with curvatures never used by the deliverable: `(k₁,u₁) =
  (1/4, jacobiSolShift (1/4) (2π))` against `(k₂,u₂) = (1/9, jacobiSolShift (1/9) (2π))`,
  whose zeros `2π`, `5π` bracket the `u₁`-zero at `4π`.
* `probe2_interlacing_shifted_witness` — the explicit zero `4π` of the shifted `k₁ = 1/4`
  model inside `(2π, 5π)`.
* `probe2_zero_count_K9` — zero-counting corollary at `(K, k) = (9, 16)`.
* `probe2_firstZero_bound_K9_interior` — first-zero bound from an **interior** curvature
  bound at `(K, k) = (9, 16)`.
* `probe2_firstZero_ordering` — first-positive-zero ordering with `(k₁,k₂) = (9, 1/16)`:
  `firstPositiveZero (jacobiSol 9) < firstPositiveZero (jacobiSol (1/16))`.
* `probe2_horizon_K16` — horizon form of the zero-counting corollary at `(K, H, k) =
  (16, 5, 25)`.
* `probe2_equality_case_K25_negated` — the equality case `k ≡ K = 25` applied to the
  *negated* model (a solution the deliverable does not use).
* `probe2_wronskian_deriv_at_pi_div_six` — `wronskian_deriv` with `(k₁,u₁) = (1,sin)` /
  `(k₂,u₂) = (0,t)` at a point the deliverable does not use.
* `probe2_mul_cos_le_sin_at_five_pi_div_six` — the antitone-Wronskian inequality off the
  endpoints.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck

noncomputable section

open Set

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- P1. The literal branch is false, re-derived from Mathlib alone. -/
theorem probe2_sin_no_zero_in_Ioo_zero_pi :
    ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0 := by
  rintro ⟨c, hc, hzero⟩
  have hpos : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 hc.2
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- P2. Without the curvature hypothesis `K ≤ k` the zero-counting conclusion fails. -/
theorem probe2_zero_counting_needs_curvature_bound :
    ¬ ∃ c ∈ Ioc (0 : ℝ) Real.pi, (fun t : ℝ => t) c = 0 := by
  rintro ⟨c, hc, hzero⟩
  exact (ne_of_gt hc.1) hzero

/-- P3. Interlacing on `(2π, 5π)` with `(k₁, k₂) = (1/4, 1/9)` and shifted models. -/
theorem probe2_interlacing_shifted :
    ∃ c ∈ Ioo (2 * Real.pi) (5 * Real.pi),
      jacobiSolShift (1 / 4) (2 * Real.pi) c = 0 := by
  have hK₂ : (0 : ℝ) < 1 / 9 := by norm_num
  have hsqrt₂ : Real.sqrt (1 / 9) = 1 / 3 := by
    rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hb : 2 * Real.pi + Real.pi / Real.sqrt (1 / 9) = 5 * Real.pi := by
    rw [hsqrt₂]; field_simp; ring
  have hstrict :
      ∃ t ∈ Ioo (2 * Real.pi) (2 * Real.pi + Real.pi / Real.sqrt (1 / 9)),
        (1 / 9 : ℝ) < 1 / 4 :=
    ⟨(2 * Real.pi + (2 * Real.pi + Real.pi / Real.sqrt (1 / 9))) / 2,
      ⟨by linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂],
       by linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂]⟩, by norm_num⟩
  have hmain := exists_zero_of_curvature_lt
    (a := 2 * Real.pi) (b := 2 * Real.pi + Real.pi / Real.sqrt (1 / 9))
    (k₁ := fun _ : ℝ => 1 / 4) (k₂ := fun _ : ℝ => 1 / 9)
    (u₁ := jacobiSolShift (1 / 4) (2 * Real.pi))
    (du₁ := jacobiDerivShift (1 / 4) (2 * Real.pi))
    (ddu₁ := fun t => -((1 / 4) * jacobiSolShift (1 / 4) (2 * Real.pi) t))
    (u₂ := jacobiSolShift (1 / 9) (2 * Real.pi))
    (du₂ := jacobiDerivShift (1 / 9) (2 * Real.pi))
    (ddu₂ := fun t => -((1 / 9) * jacobiSolShift (1 / 9) (2 * Real.pi) t))
    (by linarith [Real.pi_pos, Real.sqrt_pos_of_pos hK₂])
    (fun _ _ => by norm_num)
    (jacobiSolShift_jacobiSolutionOn (1 / 4) (2 * Real.pi) _)
    (jacobiSolShift_jacobiSolutionOn (1 / 9) (2 * Real.pi) _)
    (by simp [jacobiSolShift, jacobiSol_zero])
    (by simp [jacobiSolShift, jacobiSol_zero])
    (by
      have hfirst := modelJacobiSol_firstZero hK₂
      simpa only [jacobiSolShift, Function.comp_apply, add_sub_cancel_left] using hfirst)
    (fun t ht => jacobiSolShift_pos hK₂ t ht)
    (hasDerivAt_jacobiSolShift (1 / 9) (2 * Real.pi) _)
    hstrict
  rwa [hb] at hmain

/-- P4. The explicit shifted witness: `4π` is a zero of the `k = 1/4` shifted model inside
`(2π, 5π)`. -/
theorem probe2_interlacing_shifted_witness :
    jacobiSolShift (1 / 4) (2 * Real.pi) (4 * Real.pi) = 0 ∧
      4 * Real.pi ∈ Ioo (2 * Real.pi) (5 * Real.pi) := by
  have hsqrt : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · rw [jacobiSolShift, Function.comp_apply]
    have harg : (4 : ℝ) * Real.pi - 2 * Real.pi = Real.pi / Real.sqrt (1 / 4) := by
      rw [hsqrt]; ring
    rw [harg]
    exact modelJacobiSol_firstZero (by norm_num)
  · constructor <;> nlinarith [Real.pi_pos]

/-- P5. Zero-counting at `(K, k) = (9, 16)` (closed-interval curvature form). -/
theorem probe2_zero_count_K9 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 9), jacobiSol 16 c = 0 :=
  exists_jacobi_zero_on_Ioc_pi_sqrt (K := 9) (k := fun _ : ℝ => 16)
    (u := jacobiSol 16) (du := jacobiDeriv 16) (ddu := fun t => -(16 * jacobiSol 16 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 16 _) (jacobiSol_zero 16)

/-- P6. First-zero bound from an interior curvature bound at `(K, k) = (9, 16)`. -/
theorem probe2_firstZero_bound_K9_interior :
    firstPositiveZero (jacobiSol 16) ≤ Real.pi / Real.sqrt 9 :=
  firstPositiveZero_le_pi_sqrt_of_interior_bound (K := 9) (k := fun _ : ℝ => 16)
    (u := jacobiSol 16) (du := jacobiDeriv 16) (ddu := fun t => -(16 * jacobiSol 16 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 16 _) (jacobiSol_zero 16)

/-- P7. First-positive-zero ordering with `(k₁, k₂) = (9, 1/16)`. -/
theorem probe2_firstZero_ordering :
    firstPositiveZero (jacobiSol 9) < firstPositiveZero (jacobiSol (1 / 16)) := by
  have hK₂ : (0 : ℝ) < 1 / 16 := by norm_num
  have hb : 0 < Real.pi / Real.sqrt (1 / 16) :=
    div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK₂)
  have hstrict : ∃ t ∈ Ioo (0 : ℝ) (Real.pi / Real.sqrt (1 / 16)), (1 / 16 : ℝ) < 9 :=
    ⟨Real.pi / Real.sqrt (1 / 16) / 2, ⟨by linarith, by linarith⟩, by norm_num⟩
  have hlt := firstPositiveZero_lt_of_curvature_lt (b := Real.pi / Real.sqrt (1 / 16))
    hb (fun _ _ => by norm_num)
    (modelJacobiSolutionOn 9 _) (modelJacobiSolutionOn (1 / 16) _)
    (jacobiSol_zero 9) (jacobiSol_zero (1 / 16)) (modelJacobiSol_firstZero hK₂)
    (modelJacobiSol_pos hK₂) (hasDerivAt_jacobiSol (1 / 16) _) hstrict
  rw [firstPositiveZero_modelJacobiSol hK₂]
  exact hlt

/-- P8. Horizon form at `(K, H, k) = (16, 5, 25)`. -/
theorem probe2_horizon_K16 :
    ∃ c ∈ Ioc (0 : ℝ) (Real.pi / Real.sqrt 16), jacobiSol 25 c = 0 :=
  exists_jacobi_zero_of_horizon (K := 16) (H := 5) (k := fun _ : ℝ => 25)
    (u := jacobiSol 25) (du := jacobiDeriv 25) (ddu := fun t => -(25 * jacobiSol 25 t))
    (by norm_num) (fun _ _ => by norm_num) (modelJacobiSolutionOn 25 5) (jacobiSol_zero 25)
    (jacobiDeriv_zero 25)
    (by
      have h4 : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
      linarith [Real.pi_lt_four])

/-- P9. Equality case at `K = 25` applied to the negated model. -/
theorem probe2_equality_case_K25_negated :
    (fun t : ℝ => -(jacobiSol 25 t)) (Real.pi / Real.sqrt 25) = 0 :=
  eq_zero_at_pi_sqrt_of_curvature_eq (K := 25) (k := fun _ : ℝ => 25)
    (u := fun t : ℝ => -(jacobiSol 25 t)) (du := fun t : ℝ => -(jacobiDeriv 25 t))
    (ddu := fun t : ℝ => -(-(25 * jacobiSol 25 t)))
    (by norm_num) ((modelJacobiSolutionOn 25 _).neg) (by simp [jacobiSol_zero])
    (fun _ _ => rfl)

/-- P10. `wronskian_deriv` with explicit data at a new point `π/6`. -/
theorem probe2_wronskian_deriv_at_pi_div_six :
    deriv (wronskian Real.sin Real.cos (fun t : ℝ => t) (fun _ => 1)) (Real.pi / 6)
      = -(Real.pi / 6 * (1 / 2)) := by
  rw [wronskian_deriv_sin_linear
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, Real.sin_pi_div_six]

/-- P11. The antitone-Wronskian inequality at `t = 5π/6`. -/
theorem probe2_mul_cos_le_sin_at_five_pi_div_six :
    (5 * Real.pi / 6) * Real.cos (5 * Real.pi / 6) ≤ Real.sin (5 * Real.pi / 6) :=
  mul_cos_le_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

end Poincare.L4.GeodesicComparison

/- Kernel-cone audit of every probe theorem (parsed by the acceptance script). -/
#print axioms Poincare.L4.GeodesicComparison.probe2_sin_no_zero_in_Ioo_zero_pi
#print axioms Poincare.L4.GeodesicComparison.probe2_zero_counting_needs_curvature_bound
#print axioms Poincare.L4.GeodesicComparison.probe2_interlacing_shifted
#print axioms Poincare.L4.GeodesicComparison.probe2_interlacing_shifted_witness
#print axioms Poincare.L4.GeodesicComparison.probe2_zero_count_K9
#print axioms Poincare.L4.GeodesicComparison.probe2_firstZero_bound_K9_interior
#print axioms Poincare.L4.GeodesicComparison.probe2_firstZero_ordering
#print axioms Poincare.L4.GeodesicComparison.probe2_horizon_K16
#print axioms Poincare.L4.GeodesicComparison.probe2_equality_case_K25_negated
#print axioms Poincare.L4.GeodesicComparison.probe2_wronskian_deriv_at_pi_div_six
#print axioms Poincare.L4.GeodesicComparison.probe2_mul_cos_le_sin_at_five_pi_div_six
