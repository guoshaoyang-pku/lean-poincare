import Poincare.L4.GeodesicComparison.ConstantCurvatureRauchLower
import Poincare.L4.GeodesicComparison.ConjugatePointBound

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-- Helper: `sinh x < exp x`. -/
theorem probe_sinh_lt_exp (x : ℝ) : Real.sinh x < Real.exp x := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_pos (-x)
  have h2 := Real.exp_pos x
  linarith

/-- Helper: `exp 3 < 27`. -/
theorem probe_exp_three_lt : Real.exp 3 < 27 := by
  have h : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : Real.exp 1 ^ 3 < 3 ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
  norm_num at h1 ⊢
  exact h1

/-- Helper: `exp 5 < 243`. -/
theorem probe_exp_five_lt : Real.exp 5 < 243 := by
  have h : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h1 : Real.exp 1 ^ 5 < 3 ^ 5 :=
    pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
  norm_num at h1 ⊢
  exact h1

/-- **Sharpened non-vacuity for `rauch_lower_of_jacobi_constCurv`**: the comparison
`coth t ≤ √2·coth(√2 t)` on the twelve-times-larger interval `(0,3)`, with the *model*
bound `B = 2·j_{-2}(3)` read off from `jacobiSol_second_deriv_bound_nonpos` rather than a
hand-picked constant. -/
theorem probe_rauch_lower_T3 :
    ∀ t ∈ Ioo (0 : ℝ) 3,
      jacobiDeriv (-1) t / jacobiSol (-1) t ≤ jacobiDeriv (-2) t / jacobiSol (-2) t := by
  have hsqrt2_lt : Real.sqrt 2 < 5 / 3 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 5 / 3)]
    norm_num
  have harg_lt : Real.sqrt 2 * 3 < 5 := by nlinarith [Real.sqrt_nonneg 2]
  have hsinh_lt : Real.sinh (Real.sqrt 2 * 3) < 243 := by
    have h1 : Real.sinh (Real.sqrt 2 * 3) < Real.exp (Real.sqrt 2 * 3) :=
      probe_sinh_lt_exp _
    have h2 : Real.exp (Real.sqrt 2 * 3) ≤ Real.exp 5 := Real.exp_le_exp.mpr harg_lt.le
    linarith [probe_exp_five_lt]
  have hj2_3 : jacobiSol (-2) 3 = Real.sinh (Real.sqrt 2 * 3) / Real.sqrt 2 := by
    rw [jacobiSol_of_neg (by norm_num : (-2 : ℝ) < 0), jacobiSolHyperbolic]
    simp
  have hj2_3_le : jacobiSol (-2) 3 ≤ 250 := by
    rw [hj2_3]
    have hle : Real.sinh (Real.sqrt 2 * 3) / Real.sqrt 2 ≤ Real.sinh (Real.sqrt 2 * 3) :=
      div_le_self (Real.sinh_nonneg_iff.mpr (mul_nonneg (Real.sqrt_nonneg 2) (by norm_num)))
        (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2))
    linarith
  have hj2_3_pos : 0 < jacobiSol (-2) 3 :=
    jacobiSol_pos_of_nonpos (by norm_num) (by norm_num)
  have hj1_3 : jacobiSol (-1) 3 = Real.sinh 3 := by
    rw [jacobiSol_of_neg (by norm_num : (-1 : ℝ) < 0), jacobiSolHyperbolic]
    simp [Real.sqrt_one]
  have hj1_3_pos : 0 < jacobiSol (-1) 3 :=
    jacobiSol_pos_of_nonpos (by norm_num) (by norm_num)
  have hBmodel : (|(-1 : ℝ)| * jacobiSol (-1) 3) * (1 / 1000) ≤ 1 / 2 := by
    rw [abs_neg, abs_one, one_mul, hj1_3]
    have h : Real.sinh 3 < 27 := lt_trans (probe_sinh_lt_exp 3) probe_exp_three_lt
    linarith
  have hBt₀ : (2 * jacobiSol (-2) 3) * (1 / 1000) ≤ 1 / 2 := by linarith
  have hBnn : 0 ≤ 2 * jacobiSol (-2) 3 := by linarith [hj2_3_pos]
  have hKmnn : 0 ≤ |(-1 : ℝ)| * jacobiSol (-1) 3 := by
    rw [abs_neg, abs_one, one_mul]; linarith [hj1_3_pos]
  have hmain := rauch_lower_of_jacobi_constCurv (T := 3) (B := 2 * jacobiSol (-2) 3)
    (t₀ := 1 / 1000) (K := -1)
    (k := fun _ : ℝ => -2) (u := jacobiSol (-2)) (du := jacobiDeriv (-2))
    (ddu := fun t => -((-2 : ℝ) * jacobiSol (-2) t))
    (by norm_num) hBnn (by norm_num) (by norm_num) hBt₀
    (jacobiSol_jacobiSolutionOn (-2) 3)
    (((continuous_const.mul (continuous_jacobiSol (-2))).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound_nonpos (K := -2) (T := 3) (by norm_num) t ht
      simpa using hb)
    (jacobiSol_zero (-2)) (jacobiDeriv_zero (-2))
    (fun t ht => jacobiSol_pos_of_nonpos (by norm_num) ht.1)
    (by norm_num) (fun t ht => by norm_num) hBmodel
  intro t ht
  exact hmain t ht

/-- **Sharpened non-vacuity for `conjugate_point_bound`**: instantiate with the model
`k = K = 1` and `T = 3.14`, i.e. within `0.0016` of `π`, giving `3.14 ≤ π`.  This shows the
bound is not an artefact of an artificially tiny `T`. -/
theorem probe_conjugate_sharp : (3.14 : ℝ) ≤ Real.pi / Real.sqrt 1 := by
  have hmain := conjugate_point_bound (T := 3.14) (B := 3.14) (t₀ := 1 / 7) (K := 1)
    (k := fun _ : ℝ => 1) (u := jacobiSol 1) (du := jacobiDeriv 1)
    (ddu := fun t => -(1 * jacobiSol 1 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (jacobiSol_jacobiSolutionOn 1 3.14)
    (((continuous_const.mul (continuous_jacobiSol 1)).neg).continuousOn)
    (fun t ht => by
      have hb := jacobiSol_second_deriv_bound (K := 1) (T := 3.14) (by norm_num) t ht
      have hmax : max (1 / Real.sqrt 1) 3.14 = 3.14 := by
        rw [Real.sqrt_one, div_one, max_eq_right]; norm_num
      rw [hmax, one_mul] at hb
      simpa using hb)
    (jacobiSol_zero 1) (jacobiDeriv_zero 1)
    (fun t ht => jacobiSol_pos_of_nonneg (K := 1) (by norm_num) ht.1
      (Or.inr (by
        rw [Real.sqrt_one, one_mul]
        linarith [Real.pi_gt_d2, ht.2])))
    (by norm_num) (fun t ht => by norm_num) (by norm_num)
  exact hmain

/-- Record the trivial consistency `3.14 < π` used above. -/
theorem probe_conjugate_sharp_concl : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.probe_rauch_lower_T3
#print axioms Poincare.L4.GeodesicComparison.probe_conjugate_sharp
