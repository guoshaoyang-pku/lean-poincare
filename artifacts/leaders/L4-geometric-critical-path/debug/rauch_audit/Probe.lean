import Poincare.L4.GeodesicComparison.RauchBridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Set Filter
open scoped Topology
open Poincare.D12.ComparisonGeodesics

namespace Poincare.L4.GeodesicComparison

-- (1) exact statements
#check @abs_sub_le_of_deriv_bound
#check @jacobi_linear_bounds
#check @jacobi_pos_and_ratio_bound
#check @euclideanNormalizedOn_of_jacobi
#check @riccati_identity_of_jacobi
#check @rauch_upper_of_jacobi
#check @jacobi_areaRatio_antitone
#check @sin_jacobiSolution
#check @sin_rauch_witness
#check @sin_areaRatio_witness

-- (2) non-vacuity of the general lemma
example : |(1:ℝ) - 0| ≤ 1 * (1 - 0) :=
  abs_sub_le_of_deriv_bound (f := fun x : ℝ => x) (f' := fun _ => 1)
    (a := 0) (b := 1) (C := 1) (by norm_num) continuousOn_id continuousOn_const
    (fun t _ => hasDerivAtR_id t) (fun t _ => by norm_num)

-- local Jacobi data on a longer interval (T = 3/2), to test the propagation regime
theorem sin_jacobiSolution_long : JacobiSolutionOn (fun _ : ℝ => 1) Real.sin Real.cos
    (fun t => -Real.sin t) 0 (3/2) where
  hasDerivAt_u := by intro t ht; simpa using Real.hasDerivAt_sin t
  hasDerivAt_du := by intro t ht; simpa using Real.hasDerivAt_cos t
  eq_secondDeriv := by intro t ht; simp
  continuousOn_u := Real.continuous_sin.continuousOn
  continuousOn_du := Real.continuous_cos.continuousOn

-- (3) STRONGER non-vacuity: T = 3/2 > t₀ = 1/2 exercises engine step 2 (t > t₀)
theorem sin_rauch_witness_long : ∀ t ∈ Ioo (0:ℝ) (3/2), Real.cos t / Real.sin t ≤ 1 / t := by
  have hmain := rauch_upper_of_jacobi (T := 3/2) (B := 1) (t₀ := 1/2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sin_jacobiSolution_long (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro t ht
  simpa using hmain t ht

theorem sin_areaRatio_witness_long :
    ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 (3/2) → ∀ ⦃t : ℝ⦄, t ∈ Ioc 0 (3/2) → s ≤ t →
      Real.sin t / t ≤ Real.sin s / s := by
  have hmain := jacobi_areaRatio_antitone (T := 3/2) (B := 1) (t₀ := 1/2)
    (k := fun _ : ℝ => 1) (u := Real.sin) (du := Real.cos) (ddu := fun t => -Real.sin t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sin_jacobiSolution_long (by fun_prop)
    (fun t ht => by simpa using Real.abs_sin_le_one (x := t))
    (by simp) (by simp)
    (fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three]))
    (fun t ht => by norm_num)
  intro s hs t ht hst
  exact hmain hs ht hst

-- (4) numeric spot checks of direction (t=0.3 ≤ t₀=0.5; t=1.0 > t₀ propagates)
example : Real.cos (3/10) / Real.sin (3/10) ≤ 1 / (3/10 : ℝ) :=
  sin_rauch_witness (3/10) (by norm_num)
example : Real.cos 1 / Real.sin 1 ≤ 1 / (1 : ℝ) :=
  sin_rauch_witness_long 1 (by norm_num)
example : Real.sin (1/2) / (1/2) ≤ Real.sin (1/4) / (1/4 : ℝ) :=
  sin_areaRatio_witness (by norm_num) (by norm_num) (by norm_num)

end Poincare.L4.GeodesicComparison
