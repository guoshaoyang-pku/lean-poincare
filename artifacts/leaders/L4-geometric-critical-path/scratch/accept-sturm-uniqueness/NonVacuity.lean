/-
Reviewer non-vacuity probe for SturmUniqueness.lean (read-only w.r.t. artifact).
Concrete instantiations of the theorem hypotheses with data; where possible a
nontrivial conclusion is extracted (e.g. recover the proportionality constant).
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Poincare.L4.GeodesicComparison.TwoSidedSturm
import Poincare.L4.GeodesicComparison.SturmUniqueness

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

namespace AcceptSturmUniqueness

/-- (1) `sturmModel_pos_at_right`, K=1, a=0, c=1/2. -/
example : 0 < sturmModel 1 0 (1/2 : ℝ) :=
  sturmModel_pos_at_right (K := 1) (a := 0) (c := 1/2) (by norm_num) (by norm_num)
    (by rw [Real.sqrt_one, one_mul]; linarith [Real.pi_gt_three])

/-- (2) `sturmModel_eq_zero_at_pi_sqrt`, K=2, a=1: zero at 1 + π/√2. -/
example : sturmModel 2 1 (1 + Real.pi / Real.sqrt 2) = 0 :=
  sturmModel_eq_zero_at_pi_sqrt (K := 2) (a := 1) (by norm_num)

/-- Data used repeatedly: the model with K=1, a=0, on [0,2π]. -/
theorem hmodel : JacobiSolutionOn (fun _ : ℝ => (1 : ℝ)) (sturmModel 1 0)
    (sturmModelDeriv 1 0) (sturmModelSecondDeriv 1 0) 0 (2 * Real.pi) :=
  sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := 2 * Real.pi) (by norm_num)

theorem hca : Real.pi ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
  ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩

theorem hua : sturmModel 1 0 0 = 0 := by simp [sturmModel]

/-- `3*m` is again a Jacobi solution with the same curvature. -/
theorem hmodel3 : JacobiSolutionOn (fun _ : ℝ => (1 : ℝ)) (fun t => 3 * sturmModel 1 0 t)
    (fun t => 3 * sturmModelDeriv 1 0 t) (fun t => 3 * sturmModelSecondDeriv 1 0 t)
    0 (2 * Real.pi) where
  hasDerivAt_u := fun t _ => (hasDerivAtR_sturmModel 1 0 t).const_mul 3
  hasDerivAt_du := fun t _ =>
    (hasDerivAtR_sturmModelDeriv (K := 1) (a := 0) (by norm_num) (t := t)).const_mul 3
  eq_secondDeriv := by
    intro t _
    simp only [sturmModelSecondDeriv, sturmModel]
    ring
  continuousOn_u := hmodel.continuousOn_u.const_mul 3
  continuousOn_du := hmodel.continuousOn_du.const_mul 3

theorem hua3 : 3 * sturmModel 1 0 0 = 0 := by rw [hua, mul_zero]

/-- (6) `exists_smul_sturmModel_of_curvature_eq` with `u = 3m`, `k ≡ K = 1`, `(a,b,c) = (0,2π,π)`.
The theorem yields some `lam`; evaluating at `π/2` **recovers `lam = 3`**, so the
proportionality conclusion is non-vacuous and quantitatively correct. -/
example : ∃ lam : ℝ, lam = 3 ∧ ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    3 * sturmModel 1 0 t = lam * sturmModel 1 0 t := by
  obtain ⟨lam, hlam⟩ := exists_smul_sturmModel_of_curvature_eq
    (k := fun _ : ℝ => (1 : ℝ)) (K := 1) (a := 0) (b := 2 * Real.pi) (c := Real.pi)
    (u := fun t => 3 * sturmModel 1 0 t) (du := fun t => 3 * sturmModelDeriv 1 0 t)
    (ddu := fun t => 3 * sturmModelSecondDeriv 1 0 t)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero]) (fun _ _ => rfl)
    hmodel3 hca hua3
  have ht : Real.pi / 2 ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hval := hlam (Real.pi / 2) ht
  have hm : sturmModel 1 0 (Real.pi / 2) = 1 := by simp [sturmModel]
  rw [hm, mul_one, mul_one] at hval
  exact ⟨lam, by linarith, hlam⟩

/-- (5) `wronskian_sturmModel_eq_zero_of_curvature_eq` with `u = 3m`: `W ≡ 0` on `[0,π]`,
in particular at `π/2` where `m > 0` and `u > 0`. -/
example : wronskian (sturmModel 1 0) (sturmModelDeriv 1 0)
    (fun t => 3 * sturmModel 1 0 t) (fun t => 3 * sturmModelDeriv 1 0 t)
    (Real.pi / 2) = 0 :=
  wronskian_sturmModel_eq_zero_of_curvature_eq (k := fun _ : ℝ => (1 : ℝ)) (K := 1)
    (a := 0) (b := 2 * Real.pi) (c := Real.pi) (u := fun t => 3 * sturmModel 1 0 t)
    (du := fun t => 3 * sturmModelDeriv 1 0 t) (ddu := fun t => 3 * sturmModelSecondDeriv 1 0 t)
    (by norm_num) (fun _ _ => rfl) hmodel3 hca hua3 (Real.pi / 2)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- (4) `exists_smul_sturmModel_of_wronskian_eq_zero` used directly with the identically
vanishing Wronskian of `3m` against `m`; again `lam = 3` is recovered. -/
example : ∃ lam : ℝ, lam = 3 ∧ ∀ t ∈ Ioo (0 : ℝ) Real.pi,
    3 * sturmModel 1 0 t = lam * sturmModel 1 0 t := by
  obtain ⟨lam, hlam⟩ := exists_smul_sturmModel_of_wronskian_eq_zero (K := 1) (a := 0)
    (c := Real.pi) (u := fun t => 3 * sturmModel 1 0 t) (du := fun t => 3 * sturmModelDeriv 1 0 t)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero])
    (fun t _ => (hasDerivAtR_sturmModel 1 0 t).const_mul 3)
    (wronskian_sturmModel_eq_zero_of_curvature_eq (k := fun _ : ℝ => (1 : ℝ)) (K := 1)
      (a := 0) (b := 2 * Real.pi) (c := Real.pi) (u := fun t => 3 * sturmModel 1 0 t)
      (du := fun t => 3 * sturmModelDeriv 1 0 t)
      (ddu := fun t => 3 * sturmModelSecondDeriv 1 0 t)
      (by norm_num) (fun _ _ => rfl) hmodel3 hca hua3)
  have ht : Real.pi / 2 ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hval := hlam (Real.pi / 2) ht
  have hm : sturmModel 1 0 (Real.pi / 2) = 1 := by simp [sturmModel]
  rw [hm, mul_one, mul_one] at hval
  exact ⟨lam, by linarith, hlam⟩

/-- (7) `eq_zero_of_wronskian_sturmModel_eq_zero` with `u ≡ 0`: satisfiable instance
(the only kind, by the theorem itself) on `(0,1)`. -/
example : ∀ t ∈ Ioo (0 : ℝ) 1, (fun _ : ℝ => (0 : ℝ)) t = 0 :=
  eq_zero_of_wronskian_sturmModel_eq_zero (K := 1) (a := 0) (c := 1)
    (u := fun _ : ℝ => 0) (du := fun _ : ℝ => 0)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero]; linarith [Real.pi_gt_three]) (by norm_num)
    continuousOn_const (fun t _ => hasDerivAtR_const 0 t) rfl
    (fun t _ => by simp [wronskian])

/-- (10) `nonvanishing_near_left_of_deriv_ne` for `sin` at `0`: concrete `ε` with the
one-sided nonvanishing property. -/
example : ∃ ε > 0, ∀ t, 0 < t → t < 0 + ε → sturmModel 1 0 t ≠ sturmModel 1 0 0 :=
  nonvanishing_near_left_of_deriv_ne (u := sturmModel 1 0) (a := 0) (m := 1)
    (by simpa [sturmModelDeriv] using hasDerivAtR_sturmModel 1 0 0) (by norm_num)

/-- (11) `no_zero_of_curvature_le_of_deriv_ne`, concrete non-vacuous instance:
`K=1`, `k ≡ 1`, `u = sin` on `[0,3]`, `√1·3 = 3 < π`; conclude no zero in `(0,3)`. -/
example : ∀ c ∈ Ioo (0 : ℝ) 3, sturmModel 1 0 c ≠ 0 :=
  no_zero_of_curvature_le_of_deriv_ne (k := fun _ : ℝ => (1 : ℝ)) (K := 1) (a := 0) (b := 3)
    (u := sturmModel 1 0) (du := sturmModelDeriv 1 0) (ddu := sturmModelSecondDeriv 1 0)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero]; exact le_of_lt Real.pi_gt_three)
    (fun _ _ => le_rfl)
    (sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := 3) (by norm_num))
    (hasDerivAtR_sturmModel 1 0 0) hua (by simp [sturmModelDeriv])

/-- (11') A second instance with a longer span `b = π - 1/2` (still `< π`). -/
example : ∀ c ∈ Ioo (0 : ℝ) (Real.pi - 1/2), sturmModel 1 0 c ≠ 0 :=
  no_zero_of_curvature_le_of_deriv_ne (k := fun _ : ℝ => (1 : ℝ)) (K := 1) (a := 0)
    (b := Real.pi - 1/2) (u := sturmModel 1 0) (du := sturmModelDeriv 1 0)
    (ddu := sturmModelSecondDeriv 1 0)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero]; linarith [Real.pi_pos])
    (fun _ _ => le_rfl)
    (sturmModel_jacobiSolutionOn (K := 1) (a := 0) (b := Real.pi - 1/2) (by norm_num))
    (hasDerivAtR_sturmModel 1 0 0) hua (by simp [sturmModelDeriv])

/-- (12) `strict_span_necessary` (revised): the statement now bundles `k ≤ 1` on `Icc 0 π`. -/
example : ∃ (k : ℝ → ℝ) (u du ddu : ℝ → ℝ),
    (∀ t ∈ Icc (0 : ℝ) Real.pi, k t ≤ 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, k t = 1) ∧
      JacobiSolutionOn k u du ddu 0 (2 * Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
      (∀ t ∈ Ioo (0 : ℝ) Real.pi, u t ≠ 0) ∧ Real.sqrt 1 * Real.pi = Real.pi :=
  strict_span_necessary

/-- (11'') A genuinely **nonconstant** curvature instance: `u t = t + t²`,
`k t = -2/(t+t²)`, `K = 1`, `a = 0`, `b = 1/2`.  Then `k < 0 < K` on `(0,1/2)` (a huge
deficit, `k` is unbounded below near `0`) and `u` solves `u'' + k u = 0` on `(0,1/2)`; the
theorem concludes `u c ≠ 0` on `(0,1/2)`, which holds since `u = t(1+t) > 0`.  This rules out
vacuity of `no_zero_of_curvature_le_of_deriv_ne` for nonconstant `k`. -/
example : ∀ c ∈ Ioo (0 : ℝ) (1/2), (fun t : ℝ => t + t^2) c ≠ 0 := by
  have hderiv : ∀ t : ℝ, HasDerivAtR (fun t : ℝ => t + t^2) (1 + 2*t) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := h1.add h2
    unfold HasDerivAtR
    convert h using 1
    funext x; rfl
  have hderiv2 : ∀ t : ℝ, HasDerivAtR (fun t : ℝ => 1 + 2*t) 2 t := by
    intro t
    have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
    have h2 : HasDerivAt (fun x : ℝ => 2*x) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have h := h1.add h2
    unfold HasDerivAtR
    convert h using 1
    · funext x; rfl
    · norm_num
  refine no_zero_of_curvature_le_of_deriv_ne
    (k := fun t : ℝ => -2/(t + t^2))
    (K := 1) (a := 0) (b := 1/2)
    (u := fun t : ℝ => t + t^2) (du := fun t : ℝ => 1 + 2*t) (ddu := fun _ : ℝ => 2)
    (by norm_num) (by rw [Real.sqrt_one, one_mul, sub_zero]; linarith [Real.pi_gt_three]) ?_ ?_
    (hderiv 0) (by norm_num) (by norm_num)
  · intro t ht
    by_cases ht0 : t = 0
    · subst ht0; norm_num
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hpos : 0 < t + t^2 := by nlinarith [sq_nonneg t]
      rw [div_le_iff₀ hpos]
      linarith [ht.1, sq_nonneg t]
  · refine ⟨fun t _ => hderiv t, fun t _ => hderiv2 t, ?_, ?_, ?_⟩
    · intro t ht
      have hden : t + t^2 ≠ 0 := by
        have : 0 < t + t^2 := by nlinarith [ht.1, sq_nonneg t]
        exact ne_of_gt this
      rw [neg_mul, div_mul_cancel₀]
      · norm_num
      · exact hden
    · fun_prop
    · fun_prop

end AcceptSturmUniqueness
