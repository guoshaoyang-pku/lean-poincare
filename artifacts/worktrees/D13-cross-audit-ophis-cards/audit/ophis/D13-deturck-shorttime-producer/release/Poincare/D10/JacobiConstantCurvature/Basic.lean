/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D10 — the scalar Jacobi equation in constant sectional curvature: definitions

In a space form of constant sectional curvature `K`, the normalised Jacobi field along a
unit-speed geodesic vanishing at `0` solves the scalar initial value problem

`j'' + K * j = 0`,   `j 0 = 0`,   `j' 0 = 1`.

The explicit solutions are

* `jacobiSolSphere K t = sin (√K * t) / √K` for `K > 0` (spherical space form),
* `jacobiSolFlat t = t` for `K = 0` (Euclidean space),
* `jacobiSolHyperbolic K t = sinh (√(-K) * t) / √(-K)` for `K < 0` (hyperbolic space form),

glued into the single piecewise function `jacobiSol K`.  The companion `jacobiDeriv K` is the
explicit first derivative (`cos (√K * t)`, `1`, `cosh (√(-K) * t)` respectively).

Everything in this file is unconditional: the only ingredients are mathlib's real `sin`, `cos`,
`sinh`, `cosh` and `Real.sqrt`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace Poincare.D10

/-- The `K > 0` branch of the normalised Jacobi field: `sin (√K t) / √K`. -/
noncomputable def jacobiSolSphere (K t : ℝ) : ℝ :=
  Real.sin (Real.sqrt K * t) / Real.sqrt K

/-- The `K = 0` branch of the normalised Jacobi field: `t`. -/
def jacobiSolFlat (t : ℝ) : ℝ := t

/-- The `K < 0` branch of the normalised Jacobi field: `sinh (√(-K) t) / √(-K)`. -/
noncomputable def jacobiSolHyperbolic (K t : ℝ) : ℝ :=
  Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

/-- The solution of the scalar Jacobi equation `j'' + K j = 0` with `j 0 = 0`, `j' 0 = 1`,
written piecewise in `K`: `sin (√K t)/√K` for `K > 0`, `t` for `K = 0`, and
`sinh (√(-K) t)/√(-K)` for `K < 0`. -/
noncomputable def jacobiSol (K t : ℝ) : ℝ :=
  if 0 < K then jacobiSolSphere K t
  else if K = 0 then jacobiSolFlat t
  else jacobiSolHyperbolic K t

/-- The explicit first derivative of `jacobiSol K`: `cos (√K t)` for `K > 0`, `1` for `K = 0`,
and `cosh (√(-K) t)` for `K < 0`. -/
noncomputable def jacobiDeriv (K t : ℝ) : ℝ :=
  if 0 < K then Real.cos (Real.sqrt K * t)
  else if K = 0 then 1
  else Real.cosh (Real.sqrt (-K) * t)

/-! ## Evaluation lemmas for the three branches -/

lemma jacobiSol_of_pos {K : ℝ} (h : 0 < K) (t : ℝ) :
    jacobiSol K t = jacobiSolSphere K t := by
  simp only [jacobiSol, ite_eq_left h]

lemma jacobiSol_of_zero (t : ℝ) : jacobiSol 0 t = jacobiSolFlat t := by
  rw [jacobiSol, ite_eq_right (lt_irrefl (0 : ℝ)), ite_eq_left rfl]

lemma jacobiSol_of_neg {K : ℝ} (h : K < 0) (t : ℝ) :
    jacobiSol K t = jacobiSolHyperbolic K t := by
  rw [jacobiSol, ite_eq_right (not_lt.mpr h.le), ite_eq_right (ne_of_lt h)]

lemma jacobiDeriv_of_pos {K : ℝ} (h : 0 < K) (t : ℝ) :
    jacobiDeriv K t = Real.cos (Real.sqrt K * t) := by
  simp only [jacobiDeriv, ite_eq_left h]

lemma jacobiDeriv_of_zero (t : ℝ) : jacobiDeriv 0 t = 1 := by
  rw [jacobiDeriv, ite_eq_right (lt_irrefl (0 : ℝ)), ite_eq_left rfl]

lemma jacobiDeriv_of_neg {K : ℝ} (h : K < 0) (t : ℝ) :
    jacobiDeriv K t = Real.cosh (Real.sqrt (-K) * t) := by
  rw [jacobiDeriv, ite_eq_right (not_lt.mpr h.le), ite_eq_right (ne_of_lt h)]

lemma jacobiSolSphere_zero (K : ℝ) : jacobiSolSphere K 0 = 0 := by
  simp [jacobiSolSphere]

lemma jacobiSolFlat_zero : jacobiSolFlat 0 = 0 := rfl

lemma jacobiSolHyperbolic_zero (K : ℝ) : jacobiSolHyperbolic K 0 = 0 := by
  simp [jacobiSolHyperbolic]

/-- The normalised Jacobi field vanishes at `0`, for every curvature `K`. -/
@[simp]
theorem jacobiSol_zero (K : ℝ) : jacobiSol K 0 = 0 := by
  rcases lt_trichotomy K 0 with h | h | h
  · rw [jacobiSol_of_neg h, jacobiSolHyperbolic_zero]
  · rw [h, jacobiSol_of_zero, jacobiSolFlat_zero]
  · rw [jacobiSol_of_pos h, jacobiSolSphere_zero]

/-- The explicit derivative at `0` is `1`, for every curvature `K`. -/
@[simp]
theorem jacobiDeriv_zero (K : ℝ) : jacobiDeriv K 0 = 1 := by
  rcases lt_trichotomy K 0 with h | h | h
  · rw [jacobiDeriv_of_neg h, mul_zero, Real.cosh_zero]
  · rw [h, jacobiDeriv_of_zero]
  · rw [jacobiDeriv_of_pos h, mul_zero, Real.cos_zero]

/-! ## Sign and monotonicity of the explicit branches -/

/-- On the spherical branch the normalised Jacobi field is nonnegative before its first
positive zero `π / √K`. -/
theorem jacobiSolSphere_nonneg {K t : ℝ} (hK : 0 < K) (ht : 0 ≤ t)
    (htpi : Real.sqrt K * t ≤ Real.pi) : 0 ≤ jacobiSolSphere K t := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hmem : Real.sqrt K * t ∈ Set.Icc 0 Real.pi := ⟨mul_nonneg hsqrt.le ht, htpi⟩
  have hsin : 0 ≤ Real.sin (Real.sqrt K * t) := Real.sin_nonneg_of_mem_Icc hmem
  exact div_nonneg hsin hsqrt.le

/-- The first positive zero of the spherical branch: `π / √K`. -/
theorem jacobiSolSphere_firstZero {K : ℝ} (hK : 0 < K) :
    jacobiSolSphere K (Real.pi / Real.sqrt K) = 0 := by
  have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos_of_pos hK).ne'
  rw [jacobiSolSphere, mul_div_cancel₀ Real.pi hsqrt, Real.sin_pi, zero_div]

/-- Up to its first positive zero the spherical branch is strictly positive. -/
theorem jacobiSolSphere_pos {K t : ℝ} (hK : 0 < K) (ht : 0 < t)
    (htpi : Real.sqrt K * t < Real.pi) : 0 < jacobiSolSphere K t := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hmem : Real.sqrt K * t ∈ Set.Ioo 0 Real.pi :=
    ⟨mul_pos hsqrt ht, htpi⟩
  exact div_pos (Real.sin_pos_of_mem_Ioo hmem) hsqrt

end Poincare.D10
