/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C4 — direct Euclidean normalization of the constant-curvature model `j_K` and Rauch I

This file extends the flat-model L4 Jacobi/Rauch bridge (`u'/u ≤ 1/t` for `k ≥ 0`) to the
D10 constant-curvature model `jacobiSol K` for `K ≥ 0`.

## The mathematical content

For the normalized constant-curvature Jacobi field `j_K` (`j_K'' + K j_K = 0`,
`j_K(0) = 0`, `j_K'(0) = 1`, D10 `Poincare.D10.jacobiSol`) we prove the **direct**
Euclidean-normalization bound, with no intermediate second-derivative constant:

* `jacobiSol_logDeriv_bound` (proved): for `K ≥ 0`, `t > 0`, `K t² ≤ 1`,
  `|j_K'(t)/j_K(t) − 1/t| ≤ K t`.
* `jacobiSol_logDeriv_normalized` (proved): consequently
  `EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀` whenever `K t₀² ≤ 1`, i.e.
  `|j_K'(t)/j_K(t) − 1/t| ≤ K t₀` on `(0,t₀)`.

The proof is spherical-branch explicit: with `x = √K t` one has
`j_K'/j_K − 1/t = (x cos x − sin x)/(t sin x)`, so taking absolute values and using the two
elementary bounds `0 ≤ sin x − x cos x` and `sin x − x cos x ≤ x³/3` (both proved here from
the derivative sign, using `Real.sin_le` and `Real.sin_ge_sub_cube`) gives
`≤ (x³/3)/(t sin x) ≤ (√K)² t = K t`, the last step from `x/3 ≤ sin x` for `x ≤ 1`.
The `K = 0` branch has `j_0(t) = t`, `j_0'(t) = 1`, so the bound is `0 ≤ 0`: the flat model
is the endpoint of the family, not a separate theorem.

Feeding this normalization, together with the Riccati identity for `j_K`
(`jacobiSol_riccati_identity`), into the D12 singular engine
`riccati_le_of_singular_normalization` yields the **classical Rauch I comparison**

* `rauch_upper_of_constCurv` (conditional, proved): for a scalar Jacobi solution `u` with
  `k ≥ K ≥ 0` on `(0,T)`, `T` before the first zero of `j_K` (`K = 0` or `√K T < π`),
  `u > 0` on `(0,T]`, and the quantitative Euclidean normalization of `u'/u` with constant
  `Cu` on `(0,t₀)`:
  `u'(t)/u(t) ≤ j_K'(t)/j_K(t)` on `(0,T)`.
* `rauch_upper_of_constCurv_jacobi` (conditional, proved): the same with the normalization of
  `u'/u` *constructed* from genuine Jacobi initial data `u 0 = 0`, `u' 0 = 1` and a
  second-derivative bound `|u''| ≤ B` (the mean-value linear bounds
  `abs_sub_le_of_deriv_bound`, `jacobi_linear_bounds`, `jacobi_pos_and_ratio_bound` are
  re-proved in-file rather than imported; they follow the same standard mean-value route as
  the prior L4 flat bridge and are not claimed as a novel or independent re-derivation).
* `rauch_upper_flat_of_jacobi` (conditional, proved): the `K = 0` specialization recovers the
  flat comparison `u'/u ≤ 1/t`, so the flat bridge is the `K = 0` case of the constant-curvature
  theorem.

## Non-vacuity

* `spherical_rauch_witness` (model, proved): the spherical comparison `k = 4` against `K = 1`
  on `(0,1/2)` with `B = 2`, `t₀ = 1/4` satisfies every hypothesis, giving
  `j_4'/j_4 ≤ j_1'/j_1`; `spherical_rauch_witness_cot` states it as
  `2·cot(2t) ≤ cot t`, a genuinely nontrivial strict inequality near `0`.
* `jacobiSolOne_normalization_witness`, `jacobiSolOne_normalized`, `flat_model_normalized`
  (model, proved): the normalization bound is instantiated at `K = 1` and at `K = 0`.

No geometric identification of `u` with a geodesic-sphere area density (shape-operator
Riccati equation, Cauchy–Schwarz) is claimed: the semantic class of the Rauch theorems here
is *conditional scalar analytic comparison*, exactly as in the D12/L4 chain.
-/
import Poincare.D10.JacobiConstantCurvature.Comparison
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

open Set Filter
open scoped Topology
open MeasureTheory

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics Poincare.D10

/-! ## 1. Elementary trigonometric bounds

The two inequalities on `sin x − x cos x` are proved from the sign of the derivative (no
series, no integral representation), using mathlib's `Real.sin_le` and `Real.sin_ge_sub_cube`. -/

/-- `sin x − x cos x ≥ 0` on `[0,π]`: its derivative is `x sin x ≥ 0` there and it vanishes
at `0`. -/
theorem sin_sub_mul_cos_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) Real.pi,
      HasDerivAtR (fun z : ℝ => Real.sin z - z * Real.cos z) (y * Real.sin y) y := by
    intro y _
    have h1 : HasDerivAtR (fun z : ℝ => Real.sin z) (Real.cos y) y := Real.hasDerivAt_sin y
    have hid : HasDerivAtR (fun z : ℝ => z) (1 : ℝ) y := hasDerivAt_id y
    have hcos : HasDerivAtR Real.cos (-Real.sin y) y := Real.hasDerivAt_cos y
    have hmul : HasDerivAtR ((fun z : ℝ => z) * Real.cos)
        (1 * Real.cos y + y * (-Real.sin y)) y := HasDerivAt.mul hid hcos
    have h2 : HasDerivAtR (fun z : ℝ => z * Real.cos z)
        (Real.cos y + y * (-Real.sin y)) y := by
      have hfun : ((fun z : ℝ => z) * Real.cos) = fun z : ℝ => z * Real.cos z := by
        funext z; rfl
      have hderiv' : (1 : ℝ) * Real.cos y + y * (-Real.sin y)
          = Real.cos y + y * (-Real.sin y) := by ring
      simpa only [hfun, hderiv'] using hmul
    have hsub : HasDerivAtR ((fun z : ℝ => Real.sin z) - fun z : ℝ => z * Real.cos z)
        (Real.cos y - (Real.cos y + y * (-Real.sin y))) y := HasDerivAt.sub h1 h2
    have hfun : ((fun z : ℝ => Real.sin z) - fun z : ℝ => z * Real.cos z)
        = fun z : ℝ => Real.sin z - z * Real.cos z := by funext z; rfl
    have heq : Real.cos y - (Real.cos y + y * (-Real.sin y)) = y * Real.sin y := by ring
    simpa only [hfun, heq] using hsub
  have hmono : MonotoneOn (fun z : ℝ => Real.sin z - z * Real.cos z) (Icc 0 Real.pi) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 Real.pi) (by fun_prop) ?_ ?_
    · intro y hy
      exact (hderiv y (by simpa [interior_Icc] using hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y hy).deriv]
      exact mul_nonneg hy.1.le (Real.sin_nonneg_of_mem_Icc ⟨hy.1.le, hy.2.le⟩)
  have h0 : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hx : x ∈ Icc 0 Real.pi := ⟨hx0, hxπ⟩
  have h := hmono h0 hx hx0
  have h' : (0 : ℝ) ≤ Real.sin x - x * Real.cos x := by simpa using h
  exact h'

/-- `sin x − x cos x ≤ x³/3` for `x ≥ 0`: the function `x³/3 − (sin x − x cos x)` has
derivative `x (x − sin x) ≥ 0` and vanishes at `0`. -/
theorem sin_sub_mul_cos_le_cube {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x - x * Real.cos x ≤ x ^ 3 / 3 := by
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) x,
      HasDerivAtR (fun z : ℝ => z ^ 3 / 3 - (Real.sin z - z * Real.cos z))
        (y * (y - Real.sin y)) y := by
    intro y _
    have h3 : HasDerivAtR (fun z : ℝ => z ^ 3 / 3) (y ^ 2) y := by
      have hp : HasDerivAtR (fun z : ℝ => z ^ 3 * (1 / 3))
          ((3 : ℝ) * y ^ (3 - 1) * (1 / 3)) y :=
        HasDerivAt.mul_const (hasDerivAtR_pow 3 y) (1 / 3)
      have hfun : (fun z : ℝ => z ^ 3 * (1 / 3)) = fun z : ℝ => z ^ 3 / 3 := by
        funext z; ring
      have hval : (3 : ℝ) * y ^ (3 - 1) * (1 / 3) = y ^ 2 := by ring
      simpa only [hfun, hval] using hp
    have h1 : HasDerivAtR (fun z : ℝ => Real.sin z) (Real.cos y) y := Real.hasDerivAt_sin y
    have hid : HasDerivAtR (fun z : ℝ => z) (1 : ℝ) y := hasDerivAt_id y
    have hcos : HasDerivAtR Real.cos (-Real.sin y) y := Real.hasDerivAt_cos y
    have hmul : HasDerivAtR ((fun z : ℝ => z) * Real.cos)
        (1 * Real.cos y + y * (-Real.sin y)) y := HasDerivAt.mul hid hcos
    have hs : HasDerivAtR (fun z : ℝ => Real.sin z - z * Real.cos z) (y * Real.sin y) y := by
      have h2 : HasDerivAtR (fun z : ℝ => z * Real.cos z)
          (Real.cos y + y * (-Real.sin y)) y := by
        have hfun : ((fun z : ℝ => z) * Real.cos) = fun z : ℝ => z * Real.cos z := by
          funext z; rfl
        have hderiv' : (1 : ℝ) * Real.cos y + y * (-Real.sin y)
            = Real.cos y + y * (-Real.sin y) := by ring
        simpa only [hfun, hderiv'] using hmul
      have hsub : HasDerivAtR ((fun z : ℝ => Real.sin z) - fun z : ℝ => z * Real.cos z)
          (Real.cos y - (Real.cos y + y * (-Real.sin y))) y := HasDerivAt.sub h1 h2
      have hfun : ((fun z : ℝ => Real.sin z) - fun z : ℝ => z * Real.cos z)
          = fun z : ℝ => Real.sin z - z * Real.cos z := by funext z; rfl
      have heq : Real.cos y - (Real.cos y + y * (-Real.sin y)) = y * Real.sin y := by ring
      simpa only [hfun, heq] using hsub
    have hsub : HasDerivAtR ((fun z : ℝ => z ^ 3 / 3) - fun z : ℝ => Real.sin z - z * Real.cos z)
        (y ^ 2 - y * Real.sin y) y := HasDerivAt.sub h3 hs
    have hfun : ((fun z : ℝ => z ^ 3 / 3) - fun z : ℝ => Real.sin z - z * Real.cos z)
        = fun z : ℝ => z ^ 3 / 3 - (Real.sin z - z * Real.cos z) := by funext z; rfl
    have heq : y ^ 2 - y * Real.sin y = y * (y - Real.sin y) := by ring
    simpa only [hfun, heq] using hsub
  have hmono : MonotoneOn (fun z : ℝ => z ^ 3 / 3 - (Real.sin z - z * Real.cos z))
      (Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) (by fun_prop) ?_ ?_
    · intro y hy
      exact (hderiv y (by simpa [interior_Icc] using hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y hy).deriv]
      exact mul_nonneg hy.1.le (sub_nonneg.mpr (Real.sin_le hy.1.le))
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx⟩
  have hx' : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
  have h := hmono h0 hx' hx
  have h' : (0 : ℝ) ≤ x ^ 3 / 3 - (Real.sin x - x * Real.cos x) := by simpa using h
  linarith

/-! ## 2. The direct log-derivative bound for the spherical branch -/

/-- **Spherical log-derivative bound (auxiliary form).**  For `a > 0`, `t > 0`, `a t ≤ 1`,
the logarithmic derivative of `sin (a ·)/a` differs from `1/t` by at most `a² t`:
`|cos (a t)/(sin (a t)/a) − 1/t| ≤ a² t`. -/
theorem sphere_logDeriv_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (hat : a * t ≤ 1) :
    |Real.cos (a * t) / (Real.sin (a * t) / a) - 1 / t| ≤ a ^ 2 * t := by
  have hx0 : 0 ≤ a * t := mul_nonneg ha.le ht.le
  have hxpi : a * t ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hsinpos : 0 < Real.sin (a * t) :=
    Real.sin_pos_of_mem_Ioo ⟨mul_pos ha ht, by linarith [Real.pi_gt_three]⟩
  have hsinne : Real.sin (a * t) ≠ 0 := ne_of_gt hsinpos
  -- rewrite the difference with the common denominator `t sin (a t)`
  have hrewrite : Real.cos (a * t) / (Real.sin (a * t) / a) - 1 / t
      = (a * t * Real.cos (a * t) - Real.sin (a * t)) / (t * Real.sin (a * t)) := by
    field_simp [hsinne, ht.ne', ha.ne']
  -- numerator bounds: `0 ≤ sin x − x cos x ≤ x³/3`, `x = a t`
  have hnum_nonneg : 0 ≤ Real.sin (a * t) - a * t * Real.cos (a * t) :=
    sin_sub_mul_cos_nonneg hx0 hxpi
  have hnum_le : Real.sin (a * t) - a * t * Real.cos (a * t) ≤ (a * t) ^ 3 / 3 :=
    sin_sub_mul_cos_le_cube hx0
  have habs : |a * t * Real.cos (a * t) - Real.sin (a * t)|
      = Real.sin (a * t) - a * t * Real.cos (a * t) := by
    have hneg : a * t * Real.cos (a * t) - Real.sin (a * t)
        = -(Real.sin (a * t) - a * t * Real.cos (a * t)) := by ring
    rw [hneg, abs_neg, abs_of_nonneg hnum_nonneg]
  have hden : 0 < t * Real.sin (a * t) := mul_pos ht hsinpos
  -- `x/3 ≤ sin x` from `sin x ≥ x − x³/6` and `x ≤ 1`
  have hthird : (a * t) / 3 ≤ Real.sin (a * t) := by
    have hc := Real.sin_ge_sub_cube hx0
    nlinarith [hc, hat, hx0, sq_nonneg (a * t)]
  rw [hrewrite, abs_div, abs_of_pos hden, habs]
  calc (Real.sin (a * t) - a * t * Real.cos (a * t)) / (t * Real.sin (a * t))
      ≤ ((a * t) ^ 3 / 3) / (t * Real.sin (a * t)) :=
        div_le_div_of_nonneg_right hnum_le hden.le
    _ ≤ (a ^ 2 * t ^ 2 * Real.sin (a * t)) / (t * Real.sin (a * t)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        calc (a * t) ^ 3 / 3 = a ^ 2 * t ^ 2 * ((a * t) / 3) := by ring
          _ ≤ a ^ 2 * t ^ 2 * Real.sin (a * t) :=
              mul_le_mul_of_nonneg_left hthird (by positivity)
    _ = a ^ 2 * t := by
        field_simp [hsinne, ht.ne']

/-- **The normalized Jacobi field `j_K` is bounded by `1/√K` on the spherical branch.** -/
theorem jacobiSolSphere_abs_le {K t : ℝ} (hK : 0 < K) :
    |jacobiSolSphere K t| ≤ 1 / Real.sqrt K := by
  rw [jacobiSolSphere, abs_div, abs_of_pos (Real.sqrt_pos_of_pos hK)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (Real.sqrt_pos_of_pos hK).le

/-- **Log-derivative bound for the spherical model `j_K`, `K > 0`.**  For `t > 0` with
`K t² ≤ 1`, `|j_K'(t)/j_K(t) − 1/t| ≤ K t`. -/
theorem jacobiSolSphere_logDeriv_bound {K t : ℝ} (hK : 0 < K) (ht : 0 < t)
    (hKt : K * t ^ 2 ≤ 1) :
    |Real.cos (Real.sqrt K * t) / jacobiSolSphere K t - 1 / t| ≤ K * t := by
  have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
  have hat : Real.sqrt K * t ≤ 1 := by
    have h2 : (Real.sqrt K * t) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hK.le]
      exact hKt
    nlinarith [Real.sqrt_nonneg K, ht.le, h2]
  have h := sphere_logDeriv_bound hsqrt ht hat
  have ha2 : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK.le
  rw [jacobiSolSphere]
  simpa [ha2] using h

/-- **Direct Euclidean-normalization bound for the constant-curvature model.**  For every
`K ≥ 0`, `t > 0` with `K t² ≤ 1`:
`|j_K'(t)/j_K(t) − 1/t| ≤ K t`.  The flat case `K = 0` gives `|1 − 1| = 0 ≤ 0`. -/
theorem jacobiSol_logDeriv_bound {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (hKt : K * t ^ 2 ≤ 1) :
    |jacobiDeriv K t / jacobiSol K t - 1 / t| ≤ K * t := by
  rcases eq_or_lt_of_le hK with h0 | hpos
  · subst h0
    simp [jacobiSol_of_zero, jacobiSolFlat, jacobiDeriv_of_zero]
  · rw [jacobiSol_of_pos hpos, jacobiDeriv_of_pos hpos]
    exact jacobiSolSphere_logDeriv_bound hpos ht hKt

/-- **The model normalization interface consumed by the D12 singular engine.**
For `K ≥ 0`, `t₀ > 0` with `K t₀² ≤ 1`:
`EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀`, i.e. `|j_K'(t)/j_K(t) − 1/t| ≤ K t₀` for
every `t ∈ (0,t₀)`. -/
theorem jacobiSol_logDeriv_normalized {K t₀ : ℝ} (hK : 0 ≤ K) (ht₀ : 0 < t₀)
    (hKt₀ : K * t₀ ^ 2 ≤ 1) :
    EuclideanNormalizedOn (fun t => jacobiDeriv K t / jacobiSol K t) 1 (K * t₀) t₀ := by
  intro t ht
  have htpos : 0 < t := ht.1
  have htle : t ≤ t₀ := ht.2.le
  have hKt : K * t ^ 2 ≤ 1 := by
    have h2 : t ^ 2 ≤ t₀ ^ 2 := by nlinarith [htpos, htle]
    nlinarith [hKt₀, hK, h2]
  calc |jacobiDeriv K t / jacobiSol K t - 1 / t| ≤ K * t :=
        jacobiSol_logDeriv_bound hK htpos hKt
    _ ≤ K * t₀ := mul_le_mul_of_nonneg_left htle hK

/-! ## 3. Positivity and the Riccati identity for the model -/

/-- **Positivity of the constant-curvature model.**  For `K ≥ 0` and `0 < t` before the first
zero (`K = 0`, or `√K t < π`), `jacobiSol K t > 0`. -/
theorem jacobiSol_pos_of_nonneg {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (hzero : K = 0 ∨ Real.sqrt K * t < Real.pi) : 0 < jacobiSol K t := by
  rcases eq_or_lt_of_le hK with h | h
  · rw [← h, jacobiSol_of_zero]
    simpa [jacobiSolFlat] using ht
  · rcases hzero with h0 | hpi
    · exact absurd h0 (ne_of_gt h)
    · rw [jacobiSol_of_pos h]
      exact jacobiSolSphere_pos h ht hpi

/-- Positivity on `(0,T]` from the "before the first zero" condition at `T`. -/
theorem jacobiSol_pos_of_nonneg_Ioc {K T : ℝ} (hK : 0 ≤ K)
    (hzero : K = 0 ∨ Real.sqrt K * T < Real.pi) :
    ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t := by
  intro t ht
  refine jacobiSol_pos_of_nonneg hK ht.1 ?_
  rcases hzero with h0 | hpi
  · exact Or.inl h0
  · exact Or.inr (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hpi)

/-- **The Riccati identity for the constant-curvature model.**  On `(0,T)`, with the model
positive on `(0,T]`, the logarithmic derivative `m = j_K'/j_K` is differentiable with
derivative `(j_K'' j_K − (j_K')²)/j_K²` and satisfies the Riccati equality
`m' + m²/1 + K = 0` (the D12 engine's `d = 1` normalization).  The second derivative of the
model is `−K j_K`.  (Positivity of the model on `(0,T]` is the only hypothesis needed; `K ≥ 0`
is used by the callers to *produce* it, via `jacobiSol_pos_of_nonneg_Ioc`.) -/
theorem jacobiSol_riccati_identity {K T : ℝ}
    (hpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t) :
    (∀ t ∈ Ioo 0 T, HasDerivAtR (fun s => jacobiDeriv K s / jacobiSol K s)
        (((-(K * jacobiSol K t)) * jacobiSol K t - jacobiDeriv K t ^ 2) /
          jacobiSol K t ^ 2) t) ∧
    (∀ t ∈ Ioo 0 T, ((-(K * jacobiSol K t)) * jacobiSol K t - jacobiDeriv K t ^ 2) /
        jacobiSol K t ^ 2 + (jacobiDeriv K t / jacobiSol K t) ^ 2 / 1 + K = 0) := by
  constructor
  · intro t ht
    have hne : jacobiSol K t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    have hd : HasDerivAtR (fun s => jacobiDeriv K s / jacobiSol K s)
        ((-(K * jacobiSol K t) * jacobiSol K t - jacobiDeriv K t * jacobiDeriv K t) /
          jacobiSol K t ^ 2) t :=
      HasDerivAt.div (hasDerivAt_jacobiDeriv K t) (hasDerivAt_jacobiSol K t) hne
    simpa only [pow_two] using hd
  · intro t ht
    have hne : jacobiSol K t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    field_simp [hne]
    ring

/-! ## 4. The Jacobi initial-data normalization (re-proved, independent of the flat bridge) -/

/-- **Mean-value/FTC bound with interior differentiability only.**  If `f` is continuous on
`[a,b]`, `f'` is continuous on `[a,b]`, `f` has derivative `f' t` at every interior point and
`|f'| ≤ C` on `(a,b)`, then `|f b − f a| ≤ C (b − a)`. -/
theorem abs_sub_le_of_deriv_bound {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hfcont : ContinuousOn f (Icc a b)) (hf'cont : ContinuousOn f' (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAtR f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, |f' t| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  have hFTC : ∫ t in a..b, f' t = f b - f a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hfcont hderiv
      ((by rwa [uIcc_of_le hab] : ContinuousOn f' (uIcc a b))).intervalIntegrable
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ uIoc a b → ‖f' t‖ ≤ C := by
    have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hb] with t htb ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    simpa [Real.norm_eq_abs] using hbound t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  have hnorm : ‖∫ t in a..b, f' t‖ ≤ C * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hnull
  rw [hFTC, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-- **Jacobi linear bounds.**  From genuine Jacobi initial data `u 0 = 0`, `u' 0 = 1` and a
second-derivative bound `|u''| ≤ B` on `(0,T)`, the solution satisfies the Euclidean-tangent
bounds `|u' t − 1| ≤ B t` and `|u t − t| ≤ B t²`. -/
theorem jacobi_linear_bounds {k u du ddu : ℝ → ℝ} {T B : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1) :
    (∀ t ∈ Ioo 0 T, |du t - 1| ≤ B * t) ∧ (∀ t ∈ Ioo 0 T, |u t - t| ≤ B * t ^ 2) := by
  have hfirst : ∀ t ∈ Ioo 0 T, |du t - 1| ≤ B * t := by
    intro t ht
    have hmain := abs_sub_le_of_deriv_bound (f := fun s => du s - 1) (f' := ddu)
      (a := 0) (b := t) (C := B) ht.1.le
      ((h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_const)
      (hdducont.mono (Icc_subset_Icc_right ht.2.le))
      (fun x hx => by
        have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
        have hsub : HasDerivAtR (du - fun _ : ℝ => (1 : ℝ)) (ddu x - 0) x :=
          (h.hasDerivAt_du hxT).sub (hasDerivAtR_const (1 : ℝ) x)
        have hfun : (du - fun _ : ℝ => (1 : ℝ)) = fun s : ℝ => du s - 1 := by
          funext s; rfl
        simpa only [hfun, sub_zero] using hsub)
      (fun x hx => hB x ⟨hx.1, lt_trans hx.2 ht.2⟩)
    simpa [hdu0] using hmain
  refine ⟨hfirst, ?_⟩
  intro t ht
  have hbound : ∀ x ∈ Ioo 0 t, |du x - 1| ≤ B * t := by
    intro x hx
    exact le_trans (hfirst x ⟨hx.1, lt_trans hx.2 ht.2⟩)
      (mul_le_mul_of_nonneg_left hx.2.le hBnn)
  have hmain := abs_sub_le_of_deriv_bound (f := fun s => u s - s) (f' := fun s => du s - 1)
    (a := 0) (b := t) (C := B * t) ht.1.le
    ((h.continuousOn_u.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_id)
    ((h.continuousOn_du.mono (Icc_subset_Icc_right ht.2.le)).sub continuousOn_const)
    (fun x hx => by
      have hxT : x ∈ Ioo 0 T := ⟨hx.1, lt_trans hx.2 ht.2⟩
      have hsub : HasDerivAtR (u - fun s : ℝ => s) (du x - 1) x :=
        (h.hasDerivAt_u hxT).sub (hasDerivAtR_id x)
      have hfun : (u - fun s : ℝ => s) = fun s : ℝ => u s - s := by
        funext s; rfl
      simpa only [hfun] using hsub)
    hbound
  have hmain' : |u t - t| ≤ B * t * t := by simpa [hu0] using hmain
  calc |u t - t| ≤ B * t * t := hmain'
    _ = B * t ^ 2 := by ring

/-- **Positivity and the ratio bound.**  Under the hypotheses of `jacobi_linear_bounds`, if in
addition `B t ≤ 1/2`, then `u t > 0` and `|u' t/u t − 1/t| ≤ 4B`. -/
theorem jacobi_pos_and_ratio_bound {k u du ddu : ℝ → ℝ} {T B : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hBt : B * t ≤ 1 / 2) :
    0 < u t ∧ |du t / u t - 1 / t| ≤ 4 * B := by
  obtain ⟨hdu, hu⟩ := jacobi_linear_bounds h hdducont hBnn hB hu0 hdu0
  have hdut : |du t - 1| ≤ B * t := hdu t ht
  have hut : |u t - t| ≤ B * t ^ 2 := hu t ht
  have htpos : 0 < t := ht.1
  have htne : t ≠ 0 := ne_of_gt htpos
  have hu_lower : t / 2 ≤ u t := by
    have h₁ : -(B * t ^ 2) ≤ u t - t := (abs_le.mp hut).1
    have h₂ : B * t * t ≤ t / 2 := by nlinarith
    linarith
  have hu_pos : 0 < u t := lt_of_lt_of_le (half_pos htpos) hu_lower
  have hune : u t ≠ 0 := ne_of_gt hu_pos
  have hcross : |t * du t - u t| ≤ 2 * B * t ^ 2 := by
    have hsplit : t * du t - u t = t * (du t - 1) - (u t - t) := by ring
    rw [hsplit]
    calc |t * (du t - 1) - (u t - t)|
        ≤ |t * (du t - 1)| + |u t - t| := abs_sub _ _
      _ = t * |du t - 1| + |u t - t| := by rw [abs_mul, abs_of_pos htpos]
      _ ≤ t * (B * t) + B * t ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hdut htpos.le) hut
      _ = 2 * B * t ^ 2 := by ring
  have hratio : |du t / u t - 1 / t| ≤ 4 * B := by
    have hrewrite : du t / u t - 1 / t = (t * du t - u t) / (t * u t) := by
      field_simp [hune, htne]
    rw [hrewrite, abs_div, abs_of_pos (mul_pos htpos hu_pos)]
    have hb0 : 0 ≤ 2 * B * t ^ 2 := by positivity
    have htd : t * (t / 2) ≤ t * u t := mul_le_mul_of_nonneg_left hu_lower htpos.le
    have htdpos : 0 < t * (t / 2) := by positivity
    calc |t * du t - u t| / (t * u t)
        ≤ (2 * B * t ^ 2) / (t * u t) :=
          div_le_div_of_nonneg_right hcross (mul_pos htpos hu_pos).le
      _ ≤ (2 * B * t ^ 2) / (t * (t / 2)) :=
          div_le_div_of_nonneg_left hb0 htdpos htd
      _ = 4 * B := by field_simp; ring
  exact ⟨hu_pos, hratio⟩

/-- **Euclidean normalization from Jacobi initial data.**  If `|u''| ≤ B` on `(0,T)` and
`B t₀ ≤ 1/2`, then `EuclideanNormalizedOn (u'/u) 1 (4B) t₀`. -/
theorem euclideanNormalizedOn_of_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hBnn : 0 ≤ B) (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (_ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2) :
    EuclideanNormalizedOn (fun t => du t / u t) 1 (4 * B) t₀ := by
  intro t ht
  have htT : t ∈ Ioo 0 T := ⟨ht.1, lt_of_lt_of_le ht.2 ht₀T⟩
  have hBt : B * t ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left ht.2.le hBnn
    linarith
  exact (jacobi_pos_and_ratio_bound h hdducont hBnn hB hu0 hdu0 htT hBt).2

/-- **The Riccati identity for a positive Jacobi solution.**  If `u'' + k u = 0` and `u > 0`
on `(0,T]`, then `m = u'/u` is differentiable with derivative `(u'' u − (u')²)/u²` and
satisfies `m' + m²/1 + k = 0` on `(0,T)`. -/
theorem jacobi_riccati_identity {k u du ddu : ℝ → ℝ} {T : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) :
    (∀ t ∈ Ioo 0 T, HasDerivAtR (fun s => du s / u s)
        ((ddu t * u t - du t ^ 2) / u t ^ 2) t) ∧
    (∀ t ∈ Ioo 0 T, (ddu t * u t - du t ^ 2) / u t ^ 2
        + (du t / u t) ^ 2 / 1 + k t = 0) := by
  constructor
  · intro t ht
    have hune : u t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    have hd : HasDerivAtR (fun s => du s / u s)
        ((ddu t * u t - du t * du t) / u t ^ 2) t :=
      HasDerivAt.div (h.hasDerivAt_du ht) (h.hasDerivAt_u ht) hune
    simpa only [pow_two] using hd
  · intro t ht
    have hune : u t ≠ 0 := ne_of_gt (hpos t ⟨ht.1, ht.2.le⟩)
    rw [h.eq_secondDeriv ht]
    field_simp [hune]
    ring

/-! ## 5. Continuity of the logarithmic derivatives -/

/-- Continuity of `u'/u` on `(0,T]` for a positive Jacobi solution. -/
theorem logDeriv_continuousOn {k u du ddu : ℝ → ℝ} {T : ℝ}
    (h : JacobiSolutionOn k u du ddu 0 T) (hpos : ∀ t ∈ Ioc 0 T, 0 < u t) :
    ContinuousOn (fun t => du t / u t) (Ioc 0 T) := by
  have hdu' : ContinuousOn du (Ioc 0 T) :=
    h.continuousOn_du.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
  have hu' : ContinuousOn u (Ioc 0 T) :=
    h.continuousOn_u.mono (fun x hx => ⟨hx.1.le, hx.2⟩)
  exact hdu'.div hu' (fun x hx => ne_of_gt (hpos x hx))

/-- Continuity of `j_K'/j_K` on `(0,T]` for the positive model. -/
theorem logDeriv_continuousOn_jacobi {K T : ℝ}
    (hpos : ∀ t ∈ Ioc 0 T, 0 < jacobiSol K t) :
    ContinuousOn (fun t => jacobiDeriv K t / jacobiSol K t) (Ioc 0 T) := by
  have hdu : ContinuousOn (jacobiDeriv K) (Ioc 0 T) :=
    (continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_jacobiDeriv K t).continuousAt).continuousOn
  have hu : ContinuousOn (jacobiSol K) (Ioc 0 T) := (continuous_jacobiSol K).continuousOn
  exact hdu.div hu (fun x hx => ne_of_gt (hpos x hx))

/-! ## 6. Rauch I against the constant-curvature model -/

/-- **Rauch I (constant-curvature model, normalization form).**  Let `u` be a positive scalar
Jacobi solution on `(0,T)` with curvature `k ≥ K ≥ 0` (on `(0,T)`), with `T` before the first
zero of the model `j_K` (`K = 0` or `√K T < π`), and suppose `u'/u` satisfies the quantitative
Euclidean normalization with constant `Cu` on `(0,t₀)`, where `K t₀² ≤ 1`.  Then
`u'(t)/u(t) ≤ j_K'(t)/j_K(t)` for every `t ∈ (0,T)`.

This is the D12 singular Riccati engine fed with (i) the *direct* model normalization
`jacobiSol_logDeriv_normalized` (`C = K t₀`) and (ii) the model Riccati identity
`jacobiSol_riccati_identity`; the flat model `K = 0` is the special case `j_0(t) = t`. -/
theorem rauch_upper_of_constCurv {k u du ddu : ℝ → ℝ} {T Cu t₀ K : ℝ}
    (hT : 0 < T) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hCu : 0 ≤ Cu)
    (hK : 0 ≤ K) (hKt₀ : K * t₀ ^ 2 ≤ 1)
    (hzero : K = 0 ∨ Real.sqrt K * T < Real.pi)
    (h : JacobiSolutionOn k u du ddu 0 T)
    (hposu : ∀ t ∈ Ioc 0 T, 0 < u t)
    (hk : ∀ t ∈ Ioo 0 T, K ≤ k t)
    (hnormu : EuclideanNormalizedOn (fun t => du t / u t) 1 Cu t₀) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ jacobiDeriv K t / jacobiSol K t := by
  have hmodelpos := jacobiSol_pos_of_nonneg_Ioc (K := K) (T := T) hK hzero
  have hidu := jacobi_riccati_identity h hposu
  have hidm := jacobiSol_riccati_identity (K := K) hmodelpos
  have hnormm := jacobiSol_logDeriv_normalized (K := K) (t₀ := t₀) hK ht₀ hKt₀
  have hC : 0 ≤ max Cu (K * t₀) := le_trans hCu (le_max_left _ _)
  have hmain := riccati_le_of_singular_normalization (d := 1) (T := T)
    (C := max Cu (K * t₀)) (t₀ := t₀) (k := k) (kbar := fun _ : ℝ => K)
    (m := fun t => du t / u t)
    (dm := fun t => (ddu t * u t - du t ^ 2) / u t ^ 2)
    (mbar := fun t => jacobiDeriv K t / jacobiSol K t)
    (dmbar := fun t => ((-(K * jacobiSol K t)) * jacobiSol K t - jacobiDeriv K t ^ 2) /
      jacobiSol K t ^ 2)
    (by norm_num) hT hC ht₀ ht₀T
    (fun t ht => le_of_eq (hidu.2 t ht))
    (fun t ht => hidm.2 t ht)
    (fun t ht => hk t ht)
    (fun t ht => hidu.1 t ht)
    (fun t ht => hidm.1 t ht)
    (logDeriv_continuousOn h hposu)
    (logDeriv_continuousOn_jacobi hmodelpos)
    (fun t ht => le_trans (hnormu ht) (le_max_left _ _))
    (fun t ht => le_trans (hnormm ht) (le_max_right _ _))
  intro t ht
  exact hmain ht

/-- **Classical Rauch I against `j_K` from genuine Jacobi initial data.**  For a scalar Jacobi
solution with `u 0 = 0`, `u' 0 = 1`, `|u''| ≤ B` on `(0,T)`, `B t₀ ≤ 1/2`, curvature
`k ≥ K ≥ 0` on `(0,T)`, and `T` before the first zero of `j_K`:
`u'(t)/u(t) ≤ j_K'(t)/j_K(t)` on `(0,T)`.  The normalization of `u'/u` is *constructed*
(`euclideanNormalizedOn_of_jacobi`), so no normalization hypothesis on `u` remains. -/
theorem rauch_upper_of_constCurv_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hposu : ∀ t ∈ Ioc 0 T, 0 < u t) (hK : 0 ≤ K) (hKt₀ : K * t₀ ^ 2 ≤ 1)
    (hzero : K = 0 ∨ Real.sqrt K * T < Real.pi)
    (hk : ∀ t ∈ Ioo 0 T, K ≤ k t) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ jacobiDeriv K t / jacobiSol K t :=
  rauch_upper_of_constCurv hT ht₀ ht₀T (by positivity) hK hKt₀ hzero h hposu hk
    (euclideanNormalizedOn_of_jacobi h hdducont hBnn hB hu0 hdu0 ht₀ ht₀T hBt₀)

/-- **The flat bridge is the `K = 0` case.**  Specializing `rauch_upper_of_constCurv_jacobi`
to `K = 0` recovers the flat-model Rauch I comparison `u'/u ≤ 1/t` of the prior L4 bridge
(`j_0(t) = t`, `j_0'(t) = 1`). -/
theorem rauch_upper_flat_of_jacobi {k u du ddu : ℝ → ℝ} {T B t₀ : ℝ}
    (hT : 0 < T) (hBnn : 0 ≤ B) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hBt₀ : B * t₀ ≤ 1 / 2)
    (h : JacobiSolutionOn k u du ddu 0 T) (hdducont : ContinuousOn ddu (Icc 0 T))
    (hB : ∀ t ∈ Ioo 0 T, |ddu t| ≤ B) (hu0 : u 0 = 0) (hdu0 : du 0 = 1)
    (hposu : ∀ t ∈ Ioc 0 T, 0 < u t) (hk : ∀ t ∈ Ioo 0 T, 0 ≤ k t) :
    ∀ t ∈ Ioo 0 T, du t / u t ≤ 1 / t := by
  have hmain := rauch_upper_of_constCurv_jacobi (K := 0) (B := B) (t₀ := t₀)
    hT hBnn ht₀ ht₀T hBt₀ h hdducont hB hu0 hdu0 hposu le_rfl (by norm_num)
    (Or.inl rfl) hk
  intro t ht
  have := hmain t ht
  simpa [jacobiSol_of_zero, jacobiSolFlat, jacobiDeriv_of_zero] using this

/-! ## 7. Non-vacuity: the spherical witness `k = 4` against `K = 1` -/

/-- The spherical solution `j_4 = sin(2·)/2` on `(0,1/2)` is a Jacobi solution with curvature
`4`, `j_4(0) = 0`, `j_4'(0) = 1` and `|j_4''| ≤ 2`. -/
theorem sphere_jacobiSolutionOn_four_oneHalf :
    JacobiSolutionOn (fun _ : ℝ => 4) (jacobiSol 4) (jacobiDeriv 4)
      (fun t => -(4 * jacobiSol 4 t)) 0 (1 / 2) where
  hasDerivAt_u := by
    intro t _
    exact hasDerivAt_jacobiSol 4 t
  hasDerivAt_du := by
    intro t _
    exact hasDerivAt_jacobiDeriv 4 t
  eq_secondDeriv := by
    intro t _
    ring
  continuousOn_u := (continuous_jacobiSol 4).continuousOn
  continuousOn_du :=
    (continuous_iff_continuousAt.mpr
      fun t => (hasDerivAt_jacobiDeriv 4 t).continuousAt).continuousOn

/-- **Spherical Rauch witness.**  With `k = 4`, `K = 1`, `B = 2`, `t₀ = 1/4` on `(0,1/2)`
every hypothesis of `rauch_upper_of_constCurv_jacobi` holds, and the conclusion
`j_4'(t)/j_4(t) ≤ j_1'(t)/j_1(t)` is a genuinely nontrivial strict inequality. -/
theorem spherical_rauch_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      jacobiDeriv 4 t / jacobiSol 4 t ≤ jacobiDeriv 1 t / jacobiSol 1 t := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hpos4 : ∀ t ∈ Ioc 0 (1 / 2), 0 < jacobiSol 4 t := by
    intro t ht
    refine jacobiSol_pos_of_nonneg (K := 4) (by norm_num) ht.1 (Or.inr ?_)
    rw [hsqrt4]
    nlinarith [ht.2, Real.pi_gt_three]
  have hB : ∀ t ∈ Ioo 0 (1 / 2), |(-(4 * jacobiSol 4 t))| ≤ 2 := by
    intro t ht
    have hle : jacobiSol 4 t ≤ 1 / 2 := by
      have h4 : jacobiSol 4 t = jacobiSolSphere 4 t :=
        jacobiSol_of_pos (K := 4) (t := t) (by norm_num)
      have hsp : 0 ≤ jacobiSolSphere 4 t := by
        rw [← h4]
        exact (hpos4 t ⟨ht.1, ht.2.le⟩).le
      have hb := jacobiSolSphere_abs_le (K := 4) (t := t) (by norm_num)
      rw [hsqrt4, abs_of_nonneg hsp] at hb
      rw [h4]
      exact hb
    rw [abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) (hpos4 t ⟨ht.1, ht.2.le⟩).le)]
    linarith
  have hmain := rauch_upper_of_constCurv_jacobi (T := 1 / 2) (B := 2) (t₀ := 1 / 4) (K := 1)
    (k := fun _ : ℝ => 4) (u := jacobiSol 4) (du := jacobiDeriv 4)
    (ddu := fun t => -(4 * jacobiSol 4 t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    sphere_jacobiSolutionOn_four_oneHalf
    (((continuous_const.mul (continuous_jacobiSol 4)).neg).continuousOn)
    hB (jacobiSol_zero 4) (jacobiDeriv_zero 4) hpos4 (by norm_num) (by norm_num)
    (Or.inr (by rw [Real.sqrt_one, one_mul]; linarith [Real.pi_gt_three]))
    (fun _ _ => by norm_num)
  intro t ht
  exact hmain t ht

/-- **Spherical Rauch witness, trigonometric form.**  The same instance states
`2·cot(2t) ≤ cot t` on `(0,1/2)`. -/
theorem spherical_rauch_witness_cot :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      2 * (Real.cos (2 * t) / Real.sin (2 * t)) ≤ Real.cos t / Real.sin t := by
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  intro t ht
  have h := spherical_rauch_witness t ht
  rw [jacobiSol_of_pos (K := 4) (t := t) (by norm_num : (0 : ℝ) < 4),
    jacobiDeriv_of_pos (K := 4) (by norm_num : (0 : ℝ) < 4),
    jacobiSol_of_pos (K := 1) (t := t) (by norm_num : (0 : ℝ) < 1),
    jacobiDeriv_of_pos (K := 1) (by norm_num : (0 : ℝ) < 1),
    jacobiSolSphere, jacobiSolSphere, hsqrt4, Real.sqrt_one] at h
  have h' : Real.cos (2 * t) / (Real.sin (2 * t) / 2) ≤ Real.cos t / Real.sin t := by
    simpa using h
  calc 2 * (Real.cos (2 * t) / Real.sin (2 * t))
      = Real.cos (2 * t) / (Real.sin (2 * t) / 2) := by ring
    _ ≤ Real.cos t / Real.sin t := h'

/-- **Normalization witness at `K = 1`.**  The pointwise direct bound
`|j_1'(t)/j_1(t) − 1/t| ≤ t` on `(0,1/2)`. -/
theorem jacobiSolOne_normalization_witness :
    ∀ t ∈ Ioo (0 : ℝ) (1 / 2),
      |jacobiDeriv 1 t / jacobiSol 1 t - 1 / t| ≤ t := by
  intro t ht
  have h := jacobiSol_logDeriv_bound (K := 1) (t := t) (by norm_num) ht.1 (by nlinarith [ht.1, ht.2])
  simpa using h

/-- **Normalization interface witness at `K = 1`.**  `EuclideanNormalizedOn (j_1'/j_1) 1 (1/2)
(1/2)`, the exact interface consumed by the D12 engine with `C = K t₀ = 1/2`. -/
theorem jacobiSolOne_normalized :
    EuclideanNormalizedOn (fun t => jacobiDeriv 1 t / jacobiSol 1 t) 1 (1 / 2) (1 / 2) := by
  simpa using jacobiSol_logDeriv_normalized (K := 1) (t₀ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

/-- **Flat endpoint witness.**  For `K = 0` the direct normalization is the exact identity
`j_0'/j_0 = 1/t`, i.e. `EuclideanNormalizedOn (j_0'/j_0) 1 0 1` with constant `C = 0`. -/
theorem flat_model_normalized :
    EuclideanNormalizedOn (fun t => jacobiDeriv 0 t / jacobiSol 0 t) 1 0 1 := by
  intro t _
  simp [jacobiSol_of_zero, jacobiSolFlat, jacobiDeriv_of_zero]

end Poincare.L4.GeodesicComparison
