/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)
-/

import Mathlib
import Poincare.D13.ToppingAdapter.Scalar

/-!
# Poincare.D13.DeturckProducer.SmoothMetric

**The arbitrary smooth metric: the producer input of the Ricci--DeTurck Picard model.**

This file models "an arbitrary smooth Riemannian metric" in global coordinates on `ℝⁿ`:

* `SmoothMetricData n` — a symmetric `C²` matrix-valued metric field `g : ℝⁿ → Sym(n)` that is
  **uniformly elliptic**: there are constants `0 < lower ≤ upper` with
  `lower · ‖v‖² ≤ vᵀ g(x) v ≤ upper · ‖v‖²` for every `x` and `v`.  These are exactly the
  standard bounded-geometry hypotheses under which the DeTurck linearization at `g` is a
  *uniformly strictly parabolic* operator (proved in `SymbolMatrix.lean`), and they are plainly
  independent of any existence conclusion (they hold e.g. for the flat metric).
* `flatSmoothMetric n` — the flat metric `g = 1` as a `SmoothMetricData`, the non-vacuity
  witness and the instance on which the D12 Gaussian semigroup is the exact linearized
  evolution.

Every field is an explicit hypothesis about the metric; no field asserts existence of a flow.
The structure is the local transcription of "an arbitrary smooth metric with bounded
geometry" needed by the analytic antecedent of Hamilton/DeTurck short-time existence (U8).
-/

open scoped BigOperators
open scoped Matrix

set_option linter.unusedSimpArgs false

namespace Poincare
namespace D13
namespace DeturckProducer

noncomputable section

variable {n : ℕ}

/-! ## Norm instances

The matrix entries are analysed with the entrywise `dotProduct`; the `ContDiff` smoothness
field uses the (local) normed structure on matrices, exactly as in `Poincare.D7.ShortTime`.
-/

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

/-- The entrywise self-dot-product is nonnegative. -/
lemma dotProduct_self_nonneg (v : Fin n → ℝ) : 0 ≤ dotProduct v v := by
  rw [dotProduct]
  exact Finset.sum_nonneg (by
    intro i _
    simpa [pow_two] using sq_nonneg (v i))

/-- The entrywise self-dot-product is positive for a nonzero vector. -/
lemma dotProduct_self_pos_of_ne_zero {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v v := by
  rw [dotProduct]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ v i * v i := by
    intro i _
    exact mul_self_nonneg (v i)
  have hwit : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < v i * v i := by
    rcases Function.ne_iff.mp hv with ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simpa [sq] using sq_pos_of_ne_zero hi
  exact Finset.sum_pos' hnonneg hwit

/-! ## The arbitrary smooth metric -/

/-- **An arbitrary smooth Riemannian metric on `ℝⁿ` (global coordinates) with uniform
bounds.**  The fields are:

* `g` — the metric coefficients `g(x)` as a symmetric matrix field;
* `smooth` — `C²` smoothness of the coefficient field (what the Ricci tensor reads);
* `lower`, `coercive` — the uniform lower ellipticity bound
  `lower · ‖v‖² ≤ vᵀ g(x) v` with `lower > 0`;
* `upper`, `boundedAbove` — the uniform upper bound `vᵀ g(x) v ≤ upper · ‖v‖²`.

This is the local model of "an arbitrary smooth metric with bounded geometry": the input of
the Ricci--DeTurck Picard model producer.  None of the fields asserts the existence of any
evolution; they are plain regularity/bounds hypotheses. -/
structure SmoothMetricData (n : ℕ) where
  /-- The metric coefficients as a matrix field on `ℝⁿ`. -/
  g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- Symmetry of the metric coefficients. -/
  symm : ∀ x, (g x)ᵀ = g x
  /-- The coefficient field is `C²` (enough for the Ricci tensor). -/
  smooth : ContDiff ℝ 2 g
  /-- The uniform lower ellipticity constant. -/
  lower : ℝ
  /-- The lower constant is positive. -/
  lower_pos : 0 < lower
  /-- Uniform coercivity: `lower · ‖v‖² ≤ vᵀ g(x) v` for every `x`, `v`. -/
  coercive : ∀ x v, lower * dotProduct v v ≤ dotProduct v (g x *ᵥ v)
  /-- The uniform upper bound constant. -/
  upper : ℝ
  /-- The upper constant is positive. -/
  upper_pos : 0 < upper
  /-- Uniform upper bound: `vᵀ g(x) v ≤ upper · ‖v‖²` for every `x`, `v`. -/
  boundedAbove : ∀ x v, dotProduct v (g x *ᵥ v) ≤ upper * dotProduct v v

namespace SmoothMetricData

variable (G : SmoothMetricData n)

/-- Pointwise positive definiteness of the metric: `0 < vᵀ g(x) v` for `v ≠ 0`. -/
theorem form_pos (x : Fin n → ℝ) {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < dotProduct v (G.g x *ᵥ v) := by
  have hlower : 0 < G.lower * dotProduct v v :=
    mul_pos G.lower_pos (dotProduct_self_pos_of_ne_zero hv)
  exact lt_of_lt_of_le hlower (G.coercive x v)

/-- The metric matrix has nonzero determinant everywhere (positive definiteness). -/
theorem det_ne_zero (x : Fin n → ℝ) : (G.g x).det ≠ 0 := by
  intro hdet
  have hv := (Matrix.exists_mulVec_eq_zero_iff (M := G.g x)).mpr hdet
  rcases hv with ⟨v, hvne, hzero⟩
  have hpos : 0 < dotProduct v (G.g x *ᵥ v) := G.form_pos x hvne
  rw [hzero, dotProduct_zero] at hpos
  linarith

/-- The metric matrix is invertible everywhere. -/
theorem isUnit_det (x : Fin n → ℝ) : IsUnit (G.g x).det :=
  isUnit_iff_ne_zero.mpr (G.det_ne_zero x)

/-- The inverse metric is the transpose-inverse of the coefficient matrix (symmetry). -/
theorem inv_transpose (x : Fin n → ℝ) : ((G.g x)⁻¹)ᵀ = (G.g x)⁻¹ := by
  have h1 : G.g x * (G.g x)⁻¹ = 1 := Matrix.mul_nonsing_inv (G.g x) (G.isUnit_det x)
  have h1t : ((G.g x)⁻¹)ᵀ * (G.g x)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, h1]
    exact Matrix.transpose_one
  have h1t' : ((G.g x)⁻¹)ᵀ * G.g x = 1 := by
    simpa [G.symm x] using h1t
  calc
    ((G.g x)⁻¹)ᵀ = ((G.g x)⁻¹)ᵀ * 1 := by rw [mul_one]
    _ = ((G.g x)⁻¹)ᵀ * (G.g x * (G.g x)⁻¹) := by rw [h1]
    _ = (((G.g x)⁻¹)ᵀ * G.g x) * (G.g x)⁻¹ := by rw [mul_assoc]
    _ = 1 * (G.g x)⁻¹ := by rw [h1t']
    _ = (G.g x)⁻¹ := by rw [one_mul]

/-- **The flat metric** `g = 1` as an arbitrary smooth metric, with the explicit constants
`lower = 1/2`, `upper = 2`.  This is the non-vacuity witness: the flat instance on which the
D12 Gaussian heat semigroup is the linearized evolution family of the DeTurck operator. -/
def flatSmoothMetric (n : ℕ) : SmoothMetricData n where
  g := fun _ => 1
  symm := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.one_apply]
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [Matrix.one_apply, hij, hji]
  smooth := by
    simpa using (contDiff_const (c := (1 : Matrix (Fin n) (Fin n) ℝ)) :
      ContDiff ℝ 2 (fun _ : Fin n → ℝ => (1 : Matrix (Fin n) (Fin n) ℝ)))
  lower := 1 / 2
  lower_pos := by norm_num
  coercive := by
    intro x v
    simp only [Matrix.one_mulVec]
    nlinarith [dotProduct_self_nonneg v]
  upper := 2
  upper_pos := by norm_num
  boundedAbove := by
    intro x v
    simp only [Matrix.one_mulVec]
    nlinarith [dotProduct_self_nonneg v]

end SmoothMetricData

end

end DeturckProducer
end D13
end Poincare
