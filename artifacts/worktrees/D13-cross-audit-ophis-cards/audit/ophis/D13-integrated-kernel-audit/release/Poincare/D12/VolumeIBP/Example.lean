/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.ChangeOfVariables

/-!
# Concrete witnesses: non-vacuity of the measure/geometry bridge

1. `euclideanChartMetric_density_one`: the Euclidean chart metric has density `1`, so
   `dvol = dx` — the bridge reproduces Lebesgue measure in the flat case.

2. `expMetricOne`: on the one-dimensional chart `Vec 1 ≅ ℝ` the metric `g(x) = e^{2x₀}`
   (positive definite, smooth) has density `e^{x₀}` — a **concrete nonconstant density**
   witness (`expMetricOne_density_eq`), so the construction is not vacuous and does not
   collapse to the Euclidean case: `∃ x, density ≠ 1` is proved.

3. `chart_ibp_euclidean_one`: the chart integration-by-parts identity instantiated in
   dimension 1 with the Euclidean metric — the exact hypothesis shape the entropy/Bochner
   chains consume, shown inhabited (any `C²` pair with compactly supported first entry).
-/

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D12.VolumeIBP

namespace ChartMetric

/-- The Euclidean chart metric has constant density `1`: `√(det 1) = 1`. -/
lemma euclideanChartMetric_density_one {d : ℕ} (x : Vec d) :
    (euclideanChartMetric d).density x = 1 := by
  rw [density, matrix, show (Matrix.of (fun i j => (euclideanChartMetric d).g x i j) : Matrix (Fin d) (Fin d) ℝ) = 1 by
    ext i j
    simp [euclideanChartMetric, Matrix.one_apply]]
  rw [Matrix.det_one, Real.sqrt_one]

/-- The one-dimensional metric `g(x) = e^{2x₀}`: smooth, positive definite (the only entry
`e^{2x₀} > 0`). -/
def expMetricOne : ChartMetric 1 where
  g := fun x _ _ => Real.exp (2 * x 0)
  smooth := by
    intro i j
    change ContDiff ℝ ⊤ (fun x : Vec 1 => Real.exp (2 * x 0))
    refine ContDiff.exp ?_
    refine ContDiff.mul ?_ ?_
    · exact contDiff_const
    · exact (ContinuousLinearMap.proj 0 : Vec 1 →L[ℝ] ℝ).contDiff
  posDef := fun p => by
    refine ⟨?_, ?_⟩
    · exact Matrix.ext fun i j => by simp [Matrix.conjTranspose]
    · intro x hx
      have hx0 : x 0 ≠ 0 := by
        intro h
        exact hx (Finsupp.ext (fun i => by
          fin_cases i
          exact h))
      have hsum : x.sum (fun i xi => x.sum (fun j xj => star xi *
            (Matrix.of (fun i j => Real.exp (2 * p 0)) : Matrix (Fin 1) (Fin 1) ℝ) i j * xj))
          = x 0 * Real.exp (2 * p 0) * x 0 := by
        rw [Finsupp.sum_fintype (f := x)
          (g := fun i xi => x.sum (fun j xj => star xi *
            (Matrix.of (fun i j => Real.exp (2 * p 0)) : Matrix (Fin 1) (Fin 1) ℝ) i j * xj))
          (by intro i; simp)]
        rw [Finset.sum_eq_single (0 : Fin 1)]
        · rw [Finsupp.sum_fintype (f := x)
            (g := fun j xj => star (x 0) *
              (Matrix.of (fun i j => Real.exp (2 * p 0)) : Matrix (Fin 1) (Fin 1) ℝ) 0 j * xj)
            (by intro j; simp)]
          rw [Finset.sum_eq_single (0 : Fin 1)]
          · simp [Matrix.of_apply, star_trivial]
          · intro b _ hb
            fin_cases b
            exact (hb rfl).elim
          · intro h
            exact (h (Finset.mem_univ (0 : Fin 1))).elim
        · intro b _ hb
          fin_cases b
          exact (hb rfl).elim
        · intro h
          exact (h (Finset.mem_univ (0 : Fin 1))).elim
      have hpos : 0 < x 0 * Real.exp (2 * p 0) * x 0 := by
        have hx02 : 0 < x 0 * x 0 := by simpa [sq] using sq_pos_of_ne_zero hx0
        nlinarith [hx02, Real.exp_pos (2 * p 0)]
      rw [hsum]
      exact hpos

/-- The density of `expMetricOne` is `e^{x₀}` — a concrete nonconstant Riemannian density. -/
lemma expMetricOne_density_eq (x : Vec 1) :
    expMetricOne.density x = Real.exp (x 0) := by
  rw [density, matrix]
  change Real.sqrt ((Matrix.of (fun i j => Real.exp (2 * x 0)) : Matrix (Fin 1) (Fin 1) ℝ).det)
    = Real.exp (x 0)
  rw [Matrix.det_fin_one]
  rw [Matrix.of_apply]
  rw [show Real.exp (2 * x 0) = (Real.exp (x 0)) ^ 2 by
    rw [two_mul]
    rw [Real.exp_add]
    ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_pos (x 0)).le]

/-- Non-vacuity: the bridge has a witness whose density is not the constant `1`. -/
example : ∃ x : Vec 1, expMetricOne.density x ≠ 1 := by
  refine ⟨fun _ => 1, ?_⟩
  rw [expMetricOne_density_eq]
  exact (Real.one_lt_exp_iff.mpr (by norm_num)).ne'

/-- The chart integration-by-parts identity in dimension 1 with the Euclidean metric — the
exact shape consumed by the entropy/Bochner chains (any `C² u, v` with `u` compactly
supported; non-vacuity of the hypotheses is witnessed by `expMetricOne` for the metric side
and by the classical existence of smooth bump functions for the function side). -/
theorem chart_ibp_euclidean_one (u v : Vec 1 → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) :
    ∫ x, u x * (euclideanChartMetric 1).laplacian v x * (euclideanChartMetric 1).density x
      = -∫ x, (euclideanChartMetric 1).gradInnerInverse u v x * (euclideanChartMetric 1).density x :=
  chart_ibp (euclideanChartMetric 1) u v hu hv huc

end ChartMetric

end Poincare.D12.VolumeIBP
