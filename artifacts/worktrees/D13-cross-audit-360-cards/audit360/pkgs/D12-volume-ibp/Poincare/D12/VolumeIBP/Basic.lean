/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Mathlib

/-!
# Riemannian density and measure from a positive-definite metric matrix (chart level)

This is the D12-volume-ibp measure/geometry bridge. Everything in this layer lives on a
**Euclidean chart domain**: the ambient space is `Vec d := Fin d → ℝ`, the standard chart model
of a `d`-dimensional Riemannian manifold (a chart is exactly an open subset of `Vec d`; here we
work on the whole `Vec d`, which is the largest chart, and all integration is over `ℝᵈ` with
Lebesgue measure `volume`).

A `ChartMetric` packages

* `g : Vec d → Fin d → Fin d → ℝ` — the metric matrix coefficients as functions on the chart
  (`g x i j` is the `(i,j)`-entry of the metric at `x`),
* `smooth : ∀ i j, ContDiff ℝ 2 (fun x => g x i j)` — every metric coefficient is `C²` on the
  chart (the honest chart-level smoothness of the metric tensor; the matrix-valued form is
  equivalent, see `Compat.lean`),
* `posDef : ∀ x, (Matrix.of (fun i j => g x i j)).PosDef` — the metric matrix is positive
  definite at every point (which over `ℝ` includes symmetry).

From this we construct

* the **Riemannian density** `density G x = sqrt ((Matrix.of ...).det)` (a genuine density:
  positive, and measurable/continuous when the metric is — see `Regularity.lean`),
* the **Riemannian measure** `riemannianMeasure G = volume.withDensity (density.toNNReal)`,
  i.e. `dvol = √(det g) dx`, built from the Lebesgue measure and the density, not assumed.

The metric pairing `inner G x v w = ∑ i j, v i * g x i j * w j` and the inverse-metric matrix
`invMatrix G x = (Matrix.of ...)⁻¹` complete the bridge data.

Global manifold statements (partition-of-unity gluing of chart densities, boundary measures,
Stokes) are **not** claimed here; they are recorded as state-only `Prop`s with named blockers
in `Blocked.lean`.

## What this is not

This is not a construction of the Riemannian volume measure on a global manifold: there is no
atlas, no transition-function consistency, and no gluing. It is the exact chart-level object
that such a construction must glue, and it carries the theorems (divergence, integration by
parts, change of variables) that the entropy/Bochner chain consumes on each chart.
-/

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D12.VolumeIBP

/-- The chart model vector space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- A Riemannian metric on the chart domain `Vec d`: smooth (`C^∞`) metric-matrix coefficients, positive
definite at every point. Positivity over `ℝ` implies symmetry of the matrix. Smoothness is
stated entrywise because the pinned mathlib has no global normed instance on `Matrix`. -/
structure ChartMetric (d : ℕ) where
  /-- metric coefficients: `g x i j` -/
  g : Vec d → Fin d → Fin d → ℝ
  /-- every metric coefficient is C² on the chart -/
  smooth : ∀ i j, ContDiff ℝ ⊤ (fun x : Vec d => g x i j)
  /-- positive definite at every point -/
  posDef : ∀ x, (Matrix.of (fun i j => g x i j) : Matrix (Fin d) (Fin d) ℝ).PosDef

namespace ChartMetric

variable {d : ℕ} (G : ChartMetric d)

/-- The metric matrix at a point. -/
def matrix (x : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => G.g x i j

@[simp] lemma matrix_apply (x : Vec d) (i j : Fin d) : G.matrix x i j = G.g x i j := rfl

/-- The metric is at least `C¹` (used for all derivative manipulations). -/
lemma smooth_one (i j : Fin d) : ContDiff ℝ 1 (fun x : Vec d => G.g x i j) :=
  (G.smooth i j).of_le le_top

/-- Symmetry of the metric coefficients (positive definiteness over `ℝ` forces symmetry). -/
lemma g_symm (x : Vec d) (i j : Fin d) : G.g x j i = G.g x i j := by
  have hh : (G.matrix x).IsHermitian := (G.posDef x).1
  have hh' : (G.matrix x).conjTranspose = G.matrix x := by
    simpa [Matrix.IsHermitian] using hh
  simpa [matrix, Matrix.conjTranspose] using congr_fun (congr_fun hh' i) j

/-- The metric matrix is symmetric. -/
lemma matrix_symm (x : Vec d) : (G.matrix x).IsSymm :=
  Matrix.IsSymm.ext fun i j => by simpa [matrix] using G.g_symm x i j

/-- The determinant of the metric matrix is positive at every point. -/
lemma det_pos (x : Vec d) : 0 < (G.matrix x).det :=
  Matrix.PosDef.det_pos (G.posDef x)

/-- The determinant of the metric matrix is nonzero at every point. -/
lemma det_ne_zero (x : Vec d) : (G.matrix x).det ≠ 0 :=
  ne_of_gt (G.det_pos x)

/-- The Riemannian density `√(det g)`. -/
def density (x : Vec d) : ℝ :=
  Real.sqrt (G.matrix x).det

/-- The density is positive. -/
lemma density_pos (x : Vec d) : 0 < G.density x :=
  Real.sqrt_pos.2 (G.det_pos x)

/-- The density is nonnegative. -/
lemma density_nonneg (x : Vec d) : 0 ≤ G.density x :=
  le_of_lt (G.density_pos x)

/-- The density never vanishes. -/
lemma density_ne_zero (x : Vec d) : G.density x ≠ 0 :=
  ne_of_gt (G.density_pos x)

/-- The metric pairing `⟨v, w⟩_g(x) = ∑ i j, v i * g x i j * w j`. -/
def inner (x : Vec d) (v w : Vec d) : ℝ :=
  ∑ i, ∑ j, v i * G.g x i j * w j

/-- The metric pairing is symmetric (positive definiteness over `ℝ` forces symmetry). -/
lemma inner_comm (x : Vec d) (v w : Vec d) : G.inner x v w = G.inner x w v := by
  unfold inner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (j : Fin d) _ => ?_
  refine Finset.sum_congr rfl fun (i : Fin d) _ => ?_
  rw [G.g_symm x i j]
  ring

/-- The metric pairing is positive on nonzero vectors. -/
lemma inner_pos_of_ne_zero (x : Vec d) {v : Vec d} (hv : v ≠ 0) : 0 < G.inner x v v := by
  unfold inner
  have hv' : Finsupp.equivFunOnFinite.symm v ≠ 0 := by
    intro h
    apply hv
    have h' := congrArg Finsupp.equivFunOnFinite h
    rw [Finsupp.equivFunOnFinite.apply_symm_apply] at h'
    simpa [Finsupp.equivFunOnFinite] using h'
  have hpd := (G.posDef x).2 hv'
  simpa [Finsupp.sum_fintype, dotProduct, matrix, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_comm, mul_left_comm] using hpd

/-- The inverse metric matrix `g(x)⁻¹` (defined entrywise through the adjugate/det formula). -/
def invMatrix (x : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  (G.matrix x)⁻¹

@[simp] lemma invMatrix_mul (x : Vec d) : G.invMatrix x * G.matrix x = 1 :=
  Matrix.nonsing_inv_mul (G.matrix x) ((isUnit_iff_ne_zero).mpr (G.det_ne_zero x))

@[simp] lemma matrix_mul_invMatrix (x : Vec d) : G.matrix x * G.invMatrix x = 1 :=
  Matrix.mul_nonsing_inv (G.matrix x) ((isUnit_iff_ne_zero).mpr (G.det_ne_zero x))

/-- The inverse matrix is symmetric. -/
lemma invMatrix_symm (x : Vec d) : (G.invMatrix x).IsSymm := by
  have htr : Matrix.transpose (G.invMatrix x) = G.invMatrix x := by
    rw [invMatrix, Matrix.transpose_nonsing_inv, matrix]
    congr 1
    ext k ℓ
    simpa [Matrix.of_apply] using (G.g_symm x ℓ k).symm
  exact htr

/-- The Riemannian measure `dvol = √(det g) dx` built from Lebesgue measure `volume`
and the density. -/
def riemannianMeasure : Measure (Vec d) :=
  MeasureTheory.volume.withDensity (fun x => (G.density x).toNNReal)

/-- The density as a function `Vec d → ℝ≥0`. -/
def densityNNReal (x : Vec d) : ℝ≥0 :=
  (G.density x).toNNReal

/-- The Riemannian measure is the Lebesgue measure with `ℝ≥0` density. -/
lemma riemannianMeasure_def :
    G.riemannianMeasure = MeasureTheory.volume.withDensity (fun x => (G.densityNNReal x : ℝ≥0∞)) :=
  rfl

/-- The standard Euclidean metric (identity matrix): a canonical inhabitant of `ChartMetric`. -/
def euclideanChartMetric (d : ℕ) : ChartMetric d where
  g := fun _ i j => if i = j then 1 else 0
  smooth := by
    intro i j
    simpa using (contDiff_const (𝕜 := ℝ) (E := Vec d) (F := ℝ) (n := ⊤)
      (c := (if i = j then 1 else 0 : ℝ)))
  posDef := fun x => by
    change (1 : Matrix (Fin d) (Fin d) ℝ).PosDef
    exact Matrix.PosDef.one

end ChartMetric

end Poincare.D12.VolumeIBP
