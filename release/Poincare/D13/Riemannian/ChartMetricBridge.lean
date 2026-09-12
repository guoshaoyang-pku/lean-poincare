/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (global smooth ChartMetric from a genuine metric)

# A global smooth `ChartMetric` from a genuine Riemannian chart

D12's chart layer is parametrised by a **global** `ChartMetric d`: coefficients that are
`C^⊤` on *all* of `Vec d = Fin d → ℝ` and positive definite there. At the release pin the top
of the smoothness order `ℕ∞ω` is `ω` (**analytic**): `⊤ = ω`, and `ContDiff ℝ ⊤` is
`ContDiff ℝ ω`. So D12's `ChartMetric.smooth` field asks for *analytic* coefficients, which a
genuine `C^∞` Riemannian metric does not provide. This module records that expanded hypothesis
and builds the honest smooth variant `SmoothChartMetric` from a genuine metric:

* `chartMetricCoeff` / `chartMetricCoeffExt` — the genuine chart Gram coefficient, extended by
  the identity matrix off the chart target;
* `contDiff_chartMetricCoeffExt_mul` — for a smooth bump `φ` with `tsupport φ` inside the chart
  target, `y ↦ φ y · G^α_{ij}(y)` is `C^∞` on all of `Vec d` (smoothness on the target,
  vanishing off the closed support, the two open sets covering `Vec d`);
* `posDef_chartMetricCoeffExt` — the extended coefficient matrix is positive definite
  everywhere (genuine Gram matrix on the target, identity off it, by `chartGramMatrix_posDef`);
* **`extendedSmoothChartMetric`** — the convex combination `φ • G^α + (1 - φ) • 1` is a global
  `SmoothChartMetric d`, i.e. the chart layer of D12 is *inhabited by genuine Riemannian data*
  once its coefficient regularity is read as `C^∞`;
* `extendedSmoothChartMetric_g_eq_genuine` — where `φ = 1` it *is* the genuine chart Gram
  matrix: the extension adds no content on the region it is built for.

The remaining, genuinely global step — one extension per chart whose pairwise tensor law holds
*everywhere*, so that the abstract `OverlapAtlas` can be inhabited literally — is not claimed
here and is recorded as the residual blocker.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.Riemannian.MetricBridgeSmooth
import Poincare.D13.Riemannian.AtlasBridge
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Bundle Set
open scoped Manifold ContDiff Topology Bundle Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.D13.Riemannian

open Poincare.D12.VolumeIBP
open Poincare.D13.ManifoldIBP

variable {d : ℕ} [NeZero (Module.finrank ℝ (Vec d))]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Vec d) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ (Vec d) (TangentSpace I : M → Type _)]

/-! ## The genuine chart coefficient and its junk extension -/

/-- The genuine chart Gram coefficient, read in the coordinates of the chart at `α`. -/
def chartMetricCoeff (α : M) (y : Vec d) (i j : Fin d) : ℝ :=
  (chartMetricMatrix (I := I) α y) i j

/-- The genuine chart Gram coefficient, extended by the identity matrix off the chart target. -/
def chartMetricCoeffExt (α : M) (y : Vec d) (i j : Fin d) : ℝ := by
  classical
  exact if y ∈ (extChartAt I α).target then chartMetricCoeff (I := I) α y i j
    else if i = j then 1 else 0

lemma chartMetricCoeffExt_eq (α : M) {y : Vec d} (hy : y ∈ (extChartAt I α).target)
    (i j : Fin d) :
    chartMetricCoeffExt (I := I) α y i j = chartMetricCoeff (I := I) α y i j := by
  classical
  simp only [chartMetricCoeffExt, hy, ite_true]

/-- On the chart target the genuine chart coefficient is `C^∞` (in coordinates). -/
lemma contDiffOn_chartMetricCoeff (α : M) (i j : Fin d) :
    ContDiffOn ℝ ∞ (fun y => chartMetricCoeff (I := I) α y i j)
      (extChartAt I α).target :=
  contDiffOn_chartGramMatrix_coord (I := I) (Pi.basisFun ℝ (Fin d)) α i j

/-- **The bump-multiplied genuine coefficient is `C^∞` on all of `Vec d`.** On the chart target
it is the product of two smooth functions; off the (closed) support of the bump it vanishes;
the two open sets cover `Vec d`. -/
lemma contDiff_chartMetricCoeffExt_mul (α : M) {φ : Vec d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target) (i j : Fin d) :
    ContDiff ℝ ∞ (fun y => φ y * chartMetricCoeffExt (I := I) α y i j) := by
  refine contDiff_of_contDiffOn_union_of_isOpen ?_ ?_ ?_
    (isOpen_extChartAt_target (I := I) α) (isClosed_tsupport φ).isOpen_compl
  · refine hφ.contDiffOn.mul ?_
    exact (contDiffOn_chartMetricCoeff (I := I) α i j).congr (fun y hy =>
      chartMetricCoeffExt_eq (I := I) α hy i j)
  · intro y hy
    have hφ0 : φ =ᶠ[𝓝 y] 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hy] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hprod : (fun z => φ z * chartMetricCoeffExt (I := I) α z i j) =ᶠ[𝓝 y]
        fun _ => (0 : ℝ) := by
      filter_upwards [hφ0] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hprod).contDiffWithinAt
  · rw [eq_univ_iff_forall]
    intro y
    by_cases hy : y ∈ tsupport φ
    · exact Or.inl (hsupp hy)
    · exact Or.inr hy

/-! ## Positive definiteness -/

/-- The extended coefficient matrix is positive definite everywhere: the genuine Gram matrix
(positive definite by `chartGramMatrix_posDef`) on the chart target, the identity off it. -/
lemma posDef_chartMetricCoeffExt (α : M) (y : Vec d) :
    (Matrix.of (chartMetricCoeffExt (I := I) α y)).PosDef := by
  by_cases hy : y ∈ (extChartAt I α).target
  · have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    have h := chartGramMatrix_posDef (I := I) (B := Pi.basisFun ℝ (Fin d)) α hx
    convert h using 1
    ext i j
    simp only [Matrix.of_apply, chartMetricCoeffExt, hy, ite_true, chartMetricCoeff,
      chartMetricMatrix]
  · classical
    rw [show Matrix.of (chartMetricCoeffExt (I := I) α y) = 1 by
      ext i j
      unfold chartMetricCoeffExt
      simp only [hy, ite_false, Matrix.of_apply, Matrix.one_apply]]
    exact Matrix.PosDef.one

/-! ## The global smooth chart metric -/

/-- **The D12 `ChartMetric` interface with `C^∞` coefficients.** At the release pin the top of
`ℕ∞ω` is `ω` (analytic), so D12's `ChartMetric.smooth : ContDiff ℝ ⊤` asks for analytic
coefficients; this variant records the honest regularity of a `C^∞` Riemannian metric. -/
structure SmoothChartMetric (d : ℕ) where
  /-- metric coefficients: `g x i j` -/
  g : Vec d → Fin d → Fin d → ℝ
  /-- every metric coefficient is `C^∞` on the chart -/
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x : Vec d => g x i j)
  /-- positive definite at every point -/
  posDef : ∀ x, (Matrix.of (fun i j => g x i j) : Matrix (Fin d) (Fin d) ℝ).PosDef

/-- **A global smooth chart metric from a genuine Riemannian chart.** For a smooth bump `φ` with
values in `[0,1]` and closed support inside the chart target, the convex combination
`φ • G^α + (1 - φ) • 1` has `C^∞` coefficients and is positive definite on all of `Vec d`. -/
def extendedSmoothChartMetric (α : M) (φ : Vec d → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ 1)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target) : SmoothChartMetric d where
  g y i j := φ y * chartMetricCoeffExt (I := I) α y i j
    + (1 - φ y) * (if i = j then 1 else 0)
  smooth i j := by
    have hmain := contDiff_chartMetricCoeffExt_mul (I := I) α hφ hsupp i j
    have hdelta : ContDiff ℝ ∞
        (fun y : Vec d => (1 - φ y) * (if i = j then (1 : ℝ) else 0)) :=
      ((contDiff_const (c := (1 : ℝ))).sub hφ).mul
        (contDiff_const (c := (if i = j then (1 : ℝ) else 0)))
    exact hmain.add hdelta
  posDef y := by
    by_cases hφy : φ y = 0
    · rw [show Matrix.of (fun i j => φ y * chartMetricCoeffExt (I := I) α y i j
          + (1 - φ y) * (if i = j then 1 else 0)) = 1 by
        ext i j
        rw [hφy]
        simp only [Matrix.of_apply, Matrix.one_apply]
        ring]
      exact Matrix.PosDef.one
    · have hpos : 0 < φ y := lt_of_le_of_ne (h0 y) (Ne.symm hφy)
      have hG : (Matrix.of (chartMetricCoeffExt (I := I) α y)).PosDef :=
        posDef_chartMetricCoeffExt (I := I) α y
      have hI : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := Matrix.PosDef.one
      have hsum := (hG.smul hpos).add_posSemidef
        (hI.posSemidef.smul (sub_nonneg.mpr (h1 y)))
      convert hsum using 1
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply,
        smul_eq_mul]

/-- Where the bump equals `1`, the extended chart metric **is** the genuine chart Gram
matrix: the extension adds no content on the region it is built for. -/
theorem extendedSmoothChartMetric_g_eq_genuine (α : M) (φ : Vec d → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ 1)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target) {y : Vec d} (hy : φ y = 1)
    (i j : Fin d) :
    (extendedSmoothChartMetric (I := I) α φ hφ h0 h1 hsupp).g y i j
      = chartMetricCoeff (I := I) α y i j := by
  have hymem : y ∈ (extChartAt I α).target :=
    hsupp (subset_tsupport φ (by simp [Function.mem_support, hy]))
  simp only [extendedSmoothChartMetric, hy, one_mul, sub_self, zero_mul, add_zero,
    chartMetricCoeffExt_eq (I := I) α hymem i j]

/-! ## The analytic variant: inhabiting D12's `ChartMetric` itself -/

/-- **The bump-multiplied genuine coefficient is analytic** when the coefficient is: the same
open-cover argument as `contDiff_chartMetricCoeffExt_mul`, at `⊤ = ω` (analytic at this pin). -/
lemma contDiff_chartMetricCoeffExt_mul_top (α : M) {φ : Vec d → ℝ} (hφ : ContDiff ℝ ⊤ φ)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target)
    (hcoeff : ∀ i j, ContDiffOn ℝ ⊤ (fun y => chartMetricCoeff (I := I) α y i j)
      (extChartAt I α).target) (i j : Fin d) :
    ContDiff ℝ ⊤ (fun y => φ y * chartMetricCoeffExt (I := I) α y i j) := by
  refine contDiff_of_contDiffOn_union_of_isOpen ?_ ?_ ?_
    (isOpen_extChartAt_target (I := I) α) (isClosed_tsupport φ).isOpen_compl
  · refine hφ.contDiffOn.mul ?_
    exact (hcoeff i j).congr (fun y hy => chartMetricCoeffExt_eq (I := I) α hy i j)
  · intro y hy
    have hφ0 : φ =ᶠ[𝓝 y] 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hy] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hprod : (fun z => φ z * chartMetricCoeffExt (I := I) α z i j) =ᶠ[𝓝 y]
        fun _ => (0 : ℝ) := by
      filter_upwards [hφ0] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
    exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hprod).contDiffWithinAt
  · rw [eq_univ_iff_forall]
    intro y
    by_cases hy : y ∈ tsupport φ
    · exact Or.inl (hsupp hy)
    · exact Or.inr hy

/-- **A global D12 `ChartMetric` from an analytic Riemannian chart.** D12's `ChartMetric.smooth`
field is `ContDiff ℝ ⊤`, i.e. *analytic* at this pin; under that regularity of the genuine chart
coefficient, the bump convex combination `φ • G^α + (1 - φ) • 1` inhabits `ChartMetric d`
itself, so the D12 chart layer is inhabited by genuine Riemannian data in the analytic case. -/
def extendedChartMetric (α : M) (φ : Vec d → ℝ) (hφ : ContDiff ℝ ⊤ φ)
    (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ 1)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target)
    (hcoeff : ∀ i j, ContDiffOn ℝ ⊤ (fun y => chartMetricCoeff (I := I) α y i j)
      (extChartAt I α).target) : ChartMetric d where
  g y i j := φ y * chartMetricCoeffExt (I := I) α y i j
    + (1 - φ y) * (if i = j then 1 else 0)
  smooth i j := by
    have hmain := contDiff_chartMetricCoeffExt_mul_top (I := I) α hφ hsupp hcoeff i j
    have hdelta : ContDiff ℝ ⊤
        (fun y : Vec d => (1 - φ y) * (if i = j then (1 : ℝ) else 0)) :=
      ((contDiff_const (c := (1 : ℝ))).sub hφ).mul
        (contDiff_const (c := (if i = j then (1 : ℝ) else 0)))
    exact hmain.add hdelta
  posDef y := by
    by_cases hφy : φ y = 0
    · rw [show Matrix.of (fun i j => φ y * chartMetricCoeffExt (I := I) α y i j
          + (1 - φ y) * (if i = j then 1 else 0)) = 1 by
        ext i j
        rw [hφy]
        simp only [Matrix.of_apply, Matrix.one_apply]
        ring]
      exact Matrix.PosDef.one
    · have hpos : 0 < φ y := lt_of_le_of_ne (h0 y) (Ne.symm hφy)
      have hG : (Matrix.of (chartMetricCoeffExt (I := I) α y)).PosDef :=
        posDef_chartMetricCoeffExt (I := I) α y
      have hI : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef := Matrix.PosDef.one
      have hsum := (hG.smul hpos).add_posSemidef
        (hI.posSemidef.smul (sub_nonneg.mpr (h1 y)))
      convert hsum using 1
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply,
        smul_eq_mul]


/-- Where the bump equals `1`, the D12-valued extension **is** the genuine chart Gram matrix. -/
theorem extendedChartMetric_g_eq_genuine (α : M) (φ : Vec d → ℝ) (hφ : ContDiff ℝ ⊤ φ)
    (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ 1)
    (hsupp : tsupport φ ⊆ (extChartAt I α).target)
    (hcoeff : ∀ i j, ContDiffOn ℝ ⊤ (fun y => chartMetricCoeff (I := I) α y i j)
      (extChartAt I α).target) {y : Vec d} (hy : φ y = 1) (i j : Fin d) :
    (extendedChartMetric (I := I) α φ hφ h0 h1 hsupp hcoeff).g y i j
      = chartMetricCoeff (I := I) α y i j := by
  have hymem : y ∈ (extChartAt I α).target :=
    hsupp (subset_tsupport φ (by simp [Function.mem_support, hy]))
  simp only [extendedChartMetric, hy, one_mul, sub_self, zero_mul, add_zero,
    chartMetricCoeffExt_eq (I := I) α hymem i j]


end Poincare.D13.Riemannian

/-! ## Axiom audit -/

#print axioms Poincare.D13.Riemannian.contDiff_chartMetricCoeffExt_mul
#print axioms Poincare.D13.Riemannian.posDef_chartMetricCoeffExt
#print axioms Poincare.D13.Riemannian.extendedSmoothChartMetric
#print axioms Poincare.D13.Riemannian.extendedSmoothChartMetric_g_eq_genuine
#print axioms Poincare.D13.Riemannian.contDiff_chartMetricCoeffExt_mul_top
#print axioms Poincare.D13.Riemannian.extendedChartMetric
#print axioms Poincare.D13.Riemannian.extendedChartMetric_g_eq_genuine
