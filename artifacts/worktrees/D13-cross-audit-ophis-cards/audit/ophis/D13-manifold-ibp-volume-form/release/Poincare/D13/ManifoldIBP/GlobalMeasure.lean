/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (overlapping-atlas global measure)

# The global Riemannian measure of an overlapping atlas (release mathlib pin)

`ManifoldIBP.DisjointModel` constructed the manifold measure for an atlas whose charts have
**disjoint** images. The genuinely open part of blocker `B-D13-MANIFOLD-GLUING` /
`U7-global` is the case of charts that **overlap**: there the chart measures must agree on
overlaps, which is the classical well-definedness of `√(det gᵢⱼ) dx¹ ⋯ dxⁿ` and rests on the
`(0,2)`-tensor transformation law of the metric together with mathlib's change-of-variables
formula for the transition map.

This module ports the mathematical content of the upstream Frenzymath development
(`third_party/frenzymath/Poincare-Conjecture @ bb91a091`, file
`formalized-sources/MorganTian/MorganTianLib/Ch01/RiemannianMeasure.lean`) from the upstream
manifold/tangent-bundle layer (Lean v4.32.1 / mathlib `520045ab`) to the release pin
(Lean 4.34.0-rc2, mathlib `7974e751be`), in the local explicit-chart framework of
`Poincare.D12.VolumeIBP`:

* `OverlapAtlas M d` — a countable atlas of partial charts `chartᵢ : Vec d → M` on open
  sources, each carrying a D12 `ChartMetric`, together with transition maps
  `transition i j` between overlapping charts and the **tensor transformation law**
  `(metric j).matrix y = Jᵀ · (metric i).matrix (transition i j y) · J`, where `J` is the
  Jacobian matrix of the transition. This law is the honest hypothesis that the charts
  describe one and the same Riemannian metric; the analytic content below (the Jacobian
  cancellation in the change-of-variables formula) is *proved* from it;
* `density_transform` — the density form `ρ_j(y) = ρ_i(τ y) · |det J(y)|` of the law,
  proved by determinant algebra (`Matrix.det_mul`, `LinearMap.det_toMatrix`);
* `chartMeasure` / `chartMeasure_apply` — the chart measure and its defining density
  formula;
* **`chartMeasure_apply_eq`** — well-definedness: two charts assign the same measure to a
  measurable set contained in both chart images. The proof is the change of variables
  `τ = chartᵢ⁻¹ ∘ chartⱼ` via `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, whose
  Jacobian factor `|det (fderiv τ)|` cancels the Gram-determinant transformation law;
* `globalMeasure` — the global measure glued from a countable atlas by disjointifying the
  chart images (`Measure.sum` over `disjointed`), and **`globalMeasure_apply_chart`**: it is
  computed by the density formula in *every* chart. This is the interface theorem behind
  every global volume statement; the gluing choices are invisible through it;
* `globalMeasure_smul` — no normalization is hidden in the definition;
* `globalMeasure_eq_chartMeasure_of_cover` — a chart covering the whole manifold computes
  the global measure.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D12.VolumeIBP.ChangeOfVariables

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M]

/-! ## The overlapping atlas -/

/-- **The overlap of two charts**, as a set of *coordinates of the `j`-chart*: the points of
the `j`-source whose image under `chart j` lies in the image of the `i`-chart. This is the
domain on which the transition `i j` is defined. -/
def overlapOf {d : ℕ} (chart : ℕ → Vec d → M) (source : ℕ → Set (Vec d)) (i j : ℕ) :
    Set (Vec d) :=
  source j ∩ chart j ⁻¹' (chart i '' source i)

/-- **The Jacobian matrix of a map on a set**, in the standard basis of `Vec d`: the matrix
of `fderivWithin ℝ ψ s y`. -/
def jacobianOf {d : ℕ} (ψ : Vec d → Vec d) (s : Set (Vec d)) (y : Vec d) :
    Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
    (fderivWithin ℝ ψ s y).toLinearMap

/-- **An overlapping chart atlas with a Riemannian metric.** The manifold `M` is covered by
the images of countably many partial charts `chart i : Vec d → M` (open sources, injective,
measurable), each carrying a D12 chart metric, and the charts are related on overlaps by
transition maps satisfying the `(0,2)`-tensor transformation law. -/
structure OverlapAtlas (M : Type*) [MeasurableSpace M] (d : ℕ) where
  /-- the chart maps -/
  chart : ℕ → Vec d → M
  /-- the coordinate sources of the charts -/
  source : ℕ → Set (Vec d)
  /-- sources are open -/
  isOpen_source : ∀ i, IsOpen (source i)
  /-- chart maps are measurable (a genuine chart is measurable on its source and can be
  extended measurably outside it) -/
  measurable_chart : ∀ i, Measurable (chart i)
  /-- chart maps are injective on their sources -/
  injOn_chart : ∀ i, InjOn (chart i) (source i)
  /-- the chart images cover the manifold -/
  cover : (⋃ i, chart i '' source i) = univ
  /-- chart images are measurable (they are open for genuine charts) -/
  measurableSet_image : ∀ i, MeasurableSet (chart i '' source i)
  /-- the chart metric -/
  metric : ℕ → ChartMetric d
  /-- the transition maps, in `j`-coordinates to `i`-coordinates -/
  transition : ℕ → ℕ → Vec d → Vec d
  /-- the transition lands in the `i`-source -/
  transition_mem : ∀ i j y, y ∈ overlapOf chart source i j → transition i j y ∈ source i
  /-- the transition inverts `chart j` into `chart i` -/
  transition_chart : ∀ i j y, y ∈ overlapOf chart source i j →
    chart i (transition i j y) = chart j y
  /-- the transition is differentiable within the overlap -/
  transition_diff : ∀ i j y, y ∈ overlapOf chart source i j →
    DifferentiableWithinAt ℝ (transition i j) (overlapOf chart source i j) y
  /-- **the `(0,2)`-tensor transformation law**: on the overlap, the `j`-chart Gram matrix
  is the congruence of the `i`-chart Gram matrix by the transition Jacobian. This is the
  hypothesis that the two charts describe the same Riemannian metric. -/
  metric_transform : ∀ i j y (hy : y ∈ overlapOf chart source i j),
    (metric j).matrix y =
      (jacobianOf (transition i j) (overlapOf chart source i j) y)ᵀ
        * (metric i).matrix (transition i j y)
        * jacobianOf (transition i j) (overlapOf chart source i j) y

namespace OverlapAtlas

variable {d : ℕ} (A : OverlapAtlas M d)

/-! ## The density transformation law -/

/-- The matrix of a linear map on a set has the same determinant as the continuous linear
map, by mathlib's `LinearMap.det_toMatrix` bridge. -/
lemma det_jacobianOf (ψ : Vec d → Vec d) (s : Set (Vec d)) (y : Vec d) :
    (jacobianOf ψ s y).det = (fderivWithin ℝ ψ s y).det := by
  rw [jacobianOf]
  exact LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d)) _

/-- **The determinant transformation law**: `det g_j(y) = (det J)² · det g_i(τ y)`. Pure
matrix algebra (`Matrix.det_mul`, `Matrix.det_transpose`) plus the matrix/CLM determinant
bridge. -/
theorem det_matrix_transform (i j : ℕ) (y : Vec d) (hy : y ∈ overlapOf A.chart A.source i j) :
    ((A.metric j).matrix y).det
      = ((fderivWithin ℝ (A.transition i j) (overlapOf A.chart A.source i j) y).det) ^ 2
          * ((A.metric i).matrix (A.transition i j y)).det := by
  rw [A.metric_transform i j y hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_jacobianOf]
  ring

/-- The `i`-chart Riemannian density `ρ_i(y) = √(det g_i(y))`. -/
def density (i : ℕ) (y : Vec d) : ℝ :=
  (A.metric i).density y

lemma density_nonneg (i : ℕ) (y : Vec d) : 0 ≤ A.density i y :=
  (A.metric i).density_nonneg y

lemma density_pos (i : ℕ) (y : Vec d) : 0 < A.density i y :=
  (A.metric i).density_pos y

/-- **The density transformation law**: `ρ_j(y) = ρ_i(τ y) · |det J(y)|` — the Riemannian
density transforms by the absolute Jacobian determinant under a chart transition. This is
exactly the factor produced by mathlib's change-of-variables formula, so the two cancel in
`chartMeasure_apply_eq`. -/
theorem density_transform (i j : ℕ) (y : Vec d)
    (hy : y ∈ overlapOf A.chart A.source i j) :
    A.density j y
      = A.density i (A.transition i j y)
          * |(fderivWithin ℝ (A.transition i j) (overlapOf A.chart A.source i j) y).det| := by
  rw [density, density, ChartMetric.density, ChartMetric.density,
    A.det_matrix_transform i j y hy, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  ring

/-! ## The chart measure and its defining formula -/

/-- **The coordinate image of `s` in the `i`-chart**, written as a preimage so that its
measurability is immediate: `{y ∈ source i | chart i y ∈ s}`. -/
def chartPreimage (i : ℕ) (s : Set M) : Set (Vec d) :=
  A.source i ∩ A.chart i ⁻¹' s

lemma chartPreimage_subset_source (i : ℕ) (s : Set M) :
    A.chartPreimage i s ⊆ A.source i :=
  inter_subset_left

lemma chartPreimage_subset_overlap {i j : ℕ} {s : Set M}
    (hs : s ⊆ A.chart i '' A.source i) :
    A.chartPreimage j s ⊆ overlapOf A.chart A.source i j :=
  fun _ hy => ⟨hy.1, hs hy.2⟩

lemma measurableSet_chartPreimage (i : ℕ) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (A.chartPreimage i s) :=
  (A.isOpen_source i).measurableSet.inter ((A.measurable_chart i) hs)

/-- **The Riemannian measure read in the `i`-chart**: push the density `ρ_i · μ` forward
from the chart source to `M`. -/
def chartMeasure (μ : Measure (Vec d)) (i : ℕ) : Measure M :=
  Measure.map (A.chart i)
    ((μ.restrict (A.source i)).withDensity (fun y => ENNReal.ofReal (A.density i y)))

/-- **The defining formula**: the `i`-chart measure of a measurable set is the integral of
the density `ρ_i` over its coordinate image. -/
theorem chartMeasure_apply (μ : Measure (Vec d)) (i : ℕ) {s : Set M}
    (hs : MeasurableSet s) :
    A.chartMeasure μ i s
      = ∫⁻ y in A.chartPreimage i s, ENNReal.ofReal (A.density i y) ∂μ := by
  have hae : AEMeasurable (A.chart i) (μ.restrict (A.source i)) :=
    (A.measurable_chart i).aemeasurable
  have hae' : AEMeasurable (A.chart i)
      ((μ.restrict (A.source i)).withDensity
        (fun y => ENNReal.ofReal (A.density i y))) :=
    hae.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre : MeasurableSet (A.chart i ⁻¹' s) := (A.measurable_chart i) hs
  have hsrc : MeasurableSet (A.source i) := (A.isOpen_source i).measurableSet
  rw [chartMeasure, Measure.map_apply_of_aemeasurable hae' hs,
    MeasureTheory.withDensity_apply _ hpre, chartPreimage,
    Measure.restrict_restrict' hsrc, inter_comm]

/-! ## Chart-independence: the Riemannian measure is well defined -/

/-- **Well-definedness of the Riemannian measure.** Two charts assign the same measure to a
measurable set contained in both chart images.

The proof is the change of variables `τ = chartᵢ⁻¹ ∘ chartⱼ` on the coordinate overlap.
Mathlib's formula contributes the factor `|det (fderiv τ)|`; the Gram-determinant
transformation law contributes exactly the same factor and the two cancel. -/
theorem chartMeasure_apply_eq (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (i j : ℕ) {s : Set M}
    (hs : MeasurableSet s) (hsi : s ⊆ A.chart i '' A.source i)
    (hsj : s ⊆ A.chart j '' A.source j) :
    A.chartMeasure μ i s = A.chartMeasure μ j s := by
  classical
  rw [A.chartMeasure_apply μ i hs, A.chartMeasure_apply μ j hs]
  have hmem : ∀ y ∈ A.chartPreimage j s,
      A.chart j y ∈ s ∧ y ∈ A.source j := fun _ hy => ⟨hy.2, hy.1⟩
  have hover : ∀ y ∈ A.chartPreimage j s, y ∈ overlapOf A.chart A.source i j :=
    fun _ hy => A.chartPreimage_subset_overlap hsi hy
  -- the transition carries the `j`-coordinate image onto the `i`-coordinate image
  have himg : A.transition i j '' A.chartPreimage j s = A.chartPreimage i s := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨A.transition_mem i j y (hover y hy), ?_⟩
      show A.chart i (A.transition i j y) ∈ s
      rw [A.transition_chart i j y (hover y hy)]
      exact (hmem y hy).1
    · intro z hz
      obtain ⟨hzsrc, hzs⟩ := hz
      obtain ⟨y, hysrc, hyeq⟩ := hsj hzs
      have hyS : y ∈ A.chartPreimage j s := ⟨hysrc, by show A.chart j y ∈ s; rw [hyeq]; exact hzs⟩
      refine ⟨y, hyS, ?_⟩
      apply A.injOn_chart i (A.transition_mem i j y (hover y hyS)) hzsrc
      rw [A.transition_chart i j y (hover y hyS)]
      exact hyeq
  -- the transition is injective there
  have hinj : InjOn (A.transition i j) (A.chartPreimage j s) := by
    intro y₁ hy₁ y₂ hy₂ hEq
    have h₁ := hmem y₁ hy₁
    have h₂ := hmem y₂ hy₂
    have hchart : A.chart j y₁ = A.chart j y₂ := by
      rw [← A.transition_chart i j y₁ (hover y₁ hy₁),
        ← A.transition_chart i j y₂ (hover y₂ hy₂), hEq]
    exact A.injOn_chart j h₁.2 h₂.2 hchart
  -- its derivative is the transition Jacobian
  have hderiv : ∀ y ∈ A.chartPreimage j s,
      HasFDerivWithinAt (A.transition i j)
        (fderivWithin ℝ (A.transition i j) (overlapOf A.chart A.source i j) y)
        (A.chartPreimage j s) y := by
    intro y hy
    exact ((A.transition_diff i j y (hover y hy)).hasFDerivWithinAt).mono
      (fun z hz => hover z hz)
  rw [← himg,
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul μ
      (A.measurableSet_chartPreimage j hs) hderiv hinj
      (fun z => ENNReal.ofReal (A.density i z))]
  refine setLIntegral_congr_fun (A.measurableSet_chartPreimage j hs) ?_
  intro y hy
  show ENNReal.ofReal
        |(fderivWithin ℝ (A.transition i j) (overlapOf A.chart A.source i j) y).det|
      * ENNReal.ofReal (A.density i (A.transition i j y)) = ENNReal.ofReal (A.density j y)
  rw [mul_comm, ← ENNReal.ofReal_mul (A.density_nonneg i (A.transition i j y)),
    ← A.density_transform i j y (hover y hy)]

/-! ## The global Riemannian measure -/

/-- The disjointification of the chart images: a measurable partition of `M` whose `n`-th
piece lies inside the `n`-th chart image. -/
def chartPiece (n : ℕ) : Set M :=
  disjointed (fun k => A.chart k '' A.source k) n

lemma chartPiece_subset (n : ℕ) : A.chartPiece n ⊆ A.chart n '' A.source n :=
  disjointed_le _ n

lemma measurableSet_chartPiece (n : ℕ) : MeasurableSet (A.chartPiece n) :=
  MeasurableSet.disjointed (fun k => A.measurableSet_image k) n

lemma pairwiseDisjoint_chartPiece : Pairwise (Disjoint on A.chartPiece) :=
  disjoint_disjointed _

lemma iUnion_chartPiece : (⋃ n, A.chartPiece n) = univ :=
  (iUnion_disjointed (f := fun k => A.chart k '' A.source k)).trans A.cover

/-- **The global Riemannian volume measure** `μ_g`: glue the chart measures along a
countable atlas, cutting each chart down to its piece of a measurable partition of `M`. -/
def globalMeasure (μ : Measure (Vec d)) : Measure M :=
  Measure.sum fun n => (A.chartMeasure μ n).restrict (A.chartPiece n)

/-- **The interface theorem**: the global Riemannian measure of a measurable set contained
in *any* chart image is the integral of `ρ = √(det g)` over its coordinate image in that
chart. The atlas chosen to build `globalMeasure` is invisible here — this is what makes the
definition the honest `√(det gᵢⱼ) dx¹ ⋯ dxⁿ`, and it is the interface every volume
statement should use. -/
theorem globalMeasure_apply_chart (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (i : ℕ)
    {s : Set M} (hs : MeasurableSet s) (hsi : s ⊆ A.chart i '' A.source i) :
    A.globalMeasure μ s
      = ∫⁻ y in A.chartPreimage i s, ENNReal.ofReal (A.density i y) ∂μ := by
  classical
  have hpiece : ∀ n, MeasurableSet (s ∩ A.chartPiece n) := fun n =>
    hs.inter (A.measurableSet_chartPiece n)
  have hdisj : Pairwise (Disjoint on fun n => s ∩ A.chartPiece n) := fun _ _ hmn =>
    (A.pairwiseDisjoint_chartPiece hmn).mono inter_subset_right inter_subset_right
  have hchart : ∀ n, (A.chartMeasure μ n).restrict (A.chartPiece n) s
      = A.chartMeasure μ i (s ∩ A.chartPiece n) := by
    intro n
    rw [Measure.restrict_apply hs]
    exact A.chartMeasure_apply_eq μ n i (hpiece n)
      (fun _ hz => A.chartPiece_subset n hz.2) (fun _ hz => hsi hz.1)
  rw [globalMeasure, Measure.sum_apply _ hs]
  calc ∑' n, (A.chartMeasure μ n).restrict (A.chartPiece n) s
      = ∑' n, A.chartMeasure μ i (s ∩ A.chartPiece n) := tsum_congr hchart
    _ = A.chartMeasure μ i (⋃ n, s ∩ A.chartPiece n) :=
        (measure_iUnion hdisj hpiece).symm
    _ = A.chartMeasure μ i s := by rw [← inter_iUnion, A.iUnion_chartPiece, inter_univ]
    _ = _ := A.chartMeasure_apply μ i hs

/-! ## Normalization and the one-chart case -/

/-- A chart measure is linear in the additive Haar reference measure. -/
theorem chartMeasure_smul (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (i : ℕ) (c : ℝ≥0∞) :
    A.chartMeasure (c • μ) i = c • A.chartMeasure μ i := by
  have hae : AEMeasurable (A.chart i) (μ.restrict (A.source i)) :=
    (A.measurable_chart i).aemeasurable
  have hae' : AEMeasurable (A.chart i)
      ((μ.restrict (A.source i)).withDensity
        (fun y => ENNReal.ofReal (A.density i y))) :=
    hae.mono_ac (withDensity_absolutelyContinuous _ _)
  unfold chartMeasure
  rw [Measure.restrict_smul, MeasureTheory.withDensity_smul_measure,
    MeasureTheory.Measure.map_smul _ hae']

/-- The global Riemannian measure is linear in the additive Haar reference measure: scalar
normalization can be performed before or after assembling the manifold measure; no
normalization is hidden in the definition of `globalMeasure`. -/
theorem globalMeasure_smul (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (c : ℝ≥0∞) :
    A.globalMeasure (c • μ) = c • A.globalMeasure μ := by
  have hchart (n : ℕ) : A.chartMeasure (c • μ) n = c • A.chartMeasure μ n :=
    A.chartMeasure_smul μ n c
  have hrestrict (n : ℕ) : (A.chartMeasure (c • μ) n).restrict (A.chartPiece n)
      = c • (A.chartMeasure μ n).restrict (A.chartPiece n) := by
    rw [hchart, Measure.restrict_smul]
  apply Measure.ext
  intro s hs
  change (Measure.sum fun n =>
      (A.chartMeasure (c • μ) n).restrict (A.chartPiece n)) s =
    (c • Measure.sum fun n =>
      (A.chartMeasure μ n).restrict (A.chartPiece n)) s
  rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.sum_apply _ hs]
  simp_rw [hrestrict, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_left]

/-- **Restriction to a chart image.** The global measure restricted to the image of a chart
is the chart measure restricted to that image. This is the form used to transfer integrals
of functions whose support lies in a single chart from the chart layer to the manifold
measure. -/
theorem globalMeasure_restrict_eq_chartMeasure (μ : Measure (Vec d)) [μ.IsAddHaarMeasure]
    (i : ℕ) :
    (A.globalMeasure μ).restrict (A.chart i '' A.source i)
      = (A.chartMeasure μ i).restrict (A.chart i '' A.source i) := by
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    A.globalMeasure_apply_chart μ i (hs.inter (A.measurableSet_image i))
      (fun _ hx => hx.2),
    A.chartMeasure_apply μ i (hs.inter (A.measurableSet_image i))]

/-- **The one-chart case**: when a single chart covers the manifold, the global measure is
exactly that chart measure. In particular the global measure of a set is the density
integral in that chart. -/
theorem globalMeasure_eq_chartMeasure_of_cover (μ : Measure (Vec d)) [μ.IsAddHaarMeasure]
    (i : ℕ) (hi : A.chart i '' A.source i = univ) :
    A.globalMeasure μ = A.chartMeasure μ i := by
  apply Measure.ext
  intro s hs
  rw [A.globalMeasure_apply_chart μ i hs (fun _ _ => by rw [hi]; exact mem_univ _),
    A.chartMeasure_apply μ i hs]

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.det_jacobianOf
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.det_matrix_transform
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.density_transform
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_restrict_eq_chartMeasure
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_eq_chartMeasure_of_cover
