/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (chart atlas from a Riemannian metric)

# The atlas tensor law of `ManifoldIBP.OverlapAtlas` is a theorem for genuine metrics

`ManifoldIBP.OverlapAtlas` postulates the `(0,2)`-tensor transformation law
`metric j y = Jᵀ · metric i (transition i j y) · J` as a *hypothesis*
(`OverlapAtlas.metric_transform`). `Riemannian.MetricBridge` proved the law for the chart Gram
matrix of a genuine Riemannian metric, with the tangent coordinate change of the pin's manifold
library. This module **consumes** that theorem at the exact shape of the atlas field, in the
chart model `Vec d = Fin d → ℝ` of the D12 layer:

* `jacobianOf_eq_toMatrix` — `jacobianOf` (the Jacobian matrix used by the atlas layer) is the
  matrix of `fderivWithin` in the model basis `Pi.basisFun ℝ (Fin d)`;
* `chartMetricMatrix` — the genuine chart Gram matrix read in the coordinates of a chart
  (`metric i` of the genuine chart atlas);
* **`metric_transform_chartTransition`** — the tensor law in the atlas transition form, with
  `transition = chartTransition` and the chart Gram matrices as the metrics;
* `fderivWithin_chartTransition_eq_of_isOpen` — on a boundaryless model the derivative may be
  taken on any open set containing the point; hence on the actual chart overlap
  `overlapOf` of `ManifoldIBP.GlobalMeasure` the law is literally the atlas field equation
  (`metric_transform_overlapOf`).

The one thing this module does **not** do is package the chart Gram data into the global
`ChartMetric d` structure of D12: that structure demands `C^∞` coefficients and positive
definiteness on *all* of `Vec d`, whereas the genuine Gram matrix is a priori smooth and
positive definite only on the chart target. The identification of the genuine chart Gram
matrix with an *extended* global `ChartMetric` (smooth bump extension) is the residual
packaging gap, recorded in the results card.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.Riemannian.MetricBridge
import Poincare.D13.ManifoldIBP.GlobalMeasure

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
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-! ## The atlas Jacobian and the chart model basis -/

/-- **The atlas Jacobian is the matrix of the derivative in the model basis.** The metric bridge
is stated for an arbitrary basis; in the chart model `Vec d = Fin d → ℝ` the model basis is
`Pi.basisFun ℝ (Fin d)`, which is exactly the basis the atlas layer's `jacobianOf` uses. -/
theorem jacobianOf_eq_toMatrix (ψ : Vec d → Vec d) (s : Set (Vec d)) (y : Vec d) :
    jacobianOf ψ s y
      = LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
          (fderivWithin ℝ ψ s y).toLinearMap := rfl

/-! ## The genuine chart atlas data -/

/-- **The metric matrix of a genuine chart**, read in coordinates: the Gram matrix of the chart
coordinate frame at the point with coordinates `y`. This is the `metric i` field of the chart
atlas built from a Riemannian metric on `M`. -/
def chartMetricMatrix (α : M) (y : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  chartGramMatrix (E := Vec d) (I := I) (Pi.basisFun ℝ (Fin d)) α ((extChartAt I α).symm y)

/-! ## The tensor law in atlas shape -/

/-- **The `(0,2)`-tensor law with the chart transition**, in the shape of
`OverlapAtlas.metric_transform` with `transition = chartTransition`: the `β`-chart Gram matrix
is the congruence of the `α`-chart Gram matrix by the Jacobian of the chart transition. The
derivative is taken on `range I` (the model-with-corners range, on which the coordinate change
is defined). -/
theorem metric_transform_chartTransition (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    chartGramMatrix (E := Vec d) (I := I) (Pi.basisFun ℝ (Fin d)) β x
      = (jacobianOf (chartTransition (E := Vec d) (I := I) α β) (range I)
            (extChartAt I β x)).transpose
          * chartGramMatrix (E := Vec d) (I := I) (Pi.basisFun ℝ (Fin d)) α x
          * jacobianOf (chartTransition (E := Vec d) (I := I) α β) (range I)
              (extChartAt I β x) := by
  rw [jacobianOf_eq_toMatrix]
  exact chartGramMatrix_change_chartTransition (I := I) (Pi.basisFun ℝ (Fin d)) α β hxα hxβ

/-- **Derivatives of the chart transition may be taken on any open set.** On a boundaryless
model `range I = univ`, so the derivative within `range I` used in the tangent coordinate
change agrees with the derivative within any open set containing the point — in particular with
the derivative within the atlas overlap `overlapOf`, which is what `OverlapAtlas.metric_transform`
uses. -/
theorem fderivWithin_chartTransition_eq_of_isOpen [I.Boundaryless] (α β : M)
    {s : Set (Vec d)} (hs : IsOpen s) {y : Vec d} (hy : y ∈ s) :
    fderivWithin ℝ (chartTransition (E := Vec d) (I := I) α β) s y
      = fderivWithin ℝ (chartTransition (E := Vec d) (I := I) α β) (range I) y := by
  rw [I.range_eq_univ, fderivWithin_univ, fderivWithin_of_isOpen hs hy]

/-- **The overlap of two genuine charts**, in `β`-coordinates: the points of the `β`-chart
target whose image lies in the image of the `α`-chart. -/
def chartOverlap (α β : M) : Set (Vec d) :=
  (extChartAt I β).target ∩ (extChartAt I β).symm ⁻¹'
    ((extChartAt I α).symm '' (extChartAt I α).target)

/-- The two-chart overlap is `overlapOf` for the `ℕ`-indexed chart family
`0 ↦ β, 1 ↦ α`; this is the `source`/`chart` data of the overlapping atlas built from two
genuine charts. -/
theorem chartOverlap_eq_overlapOf (α β : M) :
    chartOverlap (I := I) α β
      = overlapOf (fun n : ℕ => if n = 0 then (extChartAt I β).symm else (extChartAt I α).symm)
          (fun n : ℕ => if n = 0 then (extChartAt I β).target
            else (extChartAt I α).target) 1 0 := by
  simp [chartOverlap, overlapOf]

/-- **The atlas tensor law on the genuine chart overlap.** For the two-chart atlas
`0 ↦ β, 1 ↦ α`, on the atlas overlap and with the derivative taken on the overlap itself (as
`OverlapAtlas.metric_transform` does), the `(0,2)`-tensor law holds — *literally* the atlas
field equation, with `metric i` the genuine chart Gram matrix and `transition = chartTransition`.
The proof is the metric bridge plus the boundaryless identification of the derivative on the
open overlap with the derivative on `range I`. -/
theorem metric_transform_chartOverlap [I.Boundaryless] (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (hs : IsOpen (chartOverlap (I := I) α β)) :
    chartGramMatrix (E := Vec d) (I := I) (Pi.basisFun ℝ (Fin d)) β x
      = (jacobianOf (chartTransition (E := Vec d) (I := I) α β)
            (chartOverlap (I := I) α β) (extChartAt I β x)).transpose
          * chartGramMatrix (E := Vec d) (I := I) (Pi.basisFun ℝ (Fin d)) α x
          * jacobianOf (chartTransition (E := Vec d) (I := I) α β)
            (chartOverlap (I := I) α β) (extChartAt I β x) := by
  have hxα' : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hxβ' : x ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hmem : extChartAt I β x ∈ chartOverlap (I := I) α β := by
    refine ⟨(extChartAt I β).map_source hxβ', ?_⟩
    show (extChartAt I β).symm (extChartAt I β x)
      ∈ (extChartAt I α).symm '' (extChartAt I α).target
    rw [(extChartAt I β).left_inv hxβ', PartialEquiv.symm_image_target_eq_source]
    exact hxα'
  have hder : fderivWithin ℝ (chartTransition (E := Vec d) (I := I) α β)
        (chartOverlap (I := I) α β) (extChartAt I β x)
      = fderivWithin ℝ (chartTransition (E := Vec d) (I := I) α β) (range I)
          (extChartAt I β x) :=
    fderivWithin_chartTransition_eq_of_isOpen (I := I) α β hs hmem
  have hbase := metric_transform_chartTransition (I := I) α β hxα hxβ
  simp only [jacobianOf, hder]
  exact hbase

end Poincare.D13.Riemannian

/-! ## Axiom audit -/

#print axioms Poincare.D13.Riemannian.jacobianOf_eq_toMatrix
#print axioms Poincare.D13.Riemannian.metric_transform_chartTransition
#print axioms Poincare.D13.Riemannian.fderivWithin_chartTransition_eq_of_isOpen
#print axioms Poincare.D13.Riemannian.chartOverlap_eq_overlapOf
#print axioms Poincare.D13.Riemannian.metric_transform_chartOverlap
