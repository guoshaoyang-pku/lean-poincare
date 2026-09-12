/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (smoothness of the chart Gram matrix)

# Smoothness of the chart Gram matrix of a genuine Riemannian metric

`Riemannian.MetricBridge` proves the `(0,2)`-tensor transformation law of the chart Gram matrix
of a genuine Riemannian metric at the release pin. For the measure-theoretic layer one also
needs that the Gram entries are smooth (the density `√(det G)` must be measurable/continuous,
and D12's `ChartMetric` demands `C^∞` coefficients). This module proves it from the pin's
`IsContMDiffRiemannianBundle` assumption:

* `contMDiffOn_chartFrameSection` — the chart frame section
  `x ↦ (x, (trivializationAt α).symm x v)` is `C^∞` on the chart source. The proof uses the
  trivialization criterion `Trivialization.contMDiffWithinAt_section`: in the trivialization's
  own coordinates the section is the *constant* `v`, and a constant is smooth;
* `contMDiffOn_chartGramMatrix_entry` — each Gram entry `x ↦ G^α_{ij}(x)` is `C^∞` on the chart
  source, by `ContMDiffOn.inner_bundle` applied to two frame sections;
* `contDiffOn_chartGramMatrix_coord` — in chart coordinates
  `y ↦ G^α_{ij}((extChartAt I α).symm y)` is `C^∞` on the chart target, which is the form
  required by the D12 chart layer.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.Riemannian.MetricBridge

open Bundle Set
open scoped Manifold ContDiff Topology Bundle Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.D13.Riemannian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- **Smoothness of the constant model-vector section.** For a model vector `v`, the section
`x ↦ (x, (trivializationAt E (TangentSpace I) α).symm x v)` of the tangent bundle over the
chart source is `C^∞`. In the trivialization's own coordinates this section is the constant
`v` (`Trivialization.mk_symm`), so the criterion
`Trivialization.contMDiffWithinAt_section` reduces it to smoothness of a constant. -/
lemma contMDiffOn_chartFrameSection (v : E) (α : M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x
        ((trivializationAt E (TangentSpace I) α).symm x v))
      (chartAt H α).source := by
  intro x hx
  have : ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := inferInstance
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  refine (Bundle.Trivialization.contMDiffWithinAt_section (n := ∞) (IB := I)
    (e := trivializationAt E (TangentSpace I) α) (chartAt H α).source hx').mpr ?_
  have hev : (fun y => ((trivializationAt E (TangentSpace I) α)
        ⟨y, (trivializationAt E (TangentSpace I) α).symm y v⟩).2)
      =ᶠ[𝓝[(chartAt H α).source] x] fun _ => v := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hy
    have h1 : TotalSpace.mk y ((trivializationAt E (TangentSpace I) α).symm y v)
        = (trivializationAt E (TangentSpace I) α).toOpenPartialHomeomorph.symm (y, v) :=
      Trivialization.mk_symm (trivializationAt E (TangentSpace I) α) hy' v
    have h2 : (trivializationAt E (TangentSpace I) α)
        ((trivializationAt E (TangentSpace I) α).toOpenPartialHomeomorph.symm (y, v))
        = (y, v) :=
      Trivialization.apply_symm_apply' (trivializationAt E (TangentSpace I) α) hy'
    show ((trivializationAt E (TangentSpace I) α)
        ⟨y, (trivializationAt E (TangentSpace I) α).symm y v⟩).2 = v
    rw [show (⟨y, (trivializationAt E (TangentSpace I) α).symm y v⟩ :
          TotalSpace E (TangentSpace I))
        = TotalSpace.mk y ((trivializationAt E (TangentSpace I) α).symm y v) from rfl, h1, h2]
  exact (contMDiffWithinAt_const (c := v)).congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin hx)

/-- **Smoothness of the chart Gram entries.** For a `C^∞` Riemannian bundle structure on the
tangent bundle, each entry of the chart Gram matrix is `C^∞` on the chart source: it is the
inner product of two smooth frame sections. -/
lemma contMDiffOn_chartGramMatrix_entry
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    (B : Module.Basis ι ℝ E) (α : M) (i j : ι) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun x => chartGramMatrix (I := I) B α x i j)
      (chartAt H α).source := by
  rw [show (fun x => chartGramMatrix (I := I) B α x i j)
      = fun x => inner ℝ ((trivializationAt E (TangentSpace I) α).symm x (B i))
          ((trivializationAt E (TangentSpace I) α).symm x (B j)) from rfl]
  exact ContMDiffOn.inner_bundle (contMDiffOn_chartFrameSection (B i) α)
    (contMDiffOn_chartFrameSection (B j) α)

/-- **Smoothness of the chart Gram entries in coordinates**: for a genuine `C^∞` Riemannian
metric, `y ↦ G^α_{ij}((extChartAt I α).symm y)` is `C^∞` on the chart target. This is the form
of the smoothness required by the D12 chart layer (`ChartMetric.smooth`). -/
lemma contDiffOn_chartGramMatrix_coord
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    (B : Module.Basis ι ℝ E) (α : M) (i j : ι) :
    ContDiffOn ℝ ∞
      (fun y => chartGramMatrix (I := I) B α ((extChartAt I α).symm y) i j)
      (extChartAt I α).target := by
  have hcomp := (contMDiffOn_chartGramMatrix_entry (I := I) B α i j).comp
    (contMDiffOn_extChartAt_symm (I := I) α) (fun y hy => by
      have h := (extChartAt I α).map_target hy
      rwa [extChartAt_source] at h)
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp

end Poincare.D13.Riemannian

/-! ## Axiom audit -/

#print axioms Poincare.D13.Riemannian.contMDiffOn_chartFrameSection
#print axioms Poincare.D13.Riemannian.contMDiffOn_chartGramMatrix_entry
#print axioms Poincare.D13.Riemannian.contDiffOn_chartGramMatrix_coord
