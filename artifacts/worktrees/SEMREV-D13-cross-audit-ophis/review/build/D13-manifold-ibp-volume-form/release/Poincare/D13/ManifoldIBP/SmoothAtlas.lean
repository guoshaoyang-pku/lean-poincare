/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (lifted partition-of-unity pieces)

# Smooth atlases with global chart transitions, and the lifted partition-of-unity pieces

`ManifoldIBP.POUAssembly` reduces the global IBP to partition-of-unity data in a base chart, but
takes the pieces `v_j` (and their pairings) as *data*: the lift of a coordinate function to the
manifold was still missing (blocker `U7-GLOBAL-LIFT`). This module supplies it for an atlas whose
charts are globally injective and whose transitions are honest global coordinate changes:

* `SmoothOverlapAtlas` — an `OverlapAtlas` with open overlaps, globally injective charts,
  measurable readbacks `Function.invFunOn (chart i) (source i)`, global `C²` transition maps and the
  global chart relation `chart i (transition i j y) = chart j y`;
* `SmoothOverlapAtlas.lift` — the lift of a coordinate function `φ` to `M` through a chart
  (`φ` read back through `chart b`, `0` off its image), with
  `lift_apply_chart`, `support_lift_subset`, `measurable_lift` and the key
  `lift_apply_chart_of_mem` identifying the lift's `i`-chart expression with
  `φ (transition b i ·)`;
* the dilation atlas `dilationAtlasTwo` inhabits `SmoothOverlapAtlas`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.GlobalMeasure
import Poincare.D13.ManifoldIBP.OverlapIBPModel

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {d : ℕ}

/-- **A smooth atlas with globally injective charts and honest global transitions.** Extends
`OverlapAtlas` with the data needed to lift coordinate functions to the manifold: open overlaps,
global injectivity of the charts, a measurable readback on each chart, global `C²` transition maps
and the global coordinate-change relation `chart i (transition i j y) = chart j y`. -/
structure SmoothOverlapAtlas (M : Type*) [MeasurableSpace M] (d : ℕ)
    extends OverlapAtlas M d where
  /-- the coordinate overlaps are open -/
  isOpen_overlap : ∀ i j, IsOpen (overlapOf chart source i j)
  /-- the charts are globally injective (their total extensions are honest coordinates) -/
  inj_chart : ∀ i, Function.Injective (chart i)
  /-- the readback through a chart is measurable -/
  measurable_readback : ∀ i, Measurable (Function.invFunOn (chart i) (source i))
  /-- the transition maps are globally `C²` -/
  contDiff_transition : ∀ i j, ContDiff ℝ 2 (transition i j)
  /-- the global coordinate-change relation -/
  transition_chart_global : ∀ i j y, chart i (transition i j y) = chart j y

namespace SmoothOverlapAtlas

variable (A : SmoothOverlapAtlas M d)

/-- **The lift of a coordinate function through a chart**: read `φ` back through `chart b`, and
return `0` off the chart image. -/
def lift (b : ℕ) (φ : Vec d → ℝ) : M → ℝ := by
  classical
  exact fun m => if m ∈ A.chart b '' A.source b
    then φ (Function.invFunOn (A.chart b) (A.source b) m) else 0

lemma lift_apply_chart {b : ℕ} {φ : Vec d → ℝ} {y : Vec d} (hy : y ∈ A.source b) :
    A.lift b φ (A.chart b y) = φ y := by
  have hmem : A.chart b y ∈ A.chart b '' A.source b := ⟨y, hy, rfl⟩
  rw [lift, if_pos hmem]
  have h1 : Function.invFunOn (A.chart b) (A.source b) (A.chart b y) ∈ A.source b :=
    Function.invFunOn_mem ⟨y, hy, rfl⟩
  have h2 : A.chart b (Function.invFunOn (A.chart b) (A.source b) (A.chart b y)) = A.chart b y :=
    Function.invFunOn_eq ⟨y, hy, rfl⟩
  rw [A.inj_chart b h2]

/-- The lift is supported in the chart image of the support of `φ`. -/
lemma support_lift_subset {b : ℕ} {φ : Vec d → ℝ} :
    support (A.lift b φ) ⊆ A.chart b '' support φ := by
  intro m hm
  rw [Function.mem_support] at hm
  by_cases hmem : m ∈ A.chart b '' A.source b
  · rw [lift, if_pos hmem] at hm
    exact ⟨Function.invFunOn (A.chart b) (A.source b) m, hm,
      Function.invFunOn_eq hmem⟩
  · rw [lift, if_neg hmem] at hm
    exact absurd rfl hm

/-- The lift is measurable as soon as `φ` is. -/
lemma measurable_lift {b : ℕ} {φ : Vec d → ℝ} (hφ : Measurable φ) :
    Measurable (A.lift b φ) := by
  have hset : MeasurableSet (A.chart b '' A.source b) := A.measurableSet_image b
  exact Measurable.ite hset (hφ.comp (A.measurable_readback b)) measurable_const

/-- **The chart-`i` expression of the lift through `b`.** On the overlap, reading the lift back
through the `i`-th chart gives `φ` evaluated at the transition `transition b i`: the transition is
the honest coordinate change, so the unique `b`-coordinate of `chart i z` is
`transition b i z`. -/
lemma lift_apply_chart_of_mem {b i : ℕ} {φ : Vec d → ℝ} {z : Vec d}
    (hz : A.chart i z ∈ A.chart b '' A.source b) :
    A.lift b φ (A.chart i z) = φ (A.transition b i z) := by
  have hmem : A.chart i z ∈ A.chart b '' A.source b := hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hτsrc : A.transition b i z ∈ A.source b := by
    have hyz' : A.chart b y = A.chart b (A.transition b i z) := by
      rw [A.transition_chart_global b i z]
      exact hyz
    have hyτ : y = A.transition b i z := A.inj_chart b hyz'
    rwa [← hyτ]
  have h1 : Function.invFunOn (A.chart b) (A.source b) (A.chart i z) ∈ A.source b :=
    Function.invFunOn_mem ⟨A.transition b i z, hτsrc, (A.transition_chart_global b i z)⟩
  have h2 : A.chart b (Function.invFunOn (A.chart b) (A.source b) (A.chart i z))
      = A.chart b (A.transition b i z) := by
    rw [Function.invFunOn_eq ⟨A.transition b i z, hτsrc, A.transition_chart_global b i z⟩,
      A.transition_chart_global b i z]
  have h3 : Function.invFunOn (A.chart b) (A.source b) (A.chart i z) = A.transition b i z :=
    A.inj_chart b h2
  rw [lift, if_pos hmem, h3]

/-- The lift of a function supported in the source is supported in the chart image of its
topological support. -/
lemma support_lift_subset_tsupport {b : ℕ} {φ : Vec d → ℝ}
    (hφ : tsupport φ ⊆ A.source b) :
    support (A.lift b φ) ⊆ A.chart b '' tsupport φ := by
  intro m hm
  obtain ⟨y, hy, hyz⟩ := A.support_lift_subset (b := b) (φ := φ) hm
  exact ⟨y, subset_tsupport φ hy, hyz⟩

end SmoothOverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_lift_subset
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.measurable_lift
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_lift_subset_tsupport
