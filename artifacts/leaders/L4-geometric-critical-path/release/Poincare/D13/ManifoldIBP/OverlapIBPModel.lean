/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (overlapping-atlas model IBP)

# The manifold IBP on the dilation-chart model, unconditionally

`ManifoldIBP.OverlapIBP` proves the manifold weighted integration-by-parts identity on the
global Riemannian measure of an *arbitrary* overlapping atlas, for test data supported in a
single chart. This module **instantiates** that theorem on the inhabited model of
`ManifoldIBP.OverlapModel` — the dilation-chart pair `1 • ·` and `2 • ·` on `Vec (n+1)`,
which overlap completely and carry genuinely different chart metrics — so the interface is
not vacuous and the identity is obtained with no atlas-level hypothesis left:

* `dilationAtlasTwo` — the model atlas with dilation factor `2`;
* `dilationAtlasTwo_integral_eq_chart` — **the global Riemannian measure computes the D12
  chart integral**: `∫_M g d(e^{-F} μ_g) = ∫ e^{-F(y)} g(y) √(det G(y)) dy` for the entropy
  measure of the atlas; this is the change-of-variables/gluing content of the atlas layer;
* `dilationAtlasTwo_weightedIBP` — **the manifold weighted integration by parts** on that
  glued measure, for `C²` data `F, U, V` with `V` compactly supported,
  `∫_M (Δ_F U) V d(e^{-F} μ_g) = -∫_M ⟨∇U,∇V⟩_{G⁻¹} d(e^{-F} μ_g)`;
* `dilationAtlasTwo_weightedIBP_chart` — the same identity written as the D12 chart identity,
  showing the manifold theorem reduces exactly to `ChartMetric.chart_weighted_ibp`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBP

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- **The dilation model atlas**: the two-chart overlapping atlas with dilation factor `2`
(unit chart `1 • ·` and dilated chart `2 • ·`) and base metric `G`. -/
def dilationAtlasTwo (n : ℕ) (G : ChartMetric (n + 1)) : OverlapAtlas (Vec (n + 1)) (n + 1) :=
  dilationAtlas (d := n + 1) 2 (by norm_num) G

/-- The `0`-th chart of the model atlas is the unit chart with source `univ`, hence its image
is everything. -/
lemma dilationAtlasTwo_image_zero (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).chart 0 '' (dilationAtlasTwo n G).source 0 = univ := by
  show dilationChart (d := n + 1) 2 0 '' univ = univ
  exact dilationChart_image_univ (d := n + 1) (by norm_num) 0

/-- The chart map of the `1`-st chart of the model atlas is the dilation by `2`. -/
lemma dilationAtlasTwo_chart_one (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).chart 1 = fun x : Vec (n + 1) => (2 : ℝ) • x := by
  show dilationChart (d := n + 1) 2 1 = fun x => (2 : ℝ) • x
  exact dilationChart_of_ne 2 (by norm_num)

/-- The chart metric of the `1`-st chart of the model atlas is the dilation pullback. -/
lemma dilationAtlasTwo_metric_one (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).metric 1 = dilateMetric G 2 (by norm_num) := by
  show dilationMetric (d := n + 1) 2 (by norm_num) G 1 = dilateMetric G 2 (by norm_num)
  simp [dilationMetric]

/-- The Riemannian density of the `1`-st chart of the model atlas is the dilation-pullback
density. -/
lemma dilationAtlasTwo_density_one (G : ChartMetric (n + 1)) (y : Vec (n + 1)) :
    (dilationAtlasTwo n G).density 1 y = (dilateMetric G 2 (by norm_num)).density y := by
  show (dilationMetric (d := n + 1) 2 (by norm_num) G 1).density y
      = (dilateMetric G 2 (by norm_num)).density y
  simp [density, dilationMetric]

/-- The Riemannian density of the `0`-th chart of the model atlas is the base density. -/
lemma dilationAtlasTwo_metric_zero (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).metric 0 = G := by
  show dilationMetric (d := n + 1) 2 (by norm_num) G 0 = G
  simp [dilationMetric]

/-- The chart map of the `0`-th chart of the model atlas is the unit dilation. -/
lemma dilationAtlasTwo_chart_zero (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).chart 0 = fun x : Vec (n + 1) => (1 : ℝ) • x := by
  show dilationChart (d := n + 1) 2 0 = fun x => (1 : ℝ) • x
  exact dilationChart_zero 2

/-- **The global measure of the model atlas computes the D12 chart integral**: for any
function on the manifold, the integral against the entropy measure
`d(e^{-F} μ_g) = e^{-F} dμ_g` of the overlapping-atlas Riemannian measure `μ_g` is the D12
chart density integral. This is the gluing content of the atlas layer, made explicit. -/
theorem dilationAtlasTwo_integral_eq_chart (G : ChartMetric (n + 1)) (F g : Vec (n + 1) → ℝ)
    (hF : Measurable F)
    (hg : AEStronglyMeasurable g ((dilationAtlasTwo n G).chartMeasure volume 0)) :
    ∫ m, g m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = ∫ y, g y * Real.exp (-(F y)) * G.density y ∂volume := by
  have hsupp : ∀ m : Vec (n + 1), g m ≠ 0 →
      m ∈ (dilationAtlasTwo n G).chart 0 '' (dilationAtlasTwo n G).source 0 := by
    intro m _
    rw [dilationAtlasTwo_image_zero]
    exact mem_univ m
  rw [(dilationAtlasTwo n G).integral_globalMeasure_withDensity_of_supported volume 0 hF hg
    hsupp]
  rw [show (dilationAtlasTwo n G).source 0 = univ from rfl, setIntegral_univ,
    dilationAtlasTwo_chart_zero]
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [one_smul]
  have hd : (dilationAtlasTwo n G).density 0 y = G.density y := by
    simp [density, dilationAtlasTwo_metric_zero]
  rw [hd]
  ring

/-- **Manifold weighted integration by parts on the overlapping-atlas model.** For `C²` data
`F, U, V` with `V` compactly supported, the weighted IBP identity holds on the global
Riemannian measure of the dilation-chart atlas — with no atlas hypothesis left to discharge:
the model atlas `dilationAtlasTwo` inhabits them. -/
theorem dilationAtlasTwo_weightedIBP (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) :
    ∫ m, G.driftLaplacian F U m * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = -∫ m, G.gradInnerInverse U V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F)) := by
  refine (dilationAtlasTwo n G).globalWeightedIBP_of_chartSupported 0 F U V
    (G.driftLaplacian F U) (G.gradInnerInverse U V)
    hF.continuous.measurable hV.continuous.measurable
    (G.driftLaplacian_continuous F U hF hU).measurable
    (G.gradInnerInverse_continuous U V hU hV).measurable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m _
    rw [dilationAtlasTwo_image_zero]
    exact mem_univ m
  · intro m _
    rw [dilationAtlasTwo_image_zero]
    exact mem_univ m
  · intro y _
    exact mem_univ y
  · intro y _
    exact mem_univ y
  · rw [dilationAtlasTwo_chart_zero]
    exact hF.comp (contDiff_const_smul (1 : ℝ))
  · rw [dilationAtlasTwo_chart_zero]
    exact hU.comp (contDiff_const_smul (1 : ℝ))
  · rw [dilationAtlasTwo_chart_zero]
    exact hV.comp (contDiff_const_smul (1 : ℝ))
  · rw [dilationAtlasTwo_chart_zero]
    simpa using hVc
  · refine ae_of_all _ fun y _ => ?_
    rw [dilationAtlasTwo_chart_zero, dilationAtlasTwo_metric_zero]
    simp only [one_smul]
  · refine ae_of_all _ fun y _ => ?_
    rw [dilationAtlasTwo_chart_zero, dilationAtlasTwo_metric_zero]
    simp only [one_smul]

/-- **The model IBP is exactly the D12 chart IBP.** The manifold identity of
`dilationAtlasTwo_weightedIBP`, with both sides expanded by
`dilationAtlasTwo_integral_eq_chart`, is the chart identity
`ChartMetric.chart_weighted_ibp`. -/
theorem dilationAtlasTwo_weightedIBP_chart (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) :
    ∫ y, G.driftLaplacian F U y * V y * Real.exp (-(F y)) * G.density y ∂volume
      = -∫ y, G.gradInnerInverse U V y * Real.exp (-(F y)) * G.density y ∂volume :=
  G.chart_weighted_ibp F U V hF hU hV hVc

/-- The entropy weight of the zero drift is identically `1`. -/
lemma dilationAtlasTwo_weight_zero (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).weight (fun _ : Vec (n + 1) => 0) = fun _ => 1 := by
  funext m
  simp [weight]

/-- Weighting the model's global measure by the zero-drift entropy weight does not change
it: it is the measure itself. -/
lemma dilationAtlasTwo_withDensity_weight_zero (G : ChartMetric (n + 1)) :
    ((dilationAtlasTwo n G).globalMeasure volume).withDensity
        ((dilationAtlasTwo n G).weight (fun _ => 0))
      = (dilationAtlasTwo n G).globalMeasure volume := by
  rw [dilationAtlasTwo_weight_zero]
  exact withDensity_one

/-- **The manifold (unweighted) integration by parts — the Green identity** on the
overlapping-atlas Riemannian measure: for `C²` `U, V` with `U` compactly supported,
`∫_M U · Δ_G V dμ_g = -∫_M ⟨∇U, ∇V⟩_{G⁻¹} dμ_g`. Obtained by the atlas bridge from D12's
`ChartMetric.chart_ibp`. -/
theorem dilationAtlasTwo_ibp (G : ChartMetric (n + 1)) (U V : Vec (n + 1) → ℝ)
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V) (hUc : HasCompactSupport U) :
    ∫ m, U m * G.laplacian V m ∂((dilationAtlasTwo n G).globalMeasure volume)
      = -∫ m, G.gradInnerInverse U V m ∂((dilationAtlasTwo n G).globalMeasure volume) := by
  have hL : ∫ m, U m * G.laplacian V m ∂((dilationAtlasTwo n G).globalMeasure volume)
      = ∫ y, U y * G.laplacian V y * G.density y ∂volume := by
    rw [← dilationAtlasTwo_withDensity_weight_zero G]
    rw [dilationAtlasTwo_integral_eq_chart G (fun _ => 0)
      (fun m => U m * G.laplacian V m) measurable_const
      (hU.continuous.measurable.mul (G.laplacian_continuous V hV).measurable).aestronglyMeasurable]
    simp
  have hR : ∫ m, G.gradInnerInverse U V m ∂((dilationAtlasTwo n G).globalMeasure volume)
      = ∫ y, G.gradInnerInverse U V y * G.density y ∂volume := by
    rw [← dilationAtlasTwo_withDensity_weight_zero G]
    rw [dilationAtlasTwo_integral_eq_chart G (fun _ => 0) (fun m => G.gradInnerInverse U V m)
      measurable_const (G.gradInnerInverse_continuous U V hU hV).measurable.aestronglyMeasurable]
    simp
  rw [hL, hR]
  exact G.chart_ibp U V hU hV hUc

/-- **The manifold divergence theorem (Laplacian form)**: `∫_M Δ_G V dμ_g = 0` for `C²` `V`
with compact support, on the overlapping-atlas Riemannian measure. Obtained by the atlas
bridge from D12's `ChartMetric.laplacian_integral_eq_zero`. -/
theorem dilationAtlasTwo_laplacianIntegralZero (G : ChartMetric (n + 1))
    (V : Vec (n + 1) → ℝ) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V) :
    ∫ m, G.laplacian V m ∂((dilationAtlasTwo n G).globalMeasure volume) = 0 := by
  have hL : ∫ m, G.laplacian V m ∂((dilationAtlasTwo n G).globalMeasure volume)
      = ∫ y, G.laplacian V y * G.density y ∂volume := by
    rw [← dilationAtlasTwo_withDensity_weight_zero G]
    rw [dilationAtlasTwo_integral_eq_chart G (fun _ => 0) (fun m => G.laplacian V m)
      measurable_const (G.laplacian_continuous V hV).measurable.aestronglyMeasurable]
    simp
  rw [hL, G.laplacian_integral_eq_zero V hV hVc]

/-- **The Dirichlet energy identity (weighted Green identity)**: for the entropy measure of
the overlapping-atlas model, `∫_M (Δ_F V) · V d(e^{-F} μ_g) = -∫_M |∇V|²_{G⁻¹} d(e^{-F} μ_g)`.
This is the weighted IBP with `U = V`. -/
theorem dilationAtlasTwo_dirichletEnergy (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V) :
    ∫ m, G.driftLaplacian F V m * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = -∫ m, G.gradInnerInverse V V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F)) :=
  dilationAtlasTwo_weightedIBP G F V V hF hV hV hVc


/-- **The two overlapping charts compute the same integral.** The unit chart (metric `G`) and
the dilation chart (metric `4 • G(2·)`) give the same value for the entropy-weighted integral
of the same manifold function — the Riemannian change-of-variables identity in which the
Jacobian `2^{n+1}` of the chart transition cancels the metric density transformation. Proved
by computing both sides through `globalMeasure` (i.e. through chart-independence), not by a
direct change of variables. -/
theorem dilationAtlasTwo_chart_integral_eq (G : ChartMetric (n + 1)) (F g : Vec (n + 1) → ℝ)
    (hF : Measurable F) (hg : Measurable g) :
    ∫ y, g y * Real.exp (-(F y)) * G.density y ∂volume
      = ∫ y, g (2 • y) * Real.exp (-(F (2 • y)))
          * (dilateMetric G 2 (by norm_num)).density y ∂volume := by
  have h0 := dilationAtlasTwo_integral_eq_chart (n := n) G F g hF hg.aestronglyMeasurable
  have h1 := (dilationAtlasTwo n G).integral_globalMeasure_withDensity_of_supported volume 1 hF
    hg.aestronglyMeasurable
    (fun m _ => by
      rw [show (dilationAtlasTwo n G).chart 1 '' (dilationAtlasTwo n G).source 1 = univ from
        dilationChart_image_univ (d := n + 1) (by norm_num) 1]
      exact mem_univ m)
  rw [← h0, h1]
  rw [show (dilationAtlasTwo n G).source 1 = univ from rfl, setIntegral_univ]
  simp only [dilationAtlasTwo_chart_one, dilationAtlasTwo_density_one]
  refine integral_congr_ae ?_
  filter_upwards with y
  have harg : (2 : ℝ) • y = y * 2 := by
    funext i
    simp [Pi.smul_apply, mul_comm]
  rw [harg]
  ring

/-- **Chart independence on the model**: the unit chart and the dilation chart carry
genuinely different Gram matrices (`G` versus `4 • G(2 ·)`), yet they define the *same*
Riemannian measure on `Vec (n+1)`. Proved from the general `chartMeasure_apply_eq` (the
dilation Jacobian `2 • 1` cancels against the density transformation law); no direct
computation of the change of variables is used here. -/
theorem dilationAtlasTwo_chartMeasure_eq (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).chartMeasure volume 0
      = (dilationAtlasTwo n G).chartMeasure volume 1 := by
  apply Measure.ext
  intro s hs
  exact (dilationAtlasTwo n G).chartMeasure_apply_eq volume 0 1 hs
    (fun _ _ => by rw [dilationAtlasTwo_image_zero]; exact mem_univ _)
    (fun _ _ => by
      rw [show (dilationAtlasTwo n G).chart 1 '' (dilationAtlasTwo n G).source 1 = univ from
        dilationChart_image_univ (d := n + 1) (by norm_num) 1]
      exact mem_univ _)

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_image_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_metric_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_integral_eq_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_withDensity_weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_ibp
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_dirichletEnergy
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartMeasure_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_metric_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_density_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_integral_eq
