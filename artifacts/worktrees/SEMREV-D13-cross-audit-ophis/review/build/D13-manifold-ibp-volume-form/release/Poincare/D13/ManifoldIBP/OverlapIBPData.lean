/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (overlapping-atlas → ManifoldAtlasData)

# The overlapping-atlas Riemannian measure inhabits `ManifoldAtlasData`

`ManifoldIBP.Transfer` defines the conditional interface `ManifoldAtlasData` (a finite atlas
with a glued measure and chart-identified operators) and proves the manifold weighted
integration by parts `manifoldWeightedIBP_of_atlasData` from it. That interface was inhabited
only by the **disjoint**-atlas model (`ManifoldIBP.DisjointModel`), where the chart measures
never overlap, so no transition Jacobian appears.

This module **inhabits `ManifoldAtlasData` with the genuinely overlapping dilation-chart
atlas** of `ManifoldIBP.OverlapIBPModel`: the measure is the entropy-weighted global measure
of the overlapping atlas, the chart is the unit chart, and the `integral_decomp` field is
*proved* from `dilationAtlasTwo_integral_eq_chart` — which itself rests on the
chart-independence theorem `chartMeasure_apply_eq` (the dilation Jacobian cancellation).

The `Integrable` hypothesis of the interface is converted into the
`AEStronglyMeasurable` input needed by the chart integral formula through the absolute
continuity `chartMeasure ≪ chartMeasure.withDensity (e^{-F})`
(`withDensity_absolutelyContinuous'`, which needs exactly the pointwise positivity of the
entropy weight).

Consequences:

* `dilationAtlasTwoData` — an inhabited `ManifoldAtlasData (Vec (n+1)) n 1` whose measure is
  the overlapping-atlas Riemannian measure (not a disjoint sum);
* `dilationAtlasTwoData_weightedIBP` — the manifold weighted IBP on that measure, obtained
  through the interface `manifoldWeightedIBP_of_atlasData` (the same statement as
  `dilationAtlasTwo_weightedIBP`, now with the interface's explicit integrability inputs).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.ManifoldIBP.Transfer

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- The model's global measure is its unit chart measure (the unit chart covers everything);
this is the one-chart case of `globalMeasure_eq_chartMeasure_of_cover`. -/
theorem dilationAtlasTwo_globalMeasure_eq_chartMeasure (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).globalMeasure volume
      = (dilationAtlasTwo n G).chartMeasure volume 0 := by
  apply Measure.ext
  intro s hs
  rw [(dilationAtlasTwo n G).globalMeasure_apply_chart volume 0 hs
      (fun _ _ => by rw [dilationAtlasTwo_image_zero]; exact mem_univ _),
    (dilationAtlasTwo n G).chartMeasure_apply volume 0 hs]

/-- The entropy weight of the model atlas is positive at every point, hence
`chartMeasure ≪ chartMeasure.withDensity (weight F)`. -/
theorem dilationAtlasTwo_chartMeasure_absolutelyContinuous (G : ChartMetric (n + 1))
    (F : Vec (n + 1) → ℝ) (hF : Measurable F) :
    (dilationAtlasTwo n G).chartMeasure volume 0
      ≪ ((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F) := by
  rw [dilationAtlasTwo_globalMeasure_eq_chartMeasure]
  exact withDensity_absolutelyContinuous'
    ((dilationAtlasTwo n G).measurable_weight hF).aemeasurable
    (ae_of_all _ fun _ => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

/-- **The overlapping-atlas Riemannian measure inhabits `ManifoldAtlasData`.** The measure is
the entropy-weighted global measure of the dilation-chart atlas, the unique chart is the unit
chart `x ↦ x`, and `integral_decomp` is *proved* from `dilationAtlasTwo_integral_eq_chart`
(hence from the chart-independence theorem). -/
def dilationAtlasTwoData (n : ℕ) (G : ChartMetric (n + 1)) (F : Vec (n + 1) → ℝ)
    (hF : Measurable F) : ManifoldAtlasData (Vec (n + 1)) n 1 where
  μ := ((dilationAtlasTwo n G).globalMeasure volume).withDensity
    ((dilationAtlasTwo n G).weight F)
  chart _ x := x
  metric _ := G
  drift _ := F
  integral_decomp := by
    intro g hg
    rw [Fin.sum_univ_one]
    have hAE : AEStronglyMeasurable g ((dilationAtlasTwo n G).chartMeasure volume 0) :=
      AEStronglyMeasurable.mono_ac
        (dilationAtlasTwo_chartMeasure_absolutelyContinuous G F hF) hg.1
    rw [dilationAtlasTwo_integral_eq_chart G F g hF hAE]
  driftLaplacianM u m := G.driftLaplacian F u m
  gradInnerM u v m := G.gradInnerInverse u v m
  weighted_laplacian_compat := by
    intro u i x
    fin_cases i
    rfl
  grad_inner_compat := by
    intro u v i x
    fin_cases i
    rfl

/-- **The manifold weighted IBP on the overlapping-atlas measure, through the
`ManifoldAtlasData` interface**: this is `manifoldWeightedIBP_of_atlasData` applied to
`dilationAtlasTwoData`, with the interface's explicit integrability inputs. The atlas is
genuinely overlapping (the unit chart and the dilation chart `2 • ·`), so the gluing datum
consumed here is the chart-independence theorem, not a disjoint-sum identification. -/
theorem dilationAtlasTwoData_weightedIBP (G : ChartMetric (n + 1)) (F u v : Vec (n + 1) → ℝ)
    (hF : Measurable F) (hd : ContDiff ℝ 2 F)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hg : Integrable (fun m => G.driftLaplacian F u m * v m)
      (dilationAtlasTwoData n G F hF).μ)
    (hg' : Integrable (fun m => G.gradInnerInverse u v m)
      (dilationAtlasTwoData n G F hF).μ) :
    ∫ m, G.driftLaplacian F u m * v m ∂(dilationAtlasTwoData n G F hF).μ
      = -∫ m, G.gradInnerInverse u v m ∂(dilationAtlasTwoData n G F hF).μ :=
  manifoldWeightedIBP_of_atlasData (dilationAtlasTwoData n G F hF) u v
    (fun i => by fin_cases i; exact hd)
    (fun i => by fin_cases i; exact hu)
    (fun i => by fin_cases i; exact hv)
    (fun i => by fin_cases i; exact hvc)
    hg hg'

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_globalMeasure_eq_chartMeasure
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartMeasure_absolutelyContinuous
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoData
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoData_weightedIBP
