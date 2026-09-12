/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (volume form ↔ global measure bridge)

# The overlapping-atlas measure is the measure induced by the chart volume forms

`ManifoldIBP.GlobalMeasure` constructs the Riemannian measure of an overlapping atlas from
the chart densities `√(det gᵢⱼ)`, and proves that it is computed by that density in *every*
chart. `VolumeForm.Basic` constructs the **Riemannian volume form**
`ω_G(x) = √(det g(x)) · ω_std` and proves that it takes the value `√(det g(x))` on the
standard coordinate frame.

This module ties the two layers together: the global measure of the atlas is the measure
induced by the chart volume forms, i.e. its value on a measurable set contained in a chart
image is the integral of `|ω_{gᵢ}(y)(∂₁,…,∂_d)|` over the coordinate image — because the
volume form on the coordinate frame is exactly the Riemannian density. In particular the
"volume form" and "density" presentations of the Riemannian measure agree on the whole
overlapping atlas, not only chartwise.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.VolumeForm.Basic

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {M : Type*} [MeasurableSpace M] {d : ℕ}

/-- The chart volume form on the standard coordinate frame is the Riemannian density:
`ω_{gᵢ}(y)(∂₁,…,∂_d) = √(det gᵢ(y))`. -/
theorem chartVolumeForm_stdFrame_eq_density (A : OverlapAtlas M d) (i : ℕ) (y : Vec d) :
    (Poincare.D13.VolumeForm.chartVolumeForm (A.metric i) y) (Poincare.D13.VolumeForm.Vec.stdFrame d) = A.density i y := by
  rw [Poincare.D13.VolumeForm.chartVolumeForm_apply, Poincare.D13.VolumeForm.Vec.matrix_of_stdFrame, Matrix.det_one, mul_one]
  rfl

/-- **The global measure is the measure induced by the chart volume forms.** For a measurable
set contained in the `i`-th chart image, the Riemannian measure of the overlapping atlas is
the integral of the absolute value of the chart volume form on the coordinate frame over the
coordinate image. This is `globalMeasure_apply_chart` with the density identified as the
volume form on the coordinate frame, so the volume-form and density presentations agree. -/
theorem globalMeasure_apply_chart_volumeForm (A : OverlapAtlas M d) (μ : Measure (Vec d))
    [μ.IsAddHaarMeasure] (i : ℕ) {s : Set M} (hs : MeasurableSet s)
    (hsi : s ⊆ A.chart i '' A.source i) :
    A.globalMeasure μ s
      = ∫⁻ y in A.chartPreimage i s,
          ENNReal.ofReal |(Poincare.D13.VolumeForm.chartVolumeForm (A.metric i) y) (Poincare.D13.VolumeForm.Vec.stdFrame d)| ∂μ := by
  rw [A.globalMeasure_apply_chart μ i hs hsi]
  refine setLIntegral_congr_fun (A.measurableSet_chartPreimage i hs) fun y _ => ?_
  rw [A.chartVolumeForm_stdFrame_eq_density i y, abs_of_pos (A.density_pos i y)]

/-- **The one-chart case in volume-form form**: when a chart covers the manifold, the global
measure of any measurable set is the integral of the chart volume form on the coordinate
frame. -/
theorem globalMeasure_apply_volumeForm_of_cover (A : OverlapAtlas M d) (μ : Measure (Vec d))
    [μ.IsAddHaarMeasure] (i : ℕ) (hi : A.chart i '' A.source i = univ) {s : Set M}
    (hs : MeasurableSet s) :
    A.globalMeasure μ s
      = ∫⁻ y in A.chartPreimage i s,
          ENNReal.ofReal |(Poincare.D13.VolumeForm.chartVolumeForm (A.metric i) y) (Poincare.D13.VolumeForm.Vec.stdFrame d)| ∂μ :=
  A.globalMeasure_apply_chart_volumeForm μ i hs (fun _ _ => by rw [hi]; exact mem_univ _)


/-- **Total volume of the model atlas.** The Riemannian volume of the whole model manifold is
the integral of the density `√(det G)` (equivalently of the volume form on the coordinate
frame), computed in the unit chart. -/
theorem dilationAtlasTwo_volume_univ (G : ChartMetric (n + 1)) :
    (dilationAtlasTwo n G).globalMeasure volume univ
      = ∫⁻ y, ENNReal.ofReal (G.density y) ∂volume := by
  have h := (dilationAtlasTwo n G).globalMeasure_apply_chart_volumeForm volume 0
    MeasurableSet.univ (fun _ _ => by
      rw [dilationAtlasTwo_image_zero]
      exact mem_univ _)
  rw [h]
  have hpre : (dilationAtlasTwo n G).chartPreimage 0 univ = univ := by
    show (dilationAtlasTwo n G).source 0 ∩ (dilationAtlasTwo n G).chart 0 ⁻¹' univ = univ
    rw [Set.preimage_univ, Set.inter_univ]
    rfl
  rw [hpre, setLIntegral_univ]
  refine lintegral_congr fun y => ?_
  rw [dilationAtlasTwo_metric_zero]
  have hdens : (Poincare.D13.VolumeForm.chartVolumeForm G y)
      (Poincare.D13.VolumeForm.Vec.stdFrame (n + 1)) = G.density y := by
    rw [Poincare.D13.VolumeForm.chartVolumeForm_apply,
      Poincare.D13.VolumeForm.Vec.matrix_of_stdFrame, Matrix.det_one, mul_one]
  rw [hdens, abs_of_pos (G.density_pos y)]

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartVolumeForm_stdFrame_eq_density
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_chart_volumeForm
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_volumeForm_of_cover
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_volume_univ
