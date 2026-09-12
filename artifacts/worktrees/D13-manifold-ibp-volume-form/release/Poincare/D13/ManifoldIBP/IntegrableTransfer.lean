/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (integrability transfer for the atlas measure)

# Integrability transfer for the global Riemannian measure

The global integration-by-parts theorems of `ManifoldIBP.POUAssemblyAE` and
`ManifoldIBP.SmoothAtlasPartialAE` take the integrability of the constructed lifted pieces as
explicit hypotheses. That is the honest interface for arbitrary atlas data, because the glued
measure `globalMeasure` is a countable sum of chart measures and need not be locally finite for
an arbitrary countable atlas.

For a function **supported in one chart image** the situation is different: the global measure
agrees with that chart's measure on the chart image
(`globalMeasure_restrict_eq_chartMeasure`), so integrability against the weighted global measure
is equivalent to integrability of the chart expression against the reference measure. This module
proves that equivalence:

* `integrable_chartMeasure_iff` — integrability against the `i`-chart measure is integrability of
  `y ↦ g (chart i y) * ρ_i(y)` against the reference measure restricted to the chart source
  (`integrable_map_measure` + `integrable_withDensity_iff_integrable_smul₀'`);
* `integrable_globalMeasure_iff` — for a chart-supported function, the global measure may be
  replaced by the chart measure (`globalMeasure_restrict_eq_chartMeasure`);
* **`integrable_globalMeasure_withDensity_of_supported`** — the entropy-weighted form: a
  chart-supported function is integrable for `(globalMeasure μ).withDensity (e^{-f})` as soon as
  its weighted chart expression is integrable against `μ`.

Consequences: the integrability hypotheses of the POU/atlas IBP theorems are discharged for
compactly supported smooth pieces (their chart expressions are continuous with compact support),
so the model instances become unconditional.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBP

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

namespace OverlapAtlas

variable (A : OverlapAtlas M (n + 1))

/-- **Integrability read in a chart.** For a function on the manifold, integrability against the
`i`-chart measure is equivalent to integrability of its chart expression
`y ↦ g (chart i y) * ρ_i(y)` against the reference measure restricted to the chart source. -/
theorem integrable_chartMeasure_iff (μ : Measure (Vec (n + 1))) (i : ℕ) {g : M → ℝ}
    (hg : AEStronglyMeasurable g (A.chartMeasure μ i)) :
    Integrable g (A.chartMeasure μ i) ↔
      Integrable (fun y => g (A.chart i y) * A.density i y) (μ.restrict (A.source i)) := by
  have hchart : AEMeasurable (A.chart i)
      ((μ.restrict (A.source i)).withDensity (fun y => ENNReal.ofReal (A.density i y))) :=
    (A.measurable_chart i).aemeasurable
  have hdens : AEMeasurable (fun y => ENNReal.ofReal (A.density i y))
      (μ.restrict (A.source i)) :=
    (ENNReal.measurable_ofReal.comp
      (A.metric i).density_contDiff_one.continuous.measurable).aemeasurable
  rw [chartMeasure, integrable_map_measure hg hchart,
    integrable_withDensity_iff_integrable_smul₀' hdens
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards with y
  rw [Function.comp_apply, ENNReal.toReal_ofReal (A.density_nonneg i y), smul_eq_mul]
  ring

/-- **Integrability transfer from a chart to the global measure.** A function supported in the
image of the `i`-th chart is integrable for the global measure iff it is integrable for that
chart measure. This is the chart-independence theorem `globalMeasure_restrict_eq_chartMeasure`
read as an integrability statement. -/
theorem integrable_globalMeasure_iff (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure] (i : ℕ)
    {g : M → ℝ} (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i) :
    Integrable g (A.globalMeasure μ) ↔ Integrable g (A.chartMeasure μ i) := by
  have hs : MeasurableSet (A.chart i '' A.source i) := A.measurableSet_image i
  have hind : (A.chart i '' A.source i).indicator g = g := by
    funext m
    by_cases hm : m ∈ A.chart i '' A.source i
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
      by_contra hne
      exact hm (hsupp m fun h => hne h.symm)
  rw [← hind, integrable_indicator_iff hs, integrable_indicator_iff hs]
  show Integrable g ((A.globalMeasure μ).restrict (A.chart i '' A.source i)) ↔
    Integrable g ((A.chartMeasure μ i).restrict (A.chart i '' A.source i))
  rw [A.globalMeasure_restrict_eq_chartMeasure μ i]

/-- **Integrability transfer for the entropy-weighted global measure.** A function supported in
the image of the `i`-th chart is integrable for `(globalMeasure μ).withDensity (e^{-f})` as soon
as its weighted chart expression `y ↦ e^{-f(chart i y)} · g(chart i y) · ρ_i(y)` is integrable
against `μ`. All the manifold-measure content is the chart-independence theorem; the weight is
handled by `integrable_withDensity_iff_integrable_smul₀'`. -/
theorem integrable_globalMeasure_withDensity_of_supported
    (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure] (i : ℕ) {f g : M → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hint : Integrable (fun y => Real.exp (-(f (A.chart i y))) * g (A.chart i y)
      * A.density i y) μ) :
    Integrable g ((A.globalMeasure μ).withDensity (A.weight f)) := by
  rw [integrable_withDensity_iff_integrable_smul₀' (A.measurable_weight hf).aemeasurable
    (ae_of_all _ fun m => A.weight_lt_top f m)]
  have hmeas : Measurable (fun m : M => (A.weight f m).toReal • g m) :=
    (ENNReal.measurable_toReal.comp (A.measurable_weight hf)).mul hg
  have hsupp' : ∀ m, (A.weight f m).toReal • g m ≠ 0 → m ∈ A.chart i '' A.source i :=
    fun m hm => hsupp m fun h0 => hm (by rw [h0, smul_zero])
  rw [A.integrable_globalMeasure_iff μ i hsupp',
    A.integrable_chartMeasure_iff μ i hmeas.aestronglyMeasurable]
  refine (hint.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards with y
  rw [A.weight_toReal, smul_eq_mul]

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_chartMeasure_iff
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_iff
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_withDensity_of_supported
