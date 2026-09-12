/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (concrete disjoint-atlas model)

# A concrete manifold model: the disjoint atlas with its glued measure

`ManifoldIBP.Transfer` proves the manifold weighted integration by parts from an explicit
atlas interface `ManifoldAtlasData`, whose `integral_decomp` field (the gluing of the
chart measures) is an interface field. This module **inhabits** that interface with a
concrete measure-theoretic model, so the manifold IBP is no longer conditional on an
uninhabited datum:

* `DisjointAtlas n ι = Fin ι × Vec (n+1)` — the disjoint union of `ι` copies of the chart
  (the honest manifold model available at the release pin: no chart overlaps, hence no
  transition functions and no smooth partition of unity are needed);
* `weightedChartMeasure D f i` — the D12 Riemannian measure of chart `i` weighted by the
  entropy density `e^{-f_i}` (`withDensity` of the `ℝ≥0` weight);
* `disjointAtlasMeasure D f = Measure.sum (fun i => (weightedChartMeasure D f i).map (·, ·))`
  — the glued manifold measure;
* `integral_disjointAtlasMeasure` / `integral_weightedChartMeasure` — the chart-sum
  decomposition is **proved** (not assumed), so `integral_decomp` holds for the model;
* `disjointAtlasData` — the `ManifoldAtlasData` instance with the constructed measure;
* `disjointAtlas_weightedIBP` — the weighted IBP on the model, from
  `manifoldWeightedIBP_of_atlasData`.

This closes the *disjoint-atlas* part of blocker `B-D13-MANIFOLD-GLUING` at the release
pin. The genuinely open part is the overlapping-atlas case (chart transitions and smooth
partition of unity), for which the upstream snapshot contains a source-level development
(`MorganTianLib.Ch01.riemannianMeasure`, Lean v4.32.1 / mathlib 520045ab) not ported here.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.Transfer

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.ManifoldIBP

variable {n ι : ℕ}

/-- **The concrete disjoint-atlas manifold model**: `ι` disjoint copies of the chart
`Vec (n+1)`, indexed as the product `Fin ι × Vec (n+1)`. -/
abbrev DisjointAtlas (n ι : ℕ) := Fin ι × Vec (n + 1)

/-- **The weighted chart measure** `e^{-f_i} dvol_i`: the D12 Riemannian measure of
chart `i` with the entropy weight. The weight is inserted as an `ℝ≥0` function so that
`integral_withDensity_eq_integral_smul₀` applies directly. -/
def weightedChartMeasure (D : ChartSumData n ι) (f : Fin ι → Vec (n + 1) → ℝ) (i : Fin ι) :
    Measure (Vec (n + 1)) :=
  (D.metric i).riemannianMeasure.withDensity
    (fun x => ((Real.toNNReal (Real.exp (-(f i x))) : NNReal) : ℝ≥0∞))

/-- **The chart measure is the weighted chart integral**: `∫ g d(e^{-f_i} dvol_i) =
∫ g · e^{-f_i} · ρ_i dx`, the measure/geometry bridge identity of D12 composed with the
`withDensity` weight. -/
theorem integral_weightedChartMeasure (D : ChartSumData n ι) (f : Fin ι → Vec (n + 1) → ℝ)
    (hf : ∀ i, Measurable (f i)) (i : Fin ι) (g : Vec (n + 1) → ℝ) :
    ∫ x, g x ∂(weightedChartMeasure D f i) =
      ∫ x, g x * Real.exp (-(f i x)) * (D.metric i).density x := by
  have hmeas : AEMeasurable (fun x : Vec (n + 1) => Real.toNNReal (Real.exp (-(f i x))))
      (D.metric i).riemannianMeasure := by
    exact (measurable_real_toNNReal.comp (Real.measurable_exp.comp ((hf i).neg))).aemeasurable.mono_ac
      (D.metric i).riemannianMeasure_absolutelyContinuous
  rw [weightedChartMeasure, integral_withDensity_eq_integral_smul₀ hmeas g]
  rw [show (fun x : Vec (n + 1) => Real.toNNReal (Real.exp (-(f i x))) • g x) =
      fun x => Real.exp (-(f i x)) * g x by
    funext x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _))]
    rfl]
  rw [(D.metric i).integral_riemannianMeasure_eq (fun x => Real.exp (-(f i x)) * g x)]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- **The glued measure of the disjoint atlas**: the sum of the chart measures pushed to
the disjoint union. -/
def disjointAtlasMeasure (D : ChartSumData n ι) (f : Fin ι → Vec (n + 1) → ℝ) :
    Measure (DisjointAtlas n ι) :=
  Measure.sum (fun i => (weightedChartMeasure D f i).map (fun x => (i, x)))

/-- **Chart-sum decomposition of the glued measure** (the `integral_decomp` field for the
concrete model): the integral over the disjoint atlas is the finite sum of the chart
integrals. Proved from `integral_sum_measure` + `MeasurableEmbedding.integral_map`, with
the integrability hypothesis the D12/D13 transfer already carries. -/
theorem integral_disjointAtlasMeasure (D : ChartSumData n ι)
    (f : Fin ι → Vec (n + 1) → ℝ) (g : DisjointAtlas n ι → ℝ)
    (hg : Integrable g (disjointAtlasMeasure D f)) :
    ∫ m, g m ∂(disjointAtlasMeasure D f) =
      ∑ i, ∫ x, g (i, x) ∂(weightedChartMeasure D f i) := by
  rw [disjointAtlasMeasure, integral_sum_measure hg, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact MeasurableEmbedding.integral_map
    (MeasurableEmbedding.prodMk_left i MeasurableEmbedding.id) g

/-- **The `ManifoldAtlasData` instance of the disjoint-atlas model.** The measure is the
constructed glued measure, the charts are the canonical inclusions, the manifold operators
are the chart operators read on the corresponding component, and `integral_decomp` is
*proved* (`integral_disjointAtlasMeasure` + `integral_weightedChartMeasure`) rather than
assumed. Only the measurability of the drifts is required. -/
def disjointAtlasData (D : ChartSumData n ι) (f : Fin ι → Vec (n + 1) → ℝ)
    (hf : ∀ i, Measurable (f i)) : ManifoldAtlasData (DisjointAtlas n ι) n ι where
  μ := disjointAtlasMeasure D f
  chart i x := (i, x)
  metric := D.metric
  drift := f
  integral_decomp := by
    intro g hg
    rw [integral_disjointAtlasMeasure D f g hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_weightedChartMeasure D f hf i (fun x => g (i, x))]
  driftLaplacianM u m := D.driftLaplacian f (fun i x => u (i, x)) m.1 m.2
  gradInnerM u v m := D.gradInnerInverse (fun i x => u (i, x)) (fun i x => v (i, x)) m.1 m.2
  weighted_laplacian_compat := by
    intro u i x
    rfl
  grad_inner_compat := by
    intro u v i x
    rfl

/-! ## Discharging the model's integrability hypotheses

The transfer theorem carries integrability of the two manifold integrands as explicit
analytic input. For the concrete model these are *theorems*: the chart integrands are
continuous (D12 `driftLaplacian_continuous` / `gradInnerInverse_continuous`, the densities,
and `exp`) with compact support (carried by `v`), hence Lebesgue-integrable, and
integrability transfers through `withDensity` and through the glued sum measure. -/

/-- **Chartwise integrability of `(Δ_f u)·v`.** For `C²` `f,u,v` with `v` compactly supported,
the drift-Laplacian integrand is integrable against the weighted chart measure. -/
theorem integrable_driftLaplacian_mul_weightedChartMeasure (D : ChartSumData n ι)
    (f u v : Fin ι → Vec (n + 1) → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (hv : ∀ i, ContDiff ℝ 2 (v i))
    (hvc : ∀ i, HasCompactSupport (v i)) (i : Fin ι) :
    Integrable (fun x => (D.metric i).driftLaplacian (f i) (u i) x * v i x)
      (weightedChartMeasure D f i) := by
  have hmeasNN : Measurable (fun x : Vec (n + 1) => Real.toNNReal (Real.exp (-(f i x)))) :=
    measurable_real_toNNReal.comp (Real.measurable_exp.comp ((hf i).continuous.neg.measurable))
  have hcont : Continuous ((fun x : Vec (n + 1) =>
      (D.metric i).driftLaplacian (f i) (u i) x * Real.exp (-(f i x)) *
        (D.metric i).density x) * (v i)) :=
    ((((D.metric i).driftLaplacian_continuous (f i) (u i) (hf i) (hu i)).mul
      (Real.continuous_exp.comp ((hf i).continuous.neg))).mul
        (D.metric i).density_continuous).mul (hv i).continuous
  have hcs : HasCompactSupport ((fun x : Vec (n + 1) =>
      (D.metric i).driftLaplacian (f i) (u i) x * Real.exp (-(f i x)) *
        (D.metric i).density x) * (v i)) :=
    (hvc i).mul_left
  have hvol : Integrable ((fun x : Vec (n + 1) =>
      (D.metric i).driftLaplacian (f i) (u i) x * Real.exp (-(f i x)) *
        (D.metric i).density x) * (v i)) volume :=
    hcont.integrable_of_hasCompactSupport hcs
  show Integrable (fun x => (D.metric i).driftLaplacian (f i) (u i) x * v i x)
    ((D.metric i).riemannianMeasure.withDensity
      (fun x => ((Real.toNNReal (Real.exp (-(f i x))) : NNReal) : ℝ≥0∞)))
  rw [Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_def]
  rw [integrable_withDensity_iff_integrable_smul hmeasNN]
  rw [integrable_withDensity_iff_integrable_smul (D.metric i).densityNNReal_measurable]
  refine hvol.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, NNReal.smul_def, Poincare.D12.VolumeIBP.ChartMetric.densityNNReal_eq,
    Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _)), smul_eq_mul]
  ring

/-- **Chartwise integrability of `⟨∇u,∇v⟩`.** For `C²` `u,v` with `v` compactly supported, the
gradient-pairing integrand is integrable against the weighted chart measure. -/
theorem integrable_gradInner_mul_weightedChartMeasure (D : ChartSumData n ι)
    (f u v : Fin ι → Vec (n + 1) → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (hv : ∀ i, ContDiff ℝ 2 (v i))
    (hvc : ∀ i, HasCompactSupport (v i)) (i : Fin ι) :
    Integrable (fun x => (D.metric i).gradInnerInverse (u i) (v i) x)
      (weightedChartMeasure D f i) := by
  have hmeasNN : Measurable (fun x : Vec (n + 1) => Real.toNNReal (Real.exp (-(f i x)))) :=
    measurable_real_toNNReal.comp (Real.measurable_exp.comp ((hf i).continuous.neg.measurable))
  -- the pairing is compactly supported because `∇v` is (D12 `grad_hasCompactSupport`)
  have hcs : HasCompactSupport (fun x : Vec (n + 1) =>
      (D.metric i).gradInnerInverse (u i) (v i) x) := by
    refine HasCompactSupport.mono ((D.metric i).grad_hasCompactSupport (v i) (hvc i)) ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hgrad
    exact hx (by
      rw [Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse_eq_sum]
      simp [hgrad])
  have hcont : Continuous ((fun x : Vec (n + 1) =>
      Real.exp (-(f i x)) * (D.metric i).density x) *
        (fun x => (D.metric i).gradInnerInverse (u i) (v i) x)) :=
    ((Real.continuous_exp.comp ((hf i).continuous.neg)).mul
      (D.metric i).density_continuous).mul
        ((D.metric i).gradInnerInverse_continuous (u i) (v i) (hu i) (hv i))
  have hvol : Integrable ((fun x : Vec (n + 1) =>
      Real.exp (-(f i x)) * (D.metric i).density x) *
        (fun x => (D.metric i).gradInnerInverse (u i) (v i) x)) volume :=
    hcont.integrable_of_hasCompactSupport hcs.mul_left
  show Integrable (fun x => (D.metric i).gradInnerInverse (u i) (v i) x)
    ((D.metric i).riemannianMeasure.withDensity
      (fun x => ((Real.toNNReal (Real.exp (-(f i x))) : NNReal) : ℝ≥0∞)))
  rw [Poincare.D12.VolumeIBP.ChartMetric.riemannianMeasure_def]
  rw [integrable_withDensity_iff_integrable_smul hmeasNN]
  rw [integrable_withDensity_iff_integrable_smul (D.metric i).densityNNReal_measurable]
  refine hvol.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, NNReal.smul_def, Poincare.D12.VolumeIBP.ChartMetric.densityNNReal_eq,
    Real.coe_toNNReal _ (le_of_lt (Real.exp_pos _)), smul_eq_mul]
  ring

/-- **Integrability of the drift-Laplacian integrand against the glued measure**: transferred
from the chartwise statement through the sum measure and the measurable embeddings. -/
theorem integrable_driftLaplacian_mul_disjointAtlasMeasure (D : ChartSumData n ι)
    (f u v : Fin ι → Vec (n + 1) → ℝ) (hm : ∀ i, Measurable (f i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    Integrable (fun m : DisjointAtlas n ι =>
      (disjointAtlasData D f hm).driftLaplacianM (fun m => u m.1 m.2) m *
        (fun m => v m.1 m.2) m) (disjointAtlasMeasure D f) := by
  rw [disjointAtlasMeasure, integrable_sum_measure_iff]
  refine ⟨fun i => ?_, Summable.of_finite⟩
  have hemb : MeasurableEmbedding (fun x : Vec (n + 1) => (i, x)) :=
    MeasurableEmbedding.prodMk_left i MeasurableEmbedding.id
  rw [hemb.integrable_map_iff]
  exact integrable_driftLaplacian_mul_weightedChartMeasure D f u v hf hu hv hvc i

/-- **Integrability of the gradient-pairing integrand against the glued measure.** -/
theorem integrable_gradInner_mul_disjointAtlasMeasure (D : ChartSumData n ι)
    (f u v : Fin ι → Vec (n + 1) → ℝ) (hm : ∀ i, Measurable (f i))
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    Integrable (fun m : DisjointAtlas n ι =>
      (disjointAtlasData D f hm).gradInnerM (fun m => u m.1 m.2) (fun m => v m.1 m.2) m)
      (disjointAtlasMeasure D f) := by
  rw [disjointAtlasMeasure, integrable_sum_measure_iff]
  refine ⟨fun i => ?_, Summable.of_finite⟩
  have hemb : MeasurableEmbedding (fun x : Vec (n + 1) => (i, x)) :=
    MeasurableEmbedding.prodMk_left i MeasurableEmbedding.id
  rw [hemb.integrable_map_iff]
  exact integrable_gradInner_mul_weightedChartMeasure D f u v hf hu hv hvc i

/-- **Manifold weighted IBP for the concrete model, with the integrability inputs discharged.**
The atlas datum is constructed (`disjointAtlasData`), the glued measure is genuine, and the two
integrability hypotheses of the transfer are proved from chartwise continuity + compact support
(`integrable_driftLaplacian_mul_disjointAtlasMeasure` /
`integrable_gradInner_mul_disjointAtlasMeasure`). The remaining hypotheses are the honest
analytic ones: chartwise `C²` data with compactly supported test functions and measurable drifts. -/
theorem disjointAtlas_weightedIBP (D : ChartSumData n ι) (f u v : Fin ι → Vec (n + 1) → ℝ)
    (hm : ∀ i, Measurable (f i))
    (hd : ∀ i, ContDiff ℝ 2 (f i)) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    (∫ m, (disjointAtlasData D f hm).driftLaplacianM (fun m => u m.1 m.2) m *
        (fun m => v m.1 m.2) m ∂(disjointAtlasData D f hm).μ) =
      -∫ m, (disjointAtlasData D f hm).gradInnerM (fun m => u m.1 m.2)
        (fun m => v m.1 m.2) m ∂(disjointAtlasData D f hm).μ := by
  refine manifoldWeightedIBP_of_atlasData (disjointAtlasData D f hm)
    (fun m : DisjointAtlas n ι => u m.1 m.2) (fun m : DisjointAtlas n ι => v m.1 m.2)
    ?_ ?_ ?_ ?_
    (integrable_driftLaplacian_mul_disjointAtlasMeasure D f u v hm hd hu hv hvc)
    (integrable_gradInner_mul_disjointAtlasMeasure D f u v hm hd hu hv hvc)
  · intro i
    exact hd i
  · intro i
    exact hu i
  · intro i
    exact hv i
  · intro i
    exact hvc i

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.DisjointAtlas
#print axioms Poincare.D13.ManifoldIBP.weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integral_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.integral_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlasData
#print axioms Poincare.D13.ManifoldIBP.integrable_driftLaplacian_mul_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_gradInner_mul_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_driftLaplacian_mul_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_gradInner_mul_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlas_weightedIBP
