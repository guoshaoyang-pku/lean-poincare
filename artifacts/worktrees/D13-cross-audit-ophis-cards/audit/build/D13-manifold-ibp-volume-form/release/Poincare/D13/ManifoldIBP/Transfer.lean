/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (manifold IBP layer)

# Conditional transfer: abstract-manifold IBP from the chart-sum layer

The honest conditional assembly that consumes `ChartSumData.globalWeightedIBP`. An
abstract manifold `M` is given as an **explicit interface** `ManifoldAtlasData`: a
finite family of chart parametrizations `chartᵢ : Vec (n+1) → M` (a disjoint atlas),
per-chart metrics `Gᵢ` and drifts `fᵢ`, and the analytic antecedents a genuine
formalization of the Riemannian measure must still construct at the pinned mathlib
revision (which has no manifold Riemannian measure, no integration of forms on
manifolds, and no smooth partition of unity):

* `integral_decomp` — the gluing of the chart measures: the integral over `M` is the
  finite sum of the chart integrals `Σᵢ ∫ g(chartᵢ x) · e^{-fᵢ(x)} · ρᵢ(x) dx`
  (the measure-gluing datum; its density-level content is proved in `Gluing.lean`);
* `weighted_laplacian_compat` / `grad_inner_compat` — the chart identification of the
  manifold-side operators on each parametrization.

With these fields (plus the chartwise regularity/support and integrability
hypotheses, all explicit), the manifold-level weighted integration by parts
`∫_M (Δ_f u) v dm = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} dm` is a **kernel-checked consequence** of the
chart-sum theorem (`manifoldWeightedIBP_of_atlasData`). No integration by parts is
assumed anywhere; each unproved antecedent is recorded in `Blocked.lean` with its
named blocker.

Semantic class: **conditional** — a proved implication over explicit interface
antecedents; the `ChartSumData` model of `ChartSum.lean` is the analytic core this
assembly consumes.
-/
import Poincare.D13.ManifoldIBP.ChartSum

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.ManifoldIBP

variable {n ι : ℕ}

/-- **Manifold atlas datum (conditional interface).** A finite disjoint-atlas manifold
datum on an abstract measurable space `M`. -/
structure ManifoldAtlasData (M : Type*) [MeasurableSpace M] (n ι : ℕ) where
  /-- the manifold (Riemannian/entropy) measure -/
  μ : Measure M
  /-- chart parametrizations `chartᵢ : Vec (n+1) → M` (a disjoint atlas) -/
  chart : Fin ι → Vec (n + 1) → M
  /-- chart metrics -/
  metric : Fin ι → Poincare.D12.VolumeIBP.ChartMetric (n + 1)
  /-- entropy drifts per chart -/
  drift : Fin ι → Vec (n + 1) → ℝ
  /-- **Interface field (B-D13-MANIFOLD-GLUING).** The manifold measure is the glued
  chart measure: for every integrable `g : M → ℝ`,
  `∫_M g dμ = Σᵢ ∫ g(chartᵢ x) · e^{-fᵢ(x)} · ρᵢ(x) dx`. -/
  integral_decomp : ∀ (g : M → ℝ), Integrable g μ →
    (∫ m, g m ∂μ) = ∑ i : Fin ι, ∫ x : Vec (n + 1),
      g (chart i x) * Real.exp (-drift i x) * (metric i).density x
  /-- the manifold-side weighted Laplacian `Δ_f` (drift fixed by the datum) -/
  driftLaplacianM : (M → ℝ) → M → ℝ
  /-- the manifold-side inverse-metric gradient pairing `⟨∇u, ∇v⟩_{g⁻¹}` -/
  gradInnerM : (M → ℝ) → (M → ℝ) → M → ℝ
  /-- **Interface field (B-D13-OPERATOR-COMPAT).** On each parametrization, the
  manifold weighted Laplacian agrees with the chart operator. -/
  weighted_laplacian_compat : ∀ (u : M → ℝ) (i : Fin ι) (x : Vec (n + 1)),
    driftLaplacianM u (chart i x) =
      (metric i).driftLaplacian (drift i) ((fun y => u (chart i y)) : Vec (n + 1) → ℝ) x
  /-- **Interface field (B-D13-OPERATOR-COMPAT).** On each parametrization, the
  manifold gradient pairing agrees with the chart pairing. -/
  grad_inner_compat : ∀ (u v : M → ℝ) (i : Fin ι) (x : Vec (n + 1)),
    gradInnerM u v (chart i x) =
      (metric i).gradInnerInverse ((fun y => u (chart i y)) : Vec (n + 1) → ℝ)
        ((fun y => v (chart i y)) : Vec (n + 1) → ℝ) x

variable {M : Type*} [MeasurableSpace M] (A : ManifoldAtlasData M n ι)

/-- The chart-sum form of the manifold weighted-Laplacian integral (interface
fields only: `integral_decomp` + `weighted_laplacian_compat`). -/
lemma laplacianIntegral_eq_chartSum (u v : M → ℝ)
    (hg : Integrable (fun m : M => A.driftLaplacianM u m * v m) A.μ) :
    (∫ m, A.driftLaplacianM u m * v m ∂A.μ) =
      ({ metric := A.metric } : ChartSumData n ι).globalIntegral A.drift
        (fun i x => ({ metric := A.metric } : ChartSumData n ι).driftLaplacian A.drift
          (fun i => ((fun y => u (A.chart i y)) : Vec (n + 1) → ℝ)) i x *
            v (A.chart i x)) := by
  rw [A.integral_decomp (fun m : M => A.driftLaplacianM u m * v m) hg]
  rw [show (∑ i : Fin ι, ∫ x : Vec (n + 1),
        (A.driftLaplacianM u (A.chart i x) * v (A.chart i x)) * Real.exp (-A.drift i x) *
          (A.metric i).density x) =
      ({ metric := A.metric } : ChartSumData n ι).globalIntegral A.drift
        (fun i x => ({ metric := A.metric } : ChartSumData n ι).driftLaplacian A.drift
          (fun i => ((fun y => u (A.chart i y)) : Vec (n + 1) → ℝ)) i x *
            v (A.chart i x)) by
    simp only [ChartSumData.globalIntegral_def, ChartSumData.driftLaplacian]
    refine Finset.sum_congr rfl ?_
    intro i _
    apply integral_congr_ae
    filter_upwards with x
    rw [A.weighted_laplacian_compat u i x]]

/-- The chart-sum form of the manifold gradient-pairing integral (interface fields
only: `integral_decomp` + `grad_inner_compat`). -/
lemma gradInnerIntegral_eq_chartSum (u v : M → ℝ)
    (hg' : Integrable (fun m : M => A.gradInnerM u v m) A.μ) :
    (∫ m, A.gradInnerM u v m ∂A.μ) =
      ({ metric := A.metric } : ChartSumData n ι).globalIntegral A.drift
        (fun i x => ({ metric := A.metric } : ChartSumData n ι).gradInnerInverse
          (fun i => ((fun y => u (A.chart i y)) : Vec (n + 1) → ℝ))
          (fun i => ((fun y => v (A.chart i y)) : Vec (n + 1) → ℝ)) i x) := by
  rw [A.integral_decomp (fun m : M => A.gradInnerM u v m) hg']
  rw [show (∑ i : Fin ι, ∫ x : Vec (n + 1),
        (A.gradInnerM u v (A.chart i x)) * Real.exp (-A.drift i x) * (A.metric i).density x) =
      ({ metric := A.metric } : ChartSumData n ι).globalIntegral A.drift
        (fun i x => ({ metric := A.metric } : ChartSumData n ι).gradInnerInverse
          (fun i => ((fun y => u (A.chart i y)) : Vec (n + 1) → ℝ))
          (fun i => ((fun y => v (A.chart i y)) : Vec (n + 1) → ℝ)) i x) by
    simp only [ChartSumData.globalIntegral_def, ChartSumData.gradInnerInverse]
    refine Finset.sum_congr rfl ?_
    intro i _
    apply integral_congr_ae
    filter_upwards with x
    rw [A.grad_inner_compat u v i x]]

/-- **Manifold weighted integration by parts (conditional).** From the atlas datum and
the chartwise regularity/support/integrability hypotheses, the manifold identity
`∫_M (Δ_f u) v dm = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} dm` follows — assembled from
`ChartSumData.globalWeightedIBP` through the interface fields. -/
theorem manifoldWeightedIBP_of_atlasData (u v : M → ℝ)
    (hd : ∀ i, ContDiff ℝ 2 (A.drift i))
    (hu : ∀ i, ContDiff ℝ 2 (fun x => u (A.chart i x)))
    (hv : ∀ i, ContDiff ℝ 2 (fun x => v (A.chart i x)))
    (hvc : ∀ i, HasCompactSupport (fun x => v (A.chart i x)))
    (hg : Integrable (fun m : M => A.driftLaplacianM u m * v m) A.μ)
    (hg' : Integrable (fun m : M => A.gradInnerM u v m) A.μ) :
    (∫ m, A.driftLaplacianM u m * v m ∂A.μ) =
      -∫ m, A.gradInnerM u v m ∂A.μ := by
  rw [laplacianIntegral_eq_chartSum A u v hg]
  rw [({ metric := A.metric } : ChartSumData n ι).globalWeightedIBP A.drift
    (fun i => ((fun y => u (A.chart i y)) : Vec (n + 1) → ℝ))
    (fun i => ((fun y => v (A.chart i y)) : Vec (n + 1) → ℝ)) hd hu hv hvc]
  rw [← gradInnerIntegral_eq_chartSum A u v hg']

end Poincare.D13.ManifoldIBP
