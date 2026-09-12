/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (manifold IBP layer)

# The manifold integration-by-parts layer: the disjoint chart-sum model

This module assembles the **manifold-level** integration-by-parts identities from the
D12 chart theorems, on the honest model available at the release pin: the **disjoint
chart sum** `M = ⨿ᵢ Uᵢ`, where each chart domain is the full model space `Vec (n+1)`
with its own chart metric `Gᵢ` (a `ChartSumData`). The global objects are defined
chartwise, and the global integral is the finite sum of the chart integrals:

`∫_M f dm := ∑ᵢ ∫ f(i, x) · e^{-fᵢ(x)} · ρᵢ(x) dx`   with `ρᵢ = √(det gᵢ)`.

Everything below is kernel-checked from the D12 chart theorems by finite linearity; no
gluing, atlas transition or quotient identification is assumed (the chart-sum has no
overlaps to identify — the identification datum is the explicit interface of
`Transfer.lean`, and the named blockers live in `Blocked.lean`):

* `globalWeightedIBP` — the global weighted integration by parts
  `∫_M (Δ_f u) v dm = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} dm` for chartwise `C² f, u, v` with each `vᵢ`
  compactly supported — the manifold-level form of D7's `WeightedIBPStatement`,
  assembled from `ChartMetric.chart_weighted_ibp` (D12 `IBP.lean`);
* `globalLaplacianIntegralZero` — `∫_M Δ_g v dm = 0` for compactly supported `C² v`
  (from D12 `laplacian_integral_eq_zero`);
* `globalDivergenceIntegralZero` — `∫_M div_g X dm = 0` for compactly supported `C¹ X`
  (from D12 `divergence_integral_eq_zero`);
* `globalUnweightedIBP` — the unweighted form `∫_M u Δ_g v dm = -∫_M ⟨∇u,∇v⟩_{g⁻¹} dm`
  (from D12 `chart_ibp`).

Semantic class: **model** — the disjoint chart sum of a Riemannian metric family; the
transfer to a genuine closed manifold is the conditional assembly of `Transfer.lean`.
-/
import Poincare.D12.VolumeIBP.Blocked
import Poincare.D13.VolumeForm.Gluing

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.ManifoldIBP

/-- The chart vector space (D12). -/
abbrev Vec (d : ℕ) := Poincare.D12.VolumeIBP.Vec d

/-- **Chart-sum datum.** A finite family of chart metrics `Gᵢ : ChartMetric (n+1)` with
drifts `fᵢ` (the entropy weights `e^{-fᵢ}`), on the disjoint chart sum `M = ⨿ᵢ Uᵢ`. -/
structure ChartSumData (n ι : ℕ) where
  /-- the metric of chart `i` -/
  metric : Fin ι → Poincare.D12.VolumeIBP.ChartMetric (n + 1)

namespace ChartSumData

variable {n ι : ℕ} (D : ChartSumData n ι)

/-- The chart-sum Riemannian density `ρ(i, x) = √(det gᵢ(x))`. -/
def density (i : Fin ι) (x : Vec (n + 1)) : ℝ :=
  (D.metric i).density x

/-- The chart-sum density is positive. -/
lemma density_pos (i : Fin ι) (x : Vec (n + 1)) : 0 < D.density i x :=
  (D.metric i).density_pos x

/-- The chart-sum drift-weighted Laplacian: `Δ_f u (i, x) = Δ_{gᵢ} uᵢ - ⟨∇fᵢ, ∇uᵢ⟩_{gᵢ⁻¹}`. -/
def driftLaplacian (f u : Fin ι → Vec (n + 1) → ℝ) (i : Fin ι) (x : Vec (n + 1)) : ℝ :=
  (D.metric i).driftLaplacian (f i) (u i) x

/-- The chart-sum inverse-metric gradient pairing
`⟨∇u, ∇v⟩_{g⁻¹}(i, x) = Σ j k, gᵢ(x)⁻¹ j k · ∂ⱼuᵢ(x) · ∂ₖvᵢ(x)`. -/
def gradInnerInverse (u v : Fin ι → Vec (n + 1) → ℝ) (i : Fin ι) (x : Vec (n + 1)) : ℝ :=
  (D.metric i).gradInnerInverse (u i) (v i) x

/-- The chart-sum metric Laplacian `Δ_{gᵢ} uᵢ`. -/
def laplacian (u : Fin ι → Vec (n + 1) → ℝ) (i : Fin ι) (x : Vec (n + 1)) : ℝ :=
  (D.metric i).laplacian (u i) x

/-- The chart-sum divergence `div_{gᵢ} Xᵢ`. -/
def divergence (X : Fin ι → Vec (n + 1) → Vec (n + 1)) (i : Fin ι) (x : Vec (n + 1)) : ℝ :=
  (D.metric i).divergence (X i) x

/-- **The chart-sum integral (weighted).** The global integral on the disjoint chart
sum `M = ⨿ᵢ Uᵢ` with the entropy measure `dm = e^{-fᵢ} ρᵢ dx` on chart `i` (the drift
`f` is the datum of the entropy measure, exactly as in the D12 chart theorems):
`∫_M g dm = Σᵢ ∫ g(i, x) · e^{-fᵢ(x)} · ρᵢ(x) dx`. -/
def globalIntegral (f g : Fin ι → Vec (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin ι, ∫ x : Vec (n + 1), g i x * Real.exp (-f i x) * (D.metric i).density x

/-- The chart-sum integral expands as a finite sum of chart integrals. -/
@[simp] lemma globalIntegral_def (f g : Fin ι → Vec (n + 1) → ℝ) :
    D.globalIntegral f g = ∑ i : Fin ι, ∫ x : Vec (n + 1),
      g i x * Real.exp (-f i x) * (D.metric i).density x := rfl

/-- **The chart-sum integral (unweighted).** `∫_M g dvol = Σᵢ ∫ g(i, x) · ρᵢ(x) dx`
(the Riemannian measure without entropy weight). -/
def globalIntegralUnweighted (g : Fin ι → Vec (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin ι, ∫ x : Vec (n + 1), g i x * (D.metric i).density x

/-- **Global weighted integration by parts (manifold-level `WeightedIBPStatement`).**
On the disjoint chart sum, for chartwise `C² f, u, v` with each `vᵢ` compactly
supported,
`∫_M (Δ_f u) · v dm = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} dm`.
Assembled from the D12 chart theorem `chart_weighted_ibp` by finite linearity of the
chart-sum integral; no integration by parts is assumed. -/
theorem globalWeightedIBP (f u v : Fin ι → Vec (n + 1) → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    D.globalIntegral f (fun i x => D.driftLaplacian f u i x * v i x) =
      - D.globalIntegral f (fun i x => D.gradInnerInverse u v i x) := by
  simp only [globalIntegral_def, driftLaplacian, gradInnerInverse]
  rw [show (∑ i : Fin ι, ∫ x : Vec (n + 1),
        (D.metric i).driftLaplacian (f i) (u i) x * v i x * Real.exp (-f i x) *
          (D.metric i).density x) =
      ∑ i : Fin ι, -∫ x : Vec (n + 1), ((D.metric i).gradInnerInverse (u i) (v i) x *
          Real.exp (-f i x) * (D.metric i).density x) by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (D.metric i).chart_weighted_ibp (f i) (u i) (v i) (hf i) (hu i) (hv i) (hvc i)]
  rw [Finset.sum_neg_distrib]

/-- **Global Laplacian integral vanishes.** `∫_M Δ_g v dvol = 0` for chartwise `C² v`
with compactly supported charts (D12 `laplacian_integral_eq_zero` per chart). -/
theorem globalLaplacianIntegralZero (v : Fin ι → Vec (n + 1) → ℝ)
    (hv : ∀ i, ContDiff ℝ 2 (v i)) (hvc : ∀ i, HasCompactSupport (v i)) :
    D.globalIntegralUnweighted (fun i x => D.laplacian v i x) = 0 := by
  unfold globalIntegralUnweighted laplacian
  refine Finset.sum_eq_zero ?_
  intro i _
  exact (D.metric i).laplacian_integral_eq_zero (v i) (hv i) (hvc i)

/-- **Global divergence integral vanishes.** `∫_M div_g X dvol = 0` for chartwise `C¹ X`
with compactly supported charts (D12 `divergence_integral_eq_zero` per chart,
transferred from the Riemannian-measure form by `integral_riemannianMeasure_eq`). -/
theorem globalDivergenceIntegralZero (X : Fin ι → Vec (n + 1) → Vec (n + 1))
    (hX : ∀ i, ContDiff ℝ 1 (X i)) (hXc : ∀ i, HasCompactSupport (X i)) :
    D.globalIntegralUnweighted (fun i x => D.divergence X i x) = 0 := by
  unfold globalIntegralUnweighted divergence
  refine Finset.sum_eq_zero ?_
  intro i _
  have hdiv := (D.metric i).divergence_integral_eq_zero (X i) (hX i) (hXc i)
  rw [← (D.metric i).integral_riemannianMeasure_eq (fun x : Vec (n + 1) => (D.metric i).divergence (X i) x)]
  exact hdiv

/-- **Global (unweighted) integration by parts.** `∫_M u Δ_g v dvol = -∫_M ⟨∇u,∇v⟩_{g⁻¹} dvol`
for chartwise `C² u, v` with compactly supported charts (D12 `chart_ibp` per chart). -/
theorem globalUnweightedIBP (u v : Fin ι → Vec (n + 1) → ℝ)
    (hu : ∀ i, ContDiff ℝ 2 (u i)) (hv : ∀ i, ContDiff ℝ 2 (v i))
    (huc : ∀ i, HasCompactSupport (u i)) :
    D.globalIntegralUnweighted (fun i x => u i x * D.laplacian v i x) =
      - D.globalIntegralUnweighted (fun i x => D.gradInnerInverse u v i x) := by
  unfold globalIntegralUnweighted laplacian gradInnerInverse
  rw [show (∑ i : Fin ι, ∫ x : Vec (n + 1),
        u i x * (D.metric i).laplacian (v i) x * (D.metric i).density x) =
      ∑ i : Fin ι, -∫ x : Vec (n + 1), ((D.metric i).gradInnerInverse (u i) (v i) x *
          (D.metric i).density x) by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (D.metric i).chart_ibp (u i) (v i) (hu i) (hv i) (huc i)]
  rw [Finset.sum_neg_distrib]

end ChartSumData

end Poincare.D13.ManifoldIBP
