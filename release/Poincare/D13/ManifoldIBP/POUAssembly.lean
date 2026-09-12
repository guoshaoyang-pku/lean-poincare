/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (partition-of-unity assembly of the global IBP)

# Global integration by parts from a smooth partition of unity

`ManifoldIBP.SmoothPartition` constructs a smooth partition of unity on the Euclidean model
space subordinate to a finite open cover of a compact set, and `ManifoldIBP.GlobalIBP` assembles
the global weighted IBP from a finite chart-supported decomposition. This module connects the
two: given **partition-of-unity functions `ψ_j` in a base chart `b`** and global functions `v_j`
whose `b`-chart expressions are `ψ_j · (v ∘ chart_b)`, the global test function `v` really is the
finite sum `Σ_j v_j` (this is the pointwise decomposition lemma `eq_sum_of_pou`), so the chart
theorem can be applied to each piece and summed.

The hypotheses on the pieces are exactly the chart-level data of the atlas layer: support in the
image of `chartOf j`, `C²` and compact support of the chart expression, and the chart
identification of the operators `Du` (drift Laplacian) and `Guv_j` (inverse-metric pairing with
the piece). The piece pairings `Guv_j` are *given*; identifying `Σ_j Guv_j` with the pairing of
the *whole* test function is the first-order chart-independence statement proved in
`Riemannian.AtlasPairing` (`OverlapAtlas.gradInnerInverse_chartTransition`) combined with the
chart-level linearity `gradInnerInverse_finset_sum`.

What remains for the fully unconditional global theorem is the *construction* of the lifted
pieces `v_j` from the partition of unity (a measurable readback / honest global transition
property of the atlas structure), recorded as the residual blocker `U7-GLOBAL-LIFT`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.GlobalIBP
import Poincare.D13.ManifoldIBP.SmoothPartition

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

namespace OverlapAtlas

/-- **The partition-of-unity decomposition lemma.** Let `ψ_j` be coordinate functions in the
base chart `b` whose sum is `1` wherever `v ∘ chart_b` does not vanish, and let the global
functions `v_j` have `b`-chart expressions `ψ_j · (v ∘ chart_b)` and be supported in the image of
`chart b`. Then `v = Σ_j v_j` pointwise. -/
lemma eq_sum_of_pou (A : OverlapAtlas M (n + 1)) (b : ℕ) {ι : Type*} [Fintype ι]
    (ψ : ι → Vec (n + 1) → ℝ) (v : M → ℝ) (vj : ι → M → ℝ)
    (hpiece : ∀ j, ∀ y ∈ A.source b, vj j (A.chart b y) = ψ j y * v (A.chart b y))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hpiece_supp : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart b '' A.source b) :
    ∀ m, v m = ∑ j, vj j m := by
  intro m
  by_cases hm : ∃ y ∈ A.source b, A.chart b y = m
  · obtain ⟨y, hy, rfl⟩ := hm
    have hsum : ∑ j, vj j (A.chart b y) = ∑ j, ψ j y * v (A.chart b y) :=
      Finset.sum_congr rfl fun j _ => hpiece j y hy
    rw [hsum]
    by_cases hv0 : v (A.chart b y) = 0
    · simp [hv0]
    · rw [← Finset.sum_mul, hψ_sum y hv0, one_mul]
  · have hv0 : v m = 0 := by
      by_contra h
      exact hm (hvsupp m h)
    have hvj0 : ∀ j, vj j m = 0 := by
      intro j
      by_contra h
      exact hm (hpiece_supp j m h)
    rw [hv0]
    simp [hvj0]

/-- **Global weighted integration by parts from partition-of-unity data.** The finite-sum global
IBP `globalWeightedIBP_finset` with the decomposition `v = Σ_j v_j` *derived* from the
partition-of-unity relations `v_j ∘ chart_b = ψ_j · (v ∘ chart_b)` and `Σ_j ψ_j = 1` on the
support of `v`. -/
theorem globalWeightedIBP_of_pouData (A : OverlapAtlas M (n + 1)) (b : ℕ)
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (ψ : ι → Vec (n + 1) → ℝ)
    (f u v Du Guv : M → ℝ) (vj Guvj : ι → M → ℝ)
    (hf : Measurable f) (hDu : Measurable Du)
    (hvj : ∀ j, Measurable (vj j)) (hGuvj : ∀ j, Measurable (Guvj j))
    (hpiece : ∀ j, ∀ y ∈ A.source b, vj j (A.chart b y) = ψ j y * v (A.chart b y))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hpiece_supp_b : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hvsupp_j : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hGuvsupp : ∀ j, ∀ m, Guvj j m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hvsrc : ∀ j, ∀ y, vj j (A.chart (chartOf j) y) ≠ 0 → y ∈ A.source (chartOf j))
    (hGuvsrc : ∀ j, ∀ y, (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y ≠ 0 → y ∈ A.source (chartOf j))
    (hfc : ∀ j, ContDiff ℝ 2 fun y => f (A.chart (chartOf j) y))
    (huc : ∀ j, ContDiff ℝ 2 fun y => u (A.chart (chartOf j) y))
    (hvc : ∀ j, ContDiff ℝ 2 fun y => vj j (A.chart (chartOf j) y))
    (hvcc : ∀ j, HasCompactSupport fun y => vj j (A.chart (chartOf j) y))
    (hD : ∀ j, ∀ᵐ y ∂volume, y ∈ A.source (chartOf j) →
      Du (A.chart (chartOf j) y) = (A.metric (chartOf j)).driftLaplacian
        (fun z => f (A.chart (chartOf j) z)) (fun z => u (A.chart (chartOf j) z)) y)
    (hG : ∀ j, ∀ᵐ y ∂volume, y ∈ A.source (chartOf j) →
      Guvj j (A.chart (chartOf j) y) = (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y)
    (hGuvdecomp : ∀ m, Guv m = ∑ j, Guvj j m)
    (hintL : ∀ j, Integrable (fun m => Du m * vj j m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => Guvj j m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) :=
  A.globalWeightedIBP_finset chartOf f u v Du Guv vj Guvj hf hDu hvj hGuvj
    hvsupp_j hGuvsupp hvsrc hGuvsrc hfc huc hvc hvcc hD hG
    (A.eq_sum_of_pou b ψ v vj hpiece hψ_sum hvsupp hpiece_supp_b)
    hGuvdecomp hintL hintR

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.eq_sum_of_pou
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData
