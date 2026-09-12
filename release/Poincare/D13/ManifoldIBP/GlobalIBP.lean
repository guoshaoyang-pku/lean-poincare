/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (finite chart decomposition of the global IBP)

# Global integration by parts from a finite chart-supported decomposition

`ManifoldIBP.OverlapIBP` proves the manifold weighted integration by parts

`∫_M (Δ_f u) v d(e^{-f} μ_g) = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} d(e^{-f} μ_g)`

for test data **supported in a single chart**. The honest global statement needs a smooth
partition of unity subordinate to the (overlapping) atlas, which splits a compactly supported
test function into *finitely many* chart-supported pieces. This module supplies the algebraic
half of that reduction: once the test function `v` and the pairing `Guv` are *given* as finite
sums of chart-supported pieces `v_j`, `Guv_j`, the global identity follows from the chart
theorem by linearity of the Bochner integral — this is the "locally finite sum through the
integral" step, with compact support making the sum finite.

The hypotheses are exactly the chart-level data of the pieces:

* `hvdecomp` / `hGuvdecomp` — the pointwise finite decompositions `v = Σ_j v_j` and
  `Guv = Σ_j Guv_j` (a partition of unity produces them);
* `hvsupp` / `hGuvsupp` — each piece is supported in the image of its chart `chartOf j`;
* `hD` / `hG` — the chart identification of the manifold operators on each piece
  (`Du` is the drift Laplacian of `u`, `Guv_j` is the inverse-metric pairing of `u` and `v_j`);
* `hvcc` — each piece is compactly supported in its chart coordinates (this is what makes the
  POU sum finite);
* `hintL` / `hintR` — integrability of the two sides of each piece (discharged in concrete
  models from continuity + compact support, see `ManifoldIBP.OverlapIBPModel`).

`gradInnerInverse_finset_sum` records the chart-level linearity of the gradient pairing in its
second argument, which is what makes the decomposed pairing `Σ_j ⟨∇u, ∇v_j⟩` reassemble into
`⟨∇u, ∇v⟩` (the telescoping identity behind the partition-of-unity proof).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBP

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-! ## Chart-level linearity of the gradient pairing -/

/-- **The inverse-metric gradient pairing is linear in its second argument over finite sums.**
`⟨∇u, ∇(Σ_{i∈s} w_i)⟩_{g⁻¹} = Σ_{i∈s} ⟨∇u, ∇w_i⟩_{g⁻¹}`. This is the chart-level identity
that lets a partition-of-unity decomposition of `v` reassemble the pairing
`⟨∇u, ∇v⟩_{g⁻¹}` from the pairings with the pieces. -/
lemma gradInnerInverse_finset_sum {n : ℕ} (G : ChartMetric (n + 1)) (u : Vec (n + 1) → ℝ)
    {ι : Type*} (s : Finset ι) (w : ι → Vec (n + 1) → ℝ) (x : Vec (n + 1))
    (hw : ∀ i ∈ s, DifferentiableAt ℝ (w i) x) :
    G.gradInnerInverse u (fun y => ∑ i ∈ s, w i y) x
      = ∑ i ∈ s, G.gradInnerInverse u (w i) x := by
  have hderiv : ∀ j : Fin (n + 1), ChartMetric.partialDeriv j (fun y => ∑ i ∈ s, w i y) x
      = ∑ i ∈ s, ChartMetric.partialDeriv j (w i) x := by
    intro j
    simp only [ChartMetric.partialDeriv]
    rw [fderiv_fun_sum hw]
    simp
  calc G.gradInnerInverse u (fun y => ∑ i ∈ s, w i y) x
      = ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
          G.invMatrix x a b * ChartMetric.partialDeriv a u x * (∑ i ∈ s, ChartMetric.partialDeriv b (w i) x) := by
        simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hderiv b]
    _ = ∑ i ∈ s, ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
          G.invMatrix x a b * ChartMetric.partialDeriv a u x * ChartMetric.partialDeriv b (w i) x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun b _ => Finset.sum_comm)]
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    _ = ∑ i ∈ s, G.gradInnerInverse u (w i) x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse]

namespace OverlapAtlas

/-- **Global weighted integration by parts from a finite chart-supported decomposition.**
Let the atlas `A` have overlapping charts, `f` a drift, `u` a test function and `v` a test
function that is a finite sum `Σ_j v_j` of pieces, each compactly supported inside the image of
a chart `chartOf j`; let `Guv = Σ_j Guv_j` where `Guv_j` is chart-identified with the
inverse-metric pairing `⟨∇u, ∇v_j⟩_{g⁻¹}` and `Du` with the drift Laplacian `Δ_f u` in that
chart. Then

`∫_M (Δ_f u) · v d(e^{-f} μ_g) = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} d(e^{-f} μ_g)`.

The proof applies the chart-supported theorem `globalWeightedIBP_of_chartSupported` to each
piece and sums the finitely many identities through the Bochner integral. No integration by
parts is assumed on the manifold side. -/
theorem globalWeightedIBP_finset (A : OverlapAtlas M (n + 1))
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (f u v Du Guv : M → ℝ)
    (vj Guvj : ι → M → ℝ)
    (hf : Measurable f) (hDu : Measurable Du)
    (hvj : ∀ j, Measurable (vj j)) (hGuvj : ∀ j, Measurable (Guvj j))
    (hvsupp : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart (chartOf j) '' A.source (chartOf j))
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
    (hvdecomp : ∀ m, v m = ∑ j, vj j m)
    (hGuvdecomp : ∀ m, Guv m = ∑ j, Guvj j m)
    (hintL : ∀ j, Integrable (fun m => Du m * vj j m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => Guvj j m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  have hpiece : ∀ j : ι, ∫ m, Du m * vj j m
        ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guvj j m ∂((A.globalMeasure volume).withDensity (A.weight f)) :=
    fun j => A.globalWeightedIBP_of_chartSupported (chartOf j) f u (vj j) Du (Guvj j)
      hf (hvj j) hDu (hGuvj j) (hvsupp j) (hGuvsupp j) (hvsrc j) (hGuvsrc j)
      (hfc j) (huc j) (hvc j) (hvcc j) (hD j) (hG j)
  have hL : ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∑ j, ∫ m, Du m * vj j m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
    have hfun : (fun m => Du m * v m) = fun m => ∑ j, Du m * vj j m := by
      funext m
      rw [hvdecomp m, Finset.mul_sum]
    rw [hfun]
    exact integral_finsetSum _ fun j _ => hintL j
  have hR : ∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∑ j, ∫ m, Guvj j m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
    have hfun : Guv = fun m => ∑ j, Guvj j m := by funext m; rw [hGuvdecomp m]
    rw [hfun]
    exact integral_finsetSum _ fun j _ => hintR j
  rw [hL, hR, Finset.sum_congr rfl fun j _ => hpiece j, Finset.sum_neg_distrib]

/-- **Global unweighted integration by parts (Green identity) from a finite chart-supported
decomposition**: `globalWeightedIBP_finset` with zero drift, where the weight is `1`. -/
theorem globalIBP_finset (A : OverlapAtlas M (n + 1))
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (u v Du Guv : M → ℝ)
    (vj Guvj : ι → M → ℝ) (hDu : Measurable Du)
    (hvj : ∀ j, Measurable (vj j)) (hGuvj : ∀ j, Measurable (Guvj j))
    (hvsupp : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hGuvsupp : ∀ j, ∀ m, Guvj j m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hvsrc : ∀ j, ∀ y, vj j (A.chart (chartOf j) y) ≠ 0 → y ∈ A.source (chartOf j))
    (hGuvsrc : ∀ j, ∀ y, (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y ≠ 0 → y ∈ A.source (chartOf j))
    (huc : ∀ j, ContDiff ℝ 2 fun y => u (A.chart (chartOf j) y))
    (hvc : ∀ j, ContDiff ℝ 2 fun y => vj j (A.chart (chartOf j) y))
    (hvcc : ∀ j, HasCompactSupport fun y => vj j (A.chart (chartOf j) y))
    (hD : ∀ j, ∀ᵐ y ∂volume, y ∈ A.source (chartOf j) →
      Du (A.chart (chartOf j) y) = (A.metric (chartOf j)).laplacian
        (fun z => u (A.chart (chartOf j) z)) y)
    (hG : ∀ j, ∀ᵐ y ∂volume, y ∈ A.source (chartOf j) →
      Guvj j (A.chart (chartOf j) y) = (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y)
    (hvdecomp : ∀ m, v m = ∑ j, vj j m)
    (hGuvdecomp : ∀ m, Guv m = ∑ j, Guvj j m)
    (hintL : ∀ j, Integrable (fun m => Du m * vj j m) (A.globalMeasure volume))
    (hintR : ∀ j, Integrable (fun m => Guvj j m) (A.globalMeasure volume)) :
    ∫ m, Du m * v m ∂(A.globalMeasure volume)
      = -∫ m, Guv m ∂(A.globalMeasure volume) := by
  have hw : ((A.globalMeasure volume).withDensity (A.weight (fun _ : M => 0)))
      = A.globalMeasure volume := by
    rw [A.weight_zero]
    exact withDensity_one
  have h := A.globalWeightedIBP_finset chartOf (fun _ => 0) u v Du Guv vj Guvj
    measurable_const hDu hvj hGuvj hvsupp hGuvsupp hvsrc hGuvsrc
    (fun _ => contDiff_const) huc hvc hvcc
    (fun j => by
      refine (hD j).mono fun y hy => ?_
      intro hys
      rw [hy hys]
      simp [ChartMetric.driftLaplacian, ChartMetric.gradInnerInverse,
        ChartMetric.metricInnerInverse, ChartMetric.partialDeriv])
    hG hvdecomp hGuvdecomp
    (fun j => by rw [hw]; exact hintL j)
    (fun j => by rw [hw]; exact hintR j)
  rwa [hw] at h

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.gradInnerInverse_finset_sum
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_finset
