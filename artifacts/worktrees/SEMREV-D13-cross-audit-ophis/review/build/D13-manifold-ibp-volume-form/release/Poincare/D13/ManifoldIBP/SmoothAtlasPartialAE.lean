/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (global IBP for null-boundary partial charts)

# The global weighted IBP for partial charts with null-boundary sources

`ManifoldIBP.SmoothAtlasPartial` proves the global weighted IBP with lifted partition-of-unity
pieces for partial charts, with the *pointwise* support of the pairing's chart expression in the
chart source (`hpair_src`) as the residual interface. For a smooth lifted expression the value
support is automatic (the expression vanishes outside the open source), but its *derivatives* need
not vanish at boundary points; only the boundary itself can carry a nonzero pairing value.

This module sharpens that: if the boundaries of the chart sources are **null** for the reference
measure (`hbd : volume (frontier (source i)) = 0`), then the pairing's chart expression vanishes
almost everywhere off the source, which is exactly what the almost-everywhere chart layer
`ManifoldIBP.POUAssemblyAE` needs. The resulting theorem
`globalWeightedIBP_of_pou_partial_ae` has the same conclusion as the pointwise version with
`hpair_src` replaced by the null-boundary hypothesis (a condition satisfied by half-spaces, balls
and all "nice" open chart sources).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.POUAssemblyAE
import Poincare.D13.ManifoldIBP.SmoothAtlasPartial

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

namespace SmoothOverlapAtlas

variable {A : SmoothOverlapAtlas M (n + 1)}

/-- **The lifted piece pairing is supported in its chart image** (from the definition of the lift:
it only reads the chart expression at source points). -/
lemma support_pouPairing_subset_chart (b i : ℕ) (u v : M → ℝ) (ψ : Vec (n + 1) → ℝ) :
    ∀ m, A.pouPairing b i u v ψ m ≠ 0 → m ∈ A.chart i '' A.source i := by
  intro m hm
  by_cases hmem : m ∈ A.chart i '' A.source i
  · exact hmem
  · rw [pouPairing, lift, if_neg hmem] at hm
    exact absurd rfl hm

/-- **The global weighted IBP with lifted partition-of-unity pieces for partial charts with
null-boundary sources.** The pointwise boundary-support hypothesis `hpair_src` of
`globalWeightedIBP_of_pou_partial` is replaced by the null-boundary condition
`volume (frontier (source i)) = 0`: off the boundary the lifted pairing's chart expression
vanishes on a neighbourhood, so it vanishes almost everywhere off the source, which is what the
almost-everywhere chart layer requires. -/
theorem globalWeightedIBP_of_pou_partial_ae
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (ψ : ι → Vec (n + 1) → ℝ)
    (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_supp : ∀ j, tsupport (ψ j) ⊆ overlapOf A.chart A.source (chartOf j) b)
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart b y))
    (hD : ∀ i y, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).driftLaplacian
        (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hψ_cc : ∀ j, HasCompactSupport (ψ j))
    (hproper : ∀ i j, ∀ K : Set (Vec (n + 1)), IsCompact K →
      IsCompact (A.transition i j ⁻¹' K))
    (hbd : ∀ i, volume (frontier (A.source i)) = 0)
    (hintL : ∀ j, Integrable (fun m => Du m * A.pouPiece b v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => A.pouPairing b (chartOf j) u v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  classical
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- supports of the lifted pieces
  have hpiece_supp_b : ∀ j m, A.pouPiece b v (ψ j) m ≠ 0 → m ∈ A.chart b '' A.source b := by
    intro j m hm
    obtain ⟨y, hy, hyz⟩ := support_lift_subset A (φ := fun y => ψ j y * v (A.chart b y)) hm
    have hyψ : y ∈ Function.support (ψ j) := by
      rw [Function.mem_support] at hy ⊢
      exact fun h0 => hy (by rw [h0, zero_mul])
    exact ⟨y, (hψ_supp j (subset_tsupport _ hyψ)).1, hyz⟩
  have hpiece_supp_j : ∀ j m, A.pouPiece b v (ψ j) m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j) := by
    intro j m hm
    obtain ⟨y, hy, hyz⟩ := support_lift_subset A (φ := fun y => ψ j y * v (A.chart b y)) hm
    have hyψ : y ∈ Function.support (ψ j) := by
      rw [Function.mem_support] at hy ⊢
      exact fun h0 => hy (by rw [h0, zero_mul])
    have hyW : y ∈ overlapOf A.chart A.source (chartOf j) b :=
      hψ_supp j (subset_tsupport _ hyψ)
    rw [← hyz]
    exact hyW.2
  -- the pieces' chart expressions vanish outside the chart source (value level, proved)
  have hpiece_src : ∀ j y, A.pouPiece b v (ψ j) (A.chart (chartOf j) y) ≠ 0 →
      y ∈ A.source (chartOf j) := by
    intro j y hy
    rw [pouPiece_chart_of_support A htrans (hψ_supp j) y] at hy
    have hsupp : A.transition b (chartOf j) y ∈ Function.support (ψ j) :=
      fun h0 => hy (by rw [h0, zero_mul])
    have hmem := hψ_supp j (subset_tsupport (ψ j) hsupp)
    obtain ⟨z, hz, hzy⟩ := hmem.2
    rw [A.transition_chart_global b (chartOf j) y] at hzy
    rw [← A.inj_chart (chartOf j) hzy]
    exact hz
  -- compact support of the pieces' chart expressions
  have hpiece_cc : ∀ j, HasCompactSupport fun y =>
      A.pouPiece b v (ψ j) (A.chart (chartOf j) y) := by
    intro j
    have hfun : (fun y => A.pouPiece b v (ψ j) (A.chart (chartOf j) y))
        = fun y => ψ j (A.transition b (chartOf j) y) * v (A.chart (chartOf j) y) := by
      funext y
      exact A.pouPiece_chart_of_support htrans (hψ_supp j) y
    rw [hfun]
    refine IsCompact.of_isClosed_subset (hproper b (chartOf j) (tsupport (ψ j)) (hψ_cc j))
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ ((isClosed_tsupport (ψ j)).preimage
      (A.contDiff_transition b (chartOf j)).continuous)
    intro y hy
    rw [Function.mem_support] at hy
    exact subset_tsupport (ψ j) (by
      rw [Function.mem_support]
      exact fun h0 => hy (by rw [h0, zero_mul]))
  -- the lifted pairing is supported in its chart image
  have hGuvsupp' : ∀ j m, A.pouPairing b (chartOf j) u v (ψ j) m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j) :=
    fun j => A.support_pouPairing_subset_chart b (chartOf j) u v (ψ j)
  -- the pairing's chart expression vanishes a.e. off the chart source, by null boundary
  have hGuvae : ∀ j, ∀ᵐ y ∂volume, y ∉ A.source (chartOf j) →
      (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => ψ j (A.transition b (chartOf j) z)
          * v (A.chart (chartOf j) z)) y = 0 := by
    intro j
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (hbd (chartOf j))]
      with y hy hys
    by_contra hne
    -- `y` is neither on the boundary nor outside the closure: it lies in the interior of the
    -- complement, where the chart expression vanishes identically
    have hcl : y ∉ closure (A.source (chartOf j)) := by
      intro hyc
      exact hy (by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨hyc, subset_closure hys⟩)
    have hinter : y ∈ interior ((A.source (chartOf j))ᶜ) := by
      rw [interior_compl]
      exact hcl
    have hFzero : (fun z => ψ j (A.transition b (chartOf j) z)
        * v (A.chart (chartOf j) z)) =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_interior.mem_nhds hinter] with z hz
      have hzs : z ∉ A.source (chartOf j) := interior_subset hz
      have hsupp : A.transition b (chartOf j) z ∉ Function.support (ψ j) := by
        intro hcon
        have hmem := hψ_supp j (subset_tsupport (ψ j) hcon)
        obtain ⟨w, hw, hwz⟩ := hmem.2
        rw [A.transition_chart_global b (chartOf j) z] at hwz
        exact hzs (A.inj_chart (chartOf j) hwz ▸ hw)
      simp [Function.notMem_support.mp hsupp]
    have hf : fderiv ℝ (fun z => ψ j (A.transition b (chartOf j) z)
        * v (A.chart (chartOf j) z)) y = 0 := by
      rw [hFzero.fderiv_eq]
      simp
    have hpd : ∀ k, ChartMetric.partialDeriv k
        (fun z => ψ j (A.transition b (chartOf j) z)
          * v (A.chart (chartOf j) z)) y = 0 := by
      intro k
      simp only [ChartMetric.partialDeriv, hf, ContinuousLinearMap.zero_apply]
    apply hne
    simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse, hpd, mul_zero,
      Finset.sum_const_zero]
  have hGuvae' : ∀ j, ∀ᵐ y ∂volume, y ∉ A.source (chartOf j) →
      (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => A.pouPiece b v (ψ j) (A.chart (chartOf j) z)) y = 0 := by
    intro j
    filter_upwards [hGuvae j] with y hy
    rw [show (fun z => A.pouPiece b v (ψ j) (A.chart (chartOf j) z))
        = fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z) from
      funext fun z => A.pouPiece_chart_of_support htrans (hψ_supp j) z]
    exact hy
  refine A.toOverlapAtlas.globalWeightedIBP_of_pouData_ae b chartOf ψ f u v Du Guv
    (fun j => A.pouPiece b v (ψ j)) (fun j => A.pouPairing b (chartOf j) u v (ψ j))
    hf hDu ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact A.measurable_pouPiece b hv (hψ_sm j)
  · intro j
    exact A.measurable_pouPairing b (chartOf j) (huc (chartOf j)) (hvc (chartOf j)) (hψ_sm j)
  · intro j y hy
    exact A.pouPiece_apply_of_mem b v (ψ j) hy
  · intro y hy
    exact hψ_sum y hy
  · exact hvsupp
  · exact hpiece_supp_b
  · exact hpiece_supp_j
  · exact hGuvsupp'
  · exact hpiece_src
  · exact hGuvae'
  · intro j
    exact hfc (chartOf j)
  · intro j
    exact huc (chartOf j)
  · intro j
    have hfun : (fun y => A.pouPiece b v (ψ j) (A.chart (chartOf j) y))
        = fun y => ψ j (A.transition b (chartOf j) y) * v (A.chart (chartOf j) y) := by
      funext y
      exact A.pouPiece_chart_of_support htrans (hψ_supp j) y
    rw [hfun]
    exact (((hψ_sm j).of_le hle).comp (A.contDiff_transition b (chartOf j))).mul
      (hvc (chartOf j))
  · exact hpiece_cc
  · intro j
    filter_upwards with y hy
    exact hD (chartOf j) y hy
  · intro j
    filter_upwards with y hy
    rw [A.pouPairing_apply_of_mem b (chartOf j) u v (ψ j) hy]
    have hfun : (fun z => A.pouPiece b v (ψ j) (A.chart (chartOf j) z))
        = fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z) := by
      funext z
      exact A.pouPiece_chart_of_support htrans (hψ_supp j) z
    rw [hfun]
  · exact A.sum_pouPairing_of_support htrans b chartOf u v ψ hψ_supp huc hvc hψ_sm hψ_sum
      Guv hG hGuvsupp
  · intro j
    exact hintL j
  · intro j
    exact hintR j

end SmoothOverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_pouPairing_subset_chart
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae
