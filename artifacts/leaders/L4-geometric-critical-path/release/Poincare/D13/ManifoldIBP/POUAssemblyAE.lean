/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (a.e. support variant of the chart IBP layer)

# The chart-supported IBP layer with almost-everywhere support

`ManifoldIBP.OverlapIBP` proves the manifold weighted IBP for test data supported in a single
chart, using the *pointwise* support of the chart expression of the pairing (`hGuvsrc`). For
partial charts the lifted piece pairings are smooth expressions that vanish outside the open
chart source but whose derivatives need not vanish at boundary points, so only an almost-everywhere
support statement is available when the boundary of the chart source is null.

This module provides that variant: the a.e. set-integral lemma and the a.e. versions of
`globalWeightedIBP_of_chartSupported`, `globalWeightedIBP_finset` and
`globalWeightedIBP_of_pouData`. The hypotheses are *weaker* than the pointwise ones
(`hGuvsrc` implies `hGuvae`), so the pointwise layer remains a special case; the a.e. layer is what
a chart atlas with null-boundary sources can discharge.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.POUAssembly

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- **Set integral with almost-everywhere support.** If `f` vanishes almost everywhere off the
measurable set `s`, then its integral over `s` is its integral over the whole space. -/
lemma setIntegral_eq_integral_of_ae_support {d : ℕ} {s : Set (Vec d)} (hs : MeasurableSet s)
    {f : Vec d → ℝ} (h : ∀ᵐ y ∂volume, y ∉ s → f y = 0) :
    ∫ y in s, f y ∂volume = ∫ y, f y ∂volume := by
  rw [← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  by_cases hys : y ∈ s
  · simp [hys]
  · simp [hys, hy hys]

namespace OverlapAtlas

/-- **The chart-supported manifold weighted IBP with almost-everywhere support of the pairing's
chart expression.** Same statement as `globalWeightedIBP_of_chartSupported`, with the pointwise
hypothesis `hGuvsrc` replaced by its almost-everywhere form. -/
theorem globalWeightedIBP_of_chartSupported_ae (A : OverlapAtlas M (n + 1))
    (i : ℕ) (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hvsrc : ∀ y, v (A.chart i y) ≠ 0 → y ∈ A.source i)
    (hGuvae : ∀ᵐ y ∂volume, y ∉ A.source i →
      (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
        (fun z => v (A.chart i z)) y = 0)
    (hfc : ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart i y))
    (hD : ∀ᵐ y ∂volume, y ∈ A.source i →
      Du (A.chart i y)
        = (A.metric i).driftLaplacian (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ᵐ y ∂volume, y ∈ A.source i →
      Guv (A.chart i y)
        = (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  have hsrc : MeasurableSet (A.source i) := (A.isOpen_source i).measurableSet
  have hL : ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∫ y in A.source i,
          Real.exp (-(f (A.chart i y))) * (Du (A.chart i y) * v (A.chart i y))
            * A.density i y ∂volume :=
    A.integral_globalMeasure_withDensity_of_supported volume i hf
      (hDu.mul hv).aestronglyMeasurable
      (fun m hm => hvsupp m (mul_ne_zero_iff.mp hm).2)
  have hL' : ∫ y in A.source i,
        Real.exp (-(f (A.chart i y))) * (Du (A.chart i y) * v (A.chart i y))
          * A.density i y ∂volume
      = ∫ y in A.source i,
          ((A.metric i).driftLaplacian (fun z => f (A.chart i z))
            (fun z => u (A.chart i z)) y * v (A.chart i y))
            * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume := by
    refine setIntegral_congr_ae hsrc ?_
    filter_upwards [hD] with y hy hys
    rw [hy hys]
    ring
  have hL'' : ∫ y in A.source i,
        ((A.metric i).driftLaplacian (fun z => f (A.chart i z))
          (fun z => u (A.chart i z)) y * v (A.chart i y))
          * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume
      = ∫ y, (A.metric i).driftLaplacian (fun z => f (A.chart i z))
          (fun z => u (A.chart i z)) y * v (A.chart i y)
          * Real.exp (-(f (A.chart i y))) * A.density i y ∂volume := by
    refine setIntegral_eq_integral_of_support hsrc ?_ volume
    intro y hy
    obtain ⟨h1, -⟩ := mul_ne_zero_iff.mp hy
    obtain ⟨h2, -⟩ := mul_ne_zero_iff.mp h1
    exact hvsrc y (mul_ne_zero_iff.mp h2).2
  have hR : ∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = ∫ y in A.source i,
          Real.exp (-(f (A.chart i y))) * Guv (A.chart i y) * A.density i y ∂volume :=
    A.integral_globalMeasure_withDensity_of_supported volume i hf
      hGuv.aestronglyMeasurable hGuvsupp
  have hR' : ∫ y in A.source i,
        Real.exp (-(f (A.chart i y))) * Guv (A.chart i y) * A.density i y ∂volume
      = ∫ y in A.source i,
          (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
            (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
            * A.density i y ∂volume := by
    refine setIntegral_congr_ae hsrc ?_
    filter_upwards [hG] with y hy hys
    rw [hy hys]
    ring
  have hR'' : ∫ y in A.source i,
        (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
          (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
          * A.density i y ∂volume
      = ∫ y, (A.metric i).gradInnerInverse (fun z => u (A.chart i z))
          (fun z => v (A.chart i z)) y * Real.exp (-(f (A.chart i y)))
          * A.density i y ∂volume := by
    refine setIntegral_eq_integral_of_ae_support hsrc ?_
    filter_upwards [hGuvae] with y hy hys
    simp [hy hys]
  rw [hL, hL', hL'', hR, hR', hR'']
  exact (A.metric i).chart_weighted_ibp (fun z => f (A.chart i z))
    (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) hfc huc hvc hvcc

/-- **The finite chart decomposition with almost-everywhere support.** Same statement as
`globalWeightedIBP_finset`, with the pointwise per-piece pairing support replaced by its
almost-everywhere form. -/
theorem globalWeightedIBP_finset_ae (A : OverlapAtlas M (n + 1))
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (f u v Du Guv : M → ℝ)
    (vj Guvj : ι → M → ℝ)
    (hf : Measurable f) (hDu : Measurable Du)
    (hvj : ∀ j, Measurable (vj j)) (hGuvj : ∀ j, Measurable (Guvj j))
    (hvsupp : ∀ j, ∀ m, vj j m ≠ 0 → m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hGuvsupp : ∀ j, ∀ m, Guvj j m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j))
    (hvsrc : ∀ j, ∀ y, vj j (A.chart (chartOf j) y) ≠ 0 → y ∈ A.source (chartOf j))
    (hGuvae : ∀ j, ∀ᵐ y ∂volume, y ∉ A.source (chartOf j) →
      (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y = 0)
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
    fun j => A.globalWeightedIBP_of_chartSupported_ae (chartOf j) f u (vj j) Du (Guvj j)
      hf (hvj j) hDu (hGuvj j) (hvsupp j) (hGuvsupp j) (hvsrc j) (hGuvae j)
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

/-- **The partition-of-unity reduction with almost-everywhere support.** Same statement as
`globalWeightedIBP_of_pouData`, with the pointwise per-piece pairing support replaced by its
almost-everywhere form. -/
theorem globalWeightedIBP_of_pouData_ae (A : OverlapAtlas M (n + 1)) (b : ℕ)
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
    (hGuvae : ∀ j, ∀ᵐ y ∂volume, y ∉ A.source (chartOf j) →
      (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => vj j (A.chart (chartOf j) z)) y = 0)
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
  A.globalWeightedIBP_finset_ae chartOf f u v Du Guv vj Guvj hf hDu hvj hGuvj
    hvsupp_j hGuvsupp hvsrc hGuvae hfc huc hvc hvcc hD hG
    (A.eq_sum_of_pou b ψ v vj hpiece hψ_sum hvsupp hpiece_supp_b)
    hGuvdecomp hintL hintR

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.setIntegral_eq_integral_of_ae_support
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData_ae
