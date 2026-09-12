/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (global IBP for partial charts)

# The global weighted IBP with lifted pieces for partial charts

`ManifoldIBP.SmoothAtlasIBP` proved the global weighted IBP with *constructed* lifted
partition-of-unity pieces for **total** chart atlases (all sources `univ`, all charts surjective).
This module removes the totality assumption: for a `SmoothOverlapAtlas` whose transitions satisfy
the coherence property

`chart j y ∈ chart i '' source i → transition i j y ∈ source i`

(the transition's `i`-coordinate of a point whose `j`-chart image lies in the `i`-chart image is in
the `i`-source), the lift of a coordinate function `φ` supported in the overlap `overlapOf i b`
still has chart-`i` expression `φ (transition b i ·)` (`lift_apply_chart_of_support`). The pieces
`pouPiece`/`pouPairing` and the pairing reassembly then go through in the same form.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.Riemannian.AtlasPairing

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- **The pairing vanishes where the second function vanishes identically nearby.** -/
lemma support_gradInnerInverse_subset {n : ℕ} (G : ChartMetric (n + 1))
    (u φ : Vec (n + 1) → ℝ) :
    support (fun x => G.gradInnerInverse u φ x) ⊆ tsupport φ := by
  intro x hx
  by_contra hxt
  apply hx
  have hopen : (tsupport φ)ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport φ).isOpen_compl.mem_nhds hxt
  have hzero : φ =ᶠ[𝓝 x] 0 :=
    Filter.eventually_of_mem hopen fun y hy =>
      Function.notMem_support.mp fun hsupp => hy (subset_tsupport φ hsupp)
  have hf : fderiv ℝ φ x = 0 := by
    rw [hzero.fderiv_eq]
    simp
  have hpd : ∀ j, ChartMetric.partialDeriv j φ x = 0 := by
    intro j
    simp only [ChartMetric.partialDeriv, hf, ContinuousLinearMap.zero_apply]
  simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse, hpd, mul_zero,
    Finset.sum_const_zero]

namespace SmoothOverlapAtlas

variable (A : SmoothOverlapAtlas M (n + 1))

/-- **The chart-`i` expression of the lift through `b` for a function supported in the overlap.**
If `φ` is supported in `overlapOf i b` then the lift of `φ` through the `b`-chart, read back
through the `i`-chart, is `φ` evaluated at the transition `transition b i`; no totality of the
charts is needed, only the coherence of the transitions. -/
lemma lift_apply_chart_of_support
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    {b i : ℕ} {φ : Vec (n + 1) → ℝ}
    (hφ : tsupport φ ⊆ overlapOf A.chart A.source i b) (z : Vec (n + 1)) :
    A.lift b φ (A.chart i z) = φ (A.transition b i z) := by
  by_cases hmem : A.chart i z ∈ A.chart b '' A.source b
  · rw [lift, if_pos hmem]
    have hτsrc : A.transition b i z ∈ A.source b := htrans b i z hmem
    have h1 : A.chart b (Function.invFunOn (A.chart b) (A.source b) (A.chart i z))
        = A.chart b (A.transition b i z) := by
      rw [Function.invFunOn_eq ⟨A.transition b i z, hτsrc, A.transition_chart_global b i z⟩,
        A.transition_chart_global b i z]
    rw [A.inj_chart b h1]
  · rw [lift, if_neg hmem]
    by_cases hsupp : A.transition b i z ∈ Function.support φ
    · have hmem' := hφ (subset_tsupport φ hsupp)
      exact absurd ⟨A.transition b i z, hmem'.1, A.transition_chart_global b i z⟩ hmem
    · exact (Function.notMem_support.mp hsupp).symm

/-- **The chart expression of a partition-of-unity piece supported in the overlap.** -/
lemma pouPiece_chart_of_support
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    {b i : ℕ} {v : M → ℝ} {ψ : Vec (n + 1) → ℝ}
    (hψ : tsupport ψ ⊆ overlapOf A.chart A.source i b) (z : Vec (n + 1)) :
    A.pouPiece b v ψ (A.chart i z) = ψ (A.transition b i z) * v (A.chart i z) := by
  rw [pouPiece, lift_apply_chart_of_support A htrans ?_ z, A.transition_chart_global b i z]
  exact (tsupport_mul_subset_left (f := ψ) (g := fun y => v (A.chart b y))).trans hψ

variable {A}

/-- The lift of a coordinate function evaluated through its own chart (partial charts). -/
lemma pouPiece_apply_of_mem (b : ℕ) (v : M → ℝ) (ψ : Vec (n + 1) → ℝ)
    {y : Vec (n + 1)} (hy : y ∈ A.source b) :
    A.pouPiece b v ψ (A.chart b y) = ψ y * v (A.chart b y) :=
  A.lift_apply_chart hy

/-- The lifted piece pairing evaluated through its own chart (partial charts). -/
lemma pouPairing_apply_of_mem (b i : ℕ) (u v : M → ℝ) (ψ : Vec (n + 1) → ℝ)
    {y : Vec (n + 1)} (hy : y ∈ A.source i) :
    A.pouPairing b i u v ψ (A.chart i y) = (A.metric i).gradInnerInverse
      (fun z' => u (A.chart i z'))
      (fun z' => ψ (A.transition b i z') * v (A.chart i z')) y :=
  A.lift_apply_chart hy

/-- The pairing vanishes where the second function vanishes identically nearby. -/
lemma gradInnerInverse_eq_zero_of_eventuallyEq_zero {i : ℕ} (u φ : Vec (n + 1) → ℝ)
    {y : Vec (n + 1)} (hφ : φ =ᶠ[𝓝 y] 0) :
    (A.metric i).gradInnerInverse u φ y = 0 := by
  have hf : fderiv ℝ φ y = 0 := by
    rw [hφ.fderiv_eq]
    simp
  have hpd : ∀ k, ChartMetric.partialDeriv k φ y = 0 := by
    intro k
    simp only [ChartMetric.partialDeriv, hf, ContinuousLinearMap.zero_apply]
  simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse, hpd, mul_zero,
    Finset.sum_const_zero]

/-- **The pairing reassembly for partial charts.** The sum of the lifted piece pairings equals the
global pairing of `u` with `v`: each piece's pairing is transferred to the base chart by the atlas
chart-independence, the pieces whose partition-of-unity function vanishes near the point
contribute zero, and the remaining pieces sum to `v` by the partition-of-unity identity. -/
lemma sum_pouPairing_of_support
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ)
    (u v : M → ℝ) (ψ : ι → Vec (n + 1) → ℝ)
    (hψ_supp : ∀ j, tsupport (ψ j) ⊆ overlapOf A.chart A.source (chartOf j) b)
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (Guv : M → ℝ)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b) :
    ∀ m, Guv m = ∑ j, A.pouPairing b (chartOf j) u v (ψ j) m := by
  classical
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- the chart-`b` value of each lifted piece pairing
  have hterm : ∀ (j : ι) (y : Vec (n + 1)), y ∈ A.source b →
      A.pouPairing b (chartOf j) u v (ψ j) (A.chart b y)
        = (A.metric b).gradInnerInverse (fun z => u (A.chart b z))
            (fun z => ψ j z * v (A.chart b z)) y := by
    intro j y hy
    set i := chartOf j with hi
    by_cases hmem : A.chart b y ∈ A.chart i '' A.source i
    · -- the piece lives in the `i`-chart: transfer by chart-independence
      set z := Function.invFunOn (A.chart i) (A.source i) (A.chart b y) with hz
      have hz_src : z ∈ A.source i := Function.invFunOn_mem hmem
      have hz_chart : A.chart i z = A.chart b y := Function.invFunOn_eq hmem
      have hz_eq : z = A.transition i b y := by
        apply A.inj_chart i
        rw [hz_chart, A.transition_chart_global i b y]
      rw [← hz_chart, pouPairing, A.lift_apply_chart (b := i) (φ := fun z' =>
        (A.metric i).gradInnerInverse (fun z'' => u (A.chart i z''))
          (fun z'' => ψ j (A.transition b i z'') * v (A.chart i z'')) z') (y := z) hz_src]
      have hcomp : (fun z' => u (A.chart i z'))
          = (fun z' => (fun y' => u (A.chart b y')) (A.transition b i z')) := by
        funext z'
        rw [← A.transition_chart_global b i z']
      have hcomp2 : (fun z' => ψ j (A.transition b i z') * v (A.chart i z'))
          = (fun z' => (fun y' => ψ j y' * v (A.chart b y')) (A.transition b i z')) := by
        funext z'
        rw [← A.transition_chart_global b i z']
      rw [hcomp, hcomp2]
      have hz_mem : z ∈ overlapOf A.chart A.source b i := by
        refine ⟨hz_src, ?_⟩
        show A.chart i z ∈ A.chart b '' A.source b
        rw [hz_chart]
        exact ⟨y, hy, rfl⟩
      have hci := A.gradInnerInverse_chartTransition (fun i j => A.isOpen_overlap i j) b i z
        hz_mem (fun y' => u (A.chart b y')) (fun y' => ψ j y' * v (A.chart b y'))
        (Differentiable.differentiableAt ((huc b).differentiable (by simp)))
        (Differentiable.differentiableAt (ContDiff.differentiable
          (((hψ_sm j).of_le hle).mul (hvc b)) (by simp)))
      rw [hci]
      have hzτ : A.transition b i z = y := by
        rw [hz_eq, A.transition_transition b i y]
      rw [hzτ]
    · -- the piece vanishes near `y`: both sides are zero
      have hy_not : y ∉ tsupport (ψ j) := fun hy' => hmem ((hψ_supp j hy').2)
      have hzero : (fun z => ψ j z * v (A.chart b z)) =ᶠ[𝓝 y] 0 := by
        have hcompl : (tsupport (ψ j))ᶜ ∈ 𝓝 y :=
          (isClosed_tsupport (ψ j)).isOpen_compl.mem_nhds hy_not
        filter_upwards [hcompl] with z hz
        have hz0 : ψ j z = 0 :=
          Function.notMem_support.mp fun hsupp => hz (subset_tsupport (ψ j) hsupp)
        simp [hz0]
      have hleft : A.pouPairing b (chartOf j) u v (ψ j) (A.chart b y) = 0 := by
        rw [pouPairing]
        by_cases hmem' : A.chart b y ∈ A.chart i '' A.source i
        · exact absurd hmem' hmem
        · rw [lift, if_neg hmem']
      have hright : (A.metric b).gradInnerInverse (fun z => u (A.chart b z))
          (fun z => ψ j z * v (A.chart b z)) y = 0 := by
        have hf : fderiv ℝ (fun z => ψ j z * v (A.chart b z)) y = 0 := by
          rw [hzero.fderiv_eq]
          simp
        have hpd : ∀ k, ChartMetric.partialDeriv k
            (fun z => ψ j z * v (A.chart b z)) y = 0 := by
          intro k
          simp only [ChartMetric.partialDeriv, hf, ContinuousLinearMap.zero_apply]
        simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse, hpd,
          mul_zero, Finset.sum_const_zero]
      rw [hleft, hright]
  intro m
  by_cases hmem : m ∈ A.chart b '' A.source b
  · obtain ⟨y, hy, rfl⟩ := hmem
    rw [hG b y hy, Finset.sum_congr rfl fun j _ => hterm j y hy]
    rw [← gradInnerInverse_finset_sum (A.metric b) (fun z => u (A.chart b z))
      (Finset.univ : Finset ι) (fun j y' => ψ j y' * v (A.chart b y')) y
      (fun j _ => Differentiable.differentiableAt
        (ContDiff.differentiable (((hψ_sm j).of_le hle).mul (hvc b)) (by simp)))]
    congr 1
    funext y'
    by_cases hv0 : v (A.chart b y') = 0
    · simp [hv0]
    · rw [← Finset.sum_mul, hψ_sum y' hv0, one_mul]
  · have hsum0 : (∑ j, A.pouPairing b (chartOf j) u v (ψ j) m) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hmem' : m ∈ A.chart (chartOf j) '' A.source (chartOf j)
      · obtain ⟨z, hz_src, rfl⟩ := hmem'
        rw [pouPairing, A.lift_apply_chart (b := chartOf j) (φ := fun z' =>
          (A.metric (chartOf j)).gradInnerInverse (fun z'' => u (A.chart (chartOf j) z''))
            (fun z'' => ψ j (A.transition b (chartOf j) z'')
              * v (A.chart (chartOf j) z'')) z') (y := z) hz_src]
        -- the piece expression vanishes near `z`
        have hz_not : A.transition b (chartOf j) z ∉ tsupport (ψ j) := by
          intro hcon
          exact hmem ⟨A.transition b (chartOf j) z, (hψ_supp j hcon).1,
            (A.transition_chart_global b (chartOf j) z)⟩
        have hcont : Continuous (fun z' => A.transition b (chartOf j) z') :=
          (A.contDiff_transition b (chartOf j)).continuous
        have hcompl : (tsupport (ψ j))ᶜ ∈ 𝓝 (A.transition b (chartOf j) z) :=
          (isClosed_tsupport (ψ j)).isOpen_compl.mem_nhds hz_not
        have hzero : (fun z' => ψ j (A.transition b (chartOf j) z')
            * v (A.chart (chartOf j) z')) =ᶠ[𝓝 z] 0 := by
          filter_upwards [hcont.continuousAt hcompl] with z' hz'
          have hz0 : ψ j (A.transition b (chartOf j) z') = 0 :=
            Function.notMem_support.mp fun hsupp => hz' (subset_tsupport (ψ j) hsupp)
          simp [hz0]
        have hf : fderiv ℝ (fun z' => ψ j (A.transition b (chartOf j) z')
            * v (A.chart (chartOf j) z')) z = 0 := by
          rw [hzero.fderiv_eq]
          simp
        have hpd : ∀ k, ChartMetric.partialDeriv k
            (fun z' => ψ j (A.transition b (chartOf j) z')
              * v (A.chart (chartOf j) z')) z = 0 := by
          intro k
          simp only [ChartMetric.partialDeriv, hf, ContinuousLinearMap.zero_apply]
        simp only [ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse, hpd,
          mul_zero, Finset.sum_const_zero]
      · rw [pouPairing, lift, if_neg hmem']
    rw [hsum0]
    by_contra hne
    exact hmem (hGuvsupp m hne)

/-- **The global weighted IBP with lifted partition-of-unity pieces for partial charts.** The
pieces `pouPiece` and their pairings `pouPairing` are constructed as in the total case; the
reassembly `Σ_j pouPairing_j = Guv` is `sum_pouPairing_of_support`. The interface inputs are the
pointwise chart identifications `hD`/`hG`, the support of the test function in the base chart
image, the support of the constructed pieces and pairings in their chart images, and integrability
of the constructed integrands. -/
theorem globalWeightedIBP_of_pou_partial
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
    (hpair_src : ∀ j y, (A.metric (chartOf j)).gradInnerInverse
      (fun z' => u (A.chart (chartOf j) z'))
      (fun z' => ψ j (A.transition b (chartOf j) z') * v (A.chart (chartOf j) z')) y ≠ 0 →
      y ∈ A.source (chartOf j))
    (hψ_cc : ∀ j, HasCompactSupport (ψ j))
    (hproper : ∀ i j, ∀ K : Set (Vec (n + 1)), IsCompact K →
      IsCompact (A.transition i j ⁻¹' K))
    (hintL : ∀ j, Integrable (fun m => Du m * A.pouPiece b v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => A.pouPairing b (chartOf j) u v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  classical
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- support of a lifted piece: inside the base chart image and inside its own chart image
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
  -- the pieces' chart expressions vanish outside the chart source (proved)
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
  -- compact support of the pieces' chart expressions, from POU compact support and properness
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
  -- the `pouPiece` form of the chart-source support follows from the explicit form
  have hGuvsrc : ∀ j y, (A.metric (chartOf j)).gradInnerInverse
      (fun z' => u (A.chart (chartOf j) z'))
      (fun z' => A.pouPiece b v (ψ j) (A.chart (chartOf j) z')) y ≠ 0 →
      y ∈ A.source (chartOf j) := by
    intro j y hy
    apply hpair_src j y
    rwa [show (fun z' => A.pouPiece b v (ψ j) (A.chart (chartOf j) z'))
        = fun z' => ψ j (A.transition b (chartOf j) z') * v (A.chart (chartOf j) z') from
      funext fun z' => A.pouPiece_chart_of_support htrans (hψ_supp j) z'] at hy
  -- the piece pairing is supported in its chart image, from the chart-source support interface
  have hpair_supp : ∀ j m, A.pouPairing b (chartOf j) u v (ψ j) m ≠ 0 →
      m ∈ A.chart (chartOf j) '' A.source (chartOf j) := by
    intro j m hm
    obtain ⟨y, hy, hyz⟩ := support_lift_subset A (φ := fun z' =>
      (A.metric (chartOf j)).gradInnerInverse (fun z'' => u (A.chart (chartOf j) z''))
        (fun z'' => ψ j (A.transition b (chartOf j) z'')
          * v (A.chart (chartOf j) z'')) z') hm
    rw [← hyz]
    exact ⟨y, hpair_src j y hy, rfl⟩
  refine A.toOverlapAtlas.globalWeightedIBP_of_pouData b chartOf ψ f u v Du Guv
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
  · exact hpair_supp
  · exact hpiece_src
  · exact hGuvsrc
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

#print axioms Poincare.D13.ManifoldIBP.support_gradInnerInverse_subset
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_chart_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_apply_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPairing_apply_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.gradInnerInverse_eq_zero_of_eventuallyEq_zero
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.sum_pouPairing_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial
