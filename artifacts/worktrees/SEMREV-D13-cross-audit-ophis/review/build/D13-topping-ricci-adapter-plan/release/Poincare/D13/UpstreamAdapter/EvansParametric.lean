/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# Upstream adapter: Evans parametric-integral differentiation ↔ local D12 weighted-integral theorem

This file is part of the D13 upstream-adapter audit.  It transcribes the compact-support
differentiation-under-the-integral lemma of the pinned Frenzymath snapshot (package `Evans`,
`formalized-sources/Evans/EvansLib/Ch02/HeatIVP.lean:55`, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0) and re-proves it locally **through
the local D12 general theorem** `Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight`
(`release/Poincare/D12/EntropyVariation/WeightedIntegral.lean:83`).  This is a downstream
checked use of the local D12 theorem in the upstream statement's exact form: the same
mathematical family (dominated differentiation of a parameter integral), here against a
compactly-supported weight, which turns the domination hypothesis into a constant bound on
the compact support.

The upstream companion file `EvansLib/Ch02/ParametricIntegral.lean` (compact-parameter
all-orders smoothness, `hasFDerivAt_parametricIntegral_iteratedFDeriv` at line 143,
`contDiff_parametricIntegral` at line 263) belongs to the Evans spherical-mean chain and is
NOT re-verified here; it is recorded as an upstream source claim in the audit card.
-/

import Poincare.D12.EntropyVariation.WeightedIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Topology.MetricSpace.Bounded

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.UpstreamAdapter.Evans

/-! ## Differentiation under the integral against a compactly-supported weight -/

/-- **Upstream `Evans.EvansLib.hasDerivAt_integral_mul_hasCompactSupport`
(`formalized-sources/Evans/EvansLib/Ch02/HeatIVP.lean:55`), re-proved locally through the
local D12 weighted-integral theorem.**  For continuous compactly-supported `g`, and a
one-parameter kernel family `K` with continuous slices, jointly continuous `K'`, and
pointwise derivative `HasDerivAt (K · y) (K' s y) s` on an open `U ∋ s₀`, the parametrized
integral `s ↦ ∫ K s y · g y` is differentiable at `s₀` with the expected derivative.
The domination bound is the upstream constant `C'` on the closed ball × support, obtained
from continuity on the compact set; the application goes through
`Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight` with the fixed
weight `ρ = g`.  Class: upstream compiled theorem (locally re-verified via the local D12
general analytic theorem). -/
lemma hasDerivAt_integral_mul_hasCompactSupport
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {K K' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set ℝ} (hU : IsOpen U) {s₀ : ℝ}
    (hs₀ : s₀ ∈ U)
    (hKcont : ∀ s ∈ U, Continuous (fun y => K s y))
    (hK'cont : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => K' p.1 p.2)
      (U ×ˢ Set.univ))
    (hderiv : ∀ s ∈ U, ∀ y, HasDerivAt (fun s => K s y) (K' s y) s) :
    HasDerivAt (fun s => ∫ y, K s y * g y) (∫ y, K' s₀ y * g y) s₀ := by
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hcball : Metric.closedBall s₀ ε' ⊆ U := by
    intro z hz
    exact hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by simp [hε']; linarith))
  have hballU : Metric.ball s₀ ε' ⊆ U := (Metric.ball_subset_closedBall).trans hcball
  have hKset : IsCompact (Metric.closedBall s₀ ε' ×ˢ tsupport g) :=
    (isCompact_closedBall _ _).prod hgc
  have hcontφ : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => K' p.1 p.2 * g p.2)
      (Metric.closedBall s₀ ε' ×ˢ tsupport g) := by
    apply ContinuousOn.mul
    · exact hK'cont.mono (Set.prod_mono hcball (Set.subset_univ _))
    · exact (hg.comp continuous_snd).continuousOn
  obtain ⟨C, hC⟩ := hKset.exists_bound_of_continuousOn hcontφ
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hc : Continuous (fun y : EuclideanSpace ℝ (Fin n) => K' s₀ y) := by
    have := hK'cont.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y => ⟨hs₀, Set.mem_univ _⟩)
    convert this using 1
    rfl
  have hint : Integrable (fun y : EuclideanSpace ℝ (Fin n) => K s₀ y * g y) volume := by
    exact (((hKcont s₀ hs₀).mul hg).integrable_of_hasCompactSupport (μ := volume) hgc.mul_left)
  have hmeas : ∀ᶠ t in 𝓝 s₀, AEStronglyMeasurable (fun y => K t y * g y) :=
    Filter.eventually_of_mem (hU.mem_nhds hs₀)
      (fun s' hs' => ((hKcont s' hs').mul hg).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable (fun y => K' s₀ y * g y) := (hc.mul hg).aestronglyMeasurable
  have hderiv' : ∀ᵐ y, ∀ t ∈ Metric.ball s₀ ε', HasDerivAt (fun s => K s y) (K' t y) t :=
    Filter.Eventually.of_forall (fun y t ht => hderiv t (hballU ht) y)
  have hdom : ∀ᵐ y, ∀ t ∈ Metric.ball s₀ ε',
      ‖K' t y * g y‖ ≤ (tsupport g).indicator (fun _ => C') y :=
    Filter.Eventually.of_forall (fun y t ht => by
      by_cases hy : y ∈ tsupport g
      · rw [Set.indicator_of_mem hy]
        exact (hC (t, y) ⟨Metric.ball_subset_closedBall ht, hy⟩).trans (le_max_left _ _)
      · rw [image_eq_zero_of_notMem_tsupport hy, Set.indicator_of_notMem hy]
        simp)
  have hbound : Integrable ((tsupport g).indicator (fun _ => C') : EuclideanSpace ℝ (Fin n) → ℝ) := by
    rw [integrable_indicator_iff (isClosed_tsupport g).measurableSet]
    exact integrableOn_const (hs := hgc.measure_lt_top.ne)
  have hmain := Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight
    (μ := volume) (g := K) (g' := K') (ρ := g)
    (bound := (tsupport g).indicator (fun _ => C'))
    (t₀ := s₀) (s := Metric.ball s₀ ε')
    (Metric.ball_mem_nhds s₀ hε'pos) hmeas hint hmeas' hderiv' hdom hbound
  exact hmain.2

end Poincare.D13.UpstreamAdapter.Evans
