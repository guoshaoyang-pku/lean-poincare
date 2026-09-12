/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10 builder

# D10 — The two one-variable analytic lemmas behind the parabolic maximum principle

The classical weak maximum principle for subsolutions of the heat equation rests on two
elementary one-variable facts at a point `(x₀,t₀)` where a function attains its maximum:

* in the **time** direction: at a maximum on `[0,t₀]` which is attained at the right
  endpoint `t₀ > 0`, the left derivative is nonnegative
  (`hasDerivWithinAt_nonneg_of_isMaxOn_Icc`);
* in each **space** direction: at a local maximum, the second derivative is nonpositive
  (`deriv_deriv_nonpos_of_isLocalMax`).

Mathlib has the converse second-derivative tests (`isLocalMin_of_deriv_deriv_pos`,
`isLocalMax_of_deriv_deriv_neg`) but not the version needed here; both facts are proved
below from the mean value theorem and Mathlib's Fermat theorem for one-sided derivatives.
-/

import Poincare.D10.MaximumPrincipleRN.Basic

namespace Poincare.D10.MaximumPrincipleRN

open Set Filter
open scoped Topology

/-- **One-sided derivative at an interior maximum.**
If `w` has a maximum on `[0,t₀]`, attained at the right endpoint `t₀ > 0`, and `w` has a left
derivative `d` at `t₀` (i.e. a derivative within `[0,t₀]`), then `0 ≤ d`.

This is the time-direction half of the parabolic maximum principle. -/
theorem hasDerivWithinAt_nonneg_of_isMaxOn_Icc {w : ℝ → ℝ} {t₀ d : ℝ} (ht₀ : 0 < t₀)
    (hmax : ∀ s ∈ Icc 0 t₀, w s ≤ w t₀)
    (hd : HasDerivWithinAt w d (Icc 0 t₀) t₀) : 0 ≤ d := by
  have hseg : segment ℝ t₀ 0 ⊆ Icc 0 t₀ := by
    rw [segment_symm, segment_eq_Icc ht₀.le]
  have hy : (0 : ℝ) - t₀ ∈ posTangentConeAt (Icc 0 t₀) t₀ :=
    sub_mem_posTangentConeAt_of_segment_subset hseg
  have hmax' : IsLocalMaxOn w (Icc 0 t₀) t₀ :=
    eventually_of_mem self_mem_nhdsWithin hmax
  have h := hmax'.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt hy
  have h' : (0 - t₀) • d ≤ 0 := h
  rw [zero_sub, neg_smul, neg_nonpos] at h'
  rw [smul_eq_mul] at h'
  exact nonneg_of_mul_nonneg_right h' ht₀

/-- `f` is continuous on `[a,b]` as soon as it is differentiable on `(a,b)` and at the two
endpoints.  (Mathlib's `DifferentiableOn.continuousOn` only gives continuity on the open
interval.) -/
theorem continuousOn_Icc_of_differentiableOn {f : ℝ → ℝ} {a b : ℝ}
    (ha : DifferentiableAt ℝ f a) (hb : DifferentiableAt ℝ f b)
    (h : DifferentiableOn ℝ f (Ioo a b)) : ContinuousOn f (Icc a b) := by
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hlt | rfl
  · rcases lt_or_eq_of_le hx.2 with hlt' | rfl
    · exact ((h.differentiableAt (Ioo_mem_nhds hlt hlt')).continuousAt).continuousWithinAt
    · exact hb.continuousAt.continuousWithinAt
  · exact ha.continuousAt.continuousWithinAt

/-- **Second derivative test at a local maximum (weak form).**
If `f` has a local maximum at `a`, is differentiable in a neighbourhood of `a`, and `deriv f`
is differentiable at `a` with derivative `c`, then `c ≤ 0`.

Note the differentiability-in-a-neighbourhood hypothesis: `deriv` is the junk-value-zero
extension of the derivative, so a statement about `deriv (deriv f) a` alone would be false.

Proof: if `c > 0` then, since `deriv f a = 0`, the sign lemma
`eventually_nhdsWithin_sign_eq_of_deriv_pos` shows `deriv f > 0` on a right-neighbourhood of
`a`; on a small interval `[a,b]` the mean value theorem then gives `f b > f a`, contradicting
the local maximality of `f` at `a`. -/
theorem deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {a c : ℝ}
    (hmax : IsLocalMax f a) (hdiff : ∀ᶠ s in 𝓝 a, DifferentiableAt ℝ f s)
    (h2 : HasDerivAt (deriv f) c a) : c ≤ 0 := by
  rw [← not_lt]
  intro hc
  have hmax' : ∀ᶠ s in 𝓝 a, f s ≤ f a := hmax
  have h0 : deriv f a = 0 := hmax.deriv_eq_zero
  have hc' : deriv (deriv f) a > 0 := by rwa [h2.deriv]
  have hsign : ∀ᶠ y in 𝓝 a, SignType.sign (deriv f y) = SignType.sign (y - a) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hc' h0
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.mp hdiff
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.eventually_nhds_iff.mp hsign
  obtain ⟨ε₃, hε₃, h₃⟩ := Metric.eventually_nhds_iff.mp hmax'
  have hmin : 0 < min (min ε₁ ε₂) ε₃ := lt_min (lt_min hε₁ hε₂) hε₃
  set δ : ℝ := min (min ε₁ ε₂) ε₃ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact half_pos hmin
  have hδ_lt : δ < min (min ε₁ ε₂) ε₃ := by rw [hδdef]; exact half_lt_self hmin
  have hδ₁ : δ < ε₁ :=
    lt_of_lt_of_le (lt_of_lt_of_le hδ_lt (min_le_left _ _)) (min_le_left _ _)
  have hδ₂ : δ < ε₂ :=
    lt_of_lt_of_le (lt_of_lt_of_le hδ_lt (min_le_left _ _)) (min_le_right _ _)
  have hδ₃ : δ < ε₃ := lt_of_lt_of_le hδ_lt (min_le_right _ _)
  set b : ℝ := a + δ with hbdef
  have hab : a < b := by rw [hbdef]; linarith
  have hdist_le : ∀ y ∈ Icc a b, dist y a ≤ δ := by
    intro y hy
    rw [Real.dist_eq, abs_le]
    refine ⟨?_, ?_⟩
    · have : 0 ≤ y - a := by linarith [hy.1]
      linarith
    · have := hy.2
      rw [hbdef] at this
      linarith
  have hderiv_pos : ∀ y ∈ Ioo a b, 0 < deriv f y := by
    intro y hy
    have hd₂ : dist y a < ε₂ :=
      lt_of_le_of_lt (hdist_le y ⟨hy.1.le, hy.2.le⟩) hδ₂
    have hs : SignType.sign (deriv f y) = SignType.sign (y - a) := h₂ hd₂
    have : SignType.sign (y - a) = 1 := sign_pos (by linarith [hy.1])
    rw [this] at hs
    exact sign_eq_one_iff.mp hs
  have hda : DifferentiableAt ℝ f a := h₁ (by simpa using hε₁)
  have hdb : DifferentiableAt ℝ f b :=
    h₁ (lt_of_le_of_lt (hdist_le b ⟨hab.le, le_rfl⟩) hδ₁)
  have hdiffOn : DifferentiableOn ℝ f (Ioo a b) := by
    intro y hy
    have hmem : DifferentiableAt ℝ f y :=
      h₁ (lt_of_le_of_lt (hdist_le y ⟨hy.1.le, hy.2.le⟩) hδ₁)
    exact hmem.differentiableWithinAt
  have hcont : ContinuousOn f (Icc a b) :=
    continuousOn_Icc_of_differentiableOn hda hdb hdiffOn
  obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope f hab hcont hdiffOn
  have hquot : 0 < (f b - f a) / (b - a) := hξeq ▸ hderiv_pos ξ hξ
  have hb_a : 0 < b - a := by linarith
  have hfb_gt : f a < f b := by
    have := (div_pos_iff_of_pos_right hb_a).mp hquot
    linarith
  have hfb : f b ≤ f a := h₃ (lt_of_le_of_lt (hdist_le b ⟨hab.le, le_rfl⟩) hδ₃)
  linarith

end Poincare.D10.MaximumPrincipleRN
