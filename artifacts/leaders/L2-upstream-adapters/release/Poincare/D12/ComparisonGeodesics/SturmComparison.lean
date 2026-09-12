/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D12 — Sturm comparison for the nonconstant scalar Jacobi equation

This file proves the classical **Sturm comparison theorem** for the scalar Jacobi
equation with *nonconstant* curvature coefficient, in the version needed for geodesic
comparison geometry:

    k₂ ≤ k₁ on [a,b],
    uᵢ'' + kᵢ·uᵢ = 0 on (a,b),
    u₁(a) = u₂(a) = 0,  u₂(b) = 0,  u₂ > 0 on (a,b)
    ⟹  u₁ has a zero in (a,b)  ∨  k₁ = k₂ on (a,b).

The proof is the classical Wronskian argument, and it is **division-free**: the
Wronskian `W = u₂·u₁' − u₁·u₂'` is a polynomial expression in the solution data, so the
"no division at zero" requirement holds by construction even though `u₁(a) = u₂(a) = 0`.

Everything is proved from the pointwise `HasDerivAt` data of `JacobiSolutionOn`; no
comparison theorem, uniqueness theorem or ODE existence theorem is assumed.
-/
import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.D12.ComparisonGeodesics

/-! ## The Wronskian derivative -/

/-- The derivative of the Wronskian `W = u₂·u₁' − u₁·u₂'` along two solutions of the
scalar Jacobi equation: `W' = (k₂ − k₁)·u₁·u₂`. -/
theorem wronskian_hasDerivAt {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAtR (wronskian u₁ du₁ u₂ du₂) ((k₂ t - k₁ t) * u₁ t * u₂ t) t := by
  have h₁ : HasDerivAt (fun s => u₂ s * du₁ s)
      (du₂ t * du₁ t + u₂ t * ddu₁ t) t :=
    (h2.hasDerivAt_u ht).mul (h1.hasDerivAt_du ht)
  have h₂ : HasDerivAt (fun s => u₁ s * du₂ s)
      (du₁ t * du₂ t + u₁ t * ddu₂ t) t :=
    (h1.hasDerivAt_u ht).mul (h2.hasDerivAt_du ht)
  have hder : (du₂ t * du₁ t + u₂ t * ddu₁ t - (du₁ t * du₂ t + u₁ t * ddu₂ t))
      = (k₂ t - k₁ t) * u₁ t * u₂ t := by
    rw [h1.eq_secondDeriv ht, h2.eq_secondDeriv ht]
    ring
  have hsub : HasDerivAtR (wronskian u₁ du₁ u₂ du₂)
      (du₂ t * du₁ t + u₂ t * ddu₁ t - (du₁ t * du₂ t + u₁ t * ddu₂ t)) t := by
    exact h₁.sub h₂
  convert hsub using 1
  exact hder.symm

/-- Pointwise form of the Wronskian derivative. -/
theorem wronskian_deriv {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b) {t : ℝ} (ht : t ∈ Ioo a b) :
    deriv (wronskian u₁ du₁ u₂ du₂) t = (k₂ t - k₁ t) * u₁ t * u₂ t :=
  (wronskian_hasDerivAt h1 h2 ht).deriv

/-- The Wronskian is continuous on the closed interval. -/
theorem wronskian_continuousOn {u₁ du₁ u₂ du₂ : ℝ → ℝ} {a b : ℝ}
    (h1 : ContinuousOn u₁ (Icc a b)) (h1d : ContinuousOn du₁ (Icc a b))
    (h2 : ContinuousOn u₂ (Icc a b)) (h2d : ContinuousOn du₂ (Icc a b)) :
    ContinuousOn (wronskian u₁ du₁ u₂ du₂) (Icc a b) := by
  unfold wronskian
  exact (h2.mul h1d).sub (h1.mul h2d)

/-- The Wronskian is differentiable on the open interval. -/
theorem wronskian_differentiableOn {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b) :
    DifferentiableOn ℝ (wronskian u₁ du₁ u₂ du₂) (Ioo a b) := by
  intro t ht
  exact (wronskian_hasDerivAt h1 h2 ht).differentiableAt.differentiableWithinAt

/-- If `k₂ ≤ k₁` and `u₁·u₂ ≥ 0` on `(a,b)`, the Wronskian is antitone on `[a,b]`. -/
theorem wronskian_antitoneOn_of_le {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (_hab : a ≤ b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₂ t ≤ k₁ t)
    (hsign : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 ≤ u₁ t * u₂ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b) :
    AntitoneOn (wronskian u₁ du₁ u₂ du₂) (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
  · exact wronskian_continuousOn h1.continuousOn_u h1.continuousOn_du
      h2.continuousOn_u h2.continuousOn_du
  · simpa [interior_Icc] using wronskian_differentiableOn h1 h2
  · intro t ht
    rw [interior_Icc] at ht
    rw [wronskian_deriv h1 h2 ht]
    have h₁ : (k₂ t - k₁ t) * (u₁ t * u₂ t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hk ht)) (hsign ht)
    simpa [mul_assoc] using h₁

/-! ## Endpoint sign lemmas -/

/-- If `u₂ > 0` on `(a,b)`, `u₂ b = 0` and `u₂` is differentiable at `b`, then
`u₂' b ≤ 0`.  (Endpoint one-sided derivative sign, via the slope limit from the left.) -/
theorem deriv_nonpos_of_posOn_Ioo_of_eq_at_right {u du : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hpos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u t) (hz : u b = 0)
    (hd : HasDerivAtR u (du b) b) : du b ≤ 0 := by
  have hlim' : Tendsto (slope u b) (𝓝[≠] b) (𝓝 (du b)) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have hlim : Tendsto (slope u b) (𝓝[<] b) (𝓝 (du b)) :=
    hlim'.mono_left (nhdsWithin_mono b (by intro x hx hxb; exact (ne_of_lt hx) hxb))
  refine le_of_tendsto_of_frequently hlim ?_
  refine Eventually.frequently ?_
  change {t | slope u b t ≤ 0} ∈ 𝓝[<] b
  rw [mem_nhdsWithin]
  refine ⟨Ioo a (b + 1), isOpen_Ioo, ⟨hab, lt_add_one b⟩, ?_⟩
  intro t ht
  rcases ht with ⟨htIoo, htlt⟩
  have htIoo' : t ∈ Ioo a b := ⟨htIoo.1, htlt⟩
  have hden : t - b < 0 := sub_neg.mpr htlt
  have hle : (u t - u b) / (t - b) ≤ 0 := by
    refine div_nonpos_of_nonneg_of_nonpos ?_ (le_of_lt hden)
    rw [hz]
    simpa using le_of_lt (hpos htIoo')
  simpa [slope, div_eq_mul_inv, mul_comm] using hle

/-- If `u₁ > 0` on `(a,b)` and `u₁` is continuous on `[a,b]`, then `u₁ b ≥ 0`. -/
theorem nonneg_of_continuousOn_of_posOn_Ioo {u : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn u (Icc a b)) (hpos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u t) :
    0 ≤ u b := by
  by_contra h
  have hbneg : u b < 0 := lt_of_not_ge h
  have hct : ContinuousWithinAt u (Icc a b) b :=
    hcont.continuousWithinAt (Set.right_mem_Icc.mpr hab.le)
  have hev : ∀ᶠ t in 𝓝[Icc a b] b, u t < 0 := hct (isOpen_Iio.mem_nhds hbneg)
  change {t | u t < 0} ∈ 𝓝[Icc a b] b at hev
  rw [mem_nhdsWithin] at hev
  rcases hev with ⟨s, hso, hsb, hs⟩
  rcases (Metric.isOpen_iff.mp hso) b hsb with ⟨δ, hδpos, hδsub⟩
  let δ₀ : ℝ := min (δ / 2) ((b - a) / 2)
  have hδ₀pos : 0 < δ₀ := lt_min (half_pos hδpos) (half_pos (sub_pos.mpr hab))
  have hδ₀small : δ₀ < b - a :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self (sub_pos.mpr hab))
  let t : ℝ := b - δ₀
  have htlt : t < b := sub_lt_self b hδ₀pos
  have hagt : a < t := by linarith
  have htIoo : t ∈ Ioo a b := ⟨hagt, htlt⟩
  have hts : t ∈ s := hδsub (by
    have hdist' : dist t b < δ := by
      rw [Real.dist_eq, abs_sub_comm]
      have : |b - t| = δ₀ := by simp [t, abs_of_nonneg hδ₀pos.le]
      rw [this]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδpos)
    exact Metric.mem_ball.mpr hdist')
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self htIoo
  have hneg : u t < 0 := hs ⟨hts, htIcc⟩
  exact (not_lt.mpr (le_of_lt (hpos htIoo))) hneg

/-! ## The Sturm comparison theorem -/

/-- **Sturm comparison (positive case).**  If `k₂ ≤ k₁` on `[a,b]`, `u₁`, `u₂` solve the
respective Jacobi equations, `u₁(a) = u₂(a) = 0`, `u₂(b) = 0`, `u₂ > 0` on `(a,b)`, and
`u₁ > 0` on `(a,b)`, then `k₁ = k₂` on `(a,b)` — otherwise the monotone Wronskian would
force a contradiction. -/
theorem sturm_zero_comparison_of_pos {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1a : u₁ a = 0) (hu2a : u₂ a = 0) (hu2b : u₂ b = 0)
    (hu1pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₁ t)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₂ t)
    (hdu2b : HasDerivAtR u₂ (du₂ b) b) :
    ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₁ t = k₂ t := by
  -- The Wronskian is antitone on [a,b] and vanishes at both endpoints.
  have hWant : AntitoneOn (wronskian u₁ du₁ u₂ du₂) (Icc a b) := by
    refine wronskian_antitoneOn_of_le hab.le hk ?_ h1 h2
    intro t ht
    exact mul_nonneg (le_of_lt (hu1pos ht)) (le_of_lt (hu2pos ht))
  have hW0a : wronskian u₁ du₁ u₂ du₂ a = 0 := by
    simp [wronskian, hu1a, hu2a]
  have hdu2b_nonpos : du₂ b ≤ 0 :=
    deriv_nonpos_of_posOn_Ioo_of_eq_at_right hab hu2pos hu2b hdu2b
  have hu1b_nonneg : 0 ≤ u₁ b :=
    nonneg_of_continuousOn_of_posOn_Ioo hab h1.continuousOn_u hu1pos
  have hW0b : wronskian u₁ du₁ u₂ du₂ b = 0 := by
    have hWble : wronskian u₁ du₁ u₂ du₂ b ≤ wronskian u₁ du₁ u₂ du₂ a :=
      hWant (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab.le
    rw [hW0a] at hWble
    have hnonneg : 0 ≤ wronskian u₁ du₁ u₂ du₂ b := by
      rw [wronskian, hu2b]
      have h₁ : u₁ b * du₂ b ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hu1b_nonneg hdu2b_nonpos
      linarith
    linarith
  -- Hence W ≡ 0 on [a,b], so W' ≡ 0 on (a,b), so (k₂−k₁)·u₁·u₂ ≡ 0 on (a,b).
  intro t ht
  have hWconst : ∀ x ∈ Icc a b, wronskian u₁ du₁ u₂ du₂ x = 0 := by
    intro x hx
    have hle1 : wronskian u₁ du₁ u₂ du₂ x ≤ wronskian u₁ du₁ u₂ du₂ a :=
      hWant (Set.left_mem_Icc.mpr hab.le) hx hx.1
    have hle2 : wronskian u₁ du₁ u₂ du₂ b ≤ wronskian u₁ du₁ u₂ du₂ x :=
      hWant hx (Set.right_mem_Icc.mpr hab.le) hx.2
    rw [hW0a] at hle1
    rw [hW0b] at hle2
    linarith
  have hWderivZero : (k₂ t - k₁ t) * u₁ t * u₂ t = 0 := by
    have hWt : HasDerivAtR (wronskian u₁ du₁ u₂ du₂) ((k₂ t - k₁ t) * u₁ t * u₂ t) t :=
      wronskian_hasDerivAt h1 h2 ht
    have hEqOn : wronskian u₁ du₁ u₂ du₂ =ᶠ[𝓝 t] fun _ => 0 := by
      change {x | wronskian u₁ du₁ u₂ du₂ x = 0} ∈ 𝓝 t
      rw [mem_nhds_iff_exists_Ioo_subset]
      refine ⟨a, b, ht, ?_⟩
      intro x hx
      exact hWconst x (Ioo_subset_Icc_self hx)
    have hder : deriv (wronskian u₁ du₁ u₂ du₂) t = 0 := by
      rw [hEqOn.deriv_eq]
      exact deriv_const t 0
    rw [← hWt.deriv, hder]
  have hk0 : k₂ t - k₁ t = 0 := by
    have h₁ : (k₂ t - k₁ t) * u₁ t = 0 :=
      (mul_eq_zero.mp hWderivZero).resolve_right (ne_of_gt (hu2pos ht))
    exact (mul_eq_zero.mp h₁).resolve_right (ne_of_gt (hu1pos ht))
  linarith

/-- Sign-constancy: a continuous function on `(a,b)` which never vanishes is either
everywhere positive or everywhere negative there. -/
lemma sign_constant_of_no_zero {u : ℝ → ℝ} {a b : ℝ} (hcont : ContinuousOn u (Ioo a b))
    (hz : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → u t ≠ 0) :
    (∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u t) ∨ (∀ ⦃t : ℝ⦄, t ∈ Ioo a b → u t < 0) := by
  by_cases hpos : ∃ t ∈ Ioo a b, 0 < u t
  · left
    intro t ht
    by_contra hnot
    have hneg : u t < 0 := lt_of_le_of_ne (le_of_not_gt hnot) (hz ht)
    rcases hpos with ⟨s, hs, hspos⟩
    rcases le_total s t with hst | hts
    · have hsubst : Icc s t ⊆ Ioo a b := by
        intro c hc
        exact ⟨lt_of_lt_of_le hs.1 hc.1, lt_of_le_of_lt hc.2 ht.2⟩
      have hcont' : ContinuousOn (-u) (Icc s t) := (hcont.mono hsubst).neg
      have hneg₁ : (-u) s ≤ 0 := by
        rw [Pi.neg_apply]
        exact neg_nonpos.mpr (le_of_lt hspos)
      have hpos₂ : 0 ≤ (-u) t := by
        rw [Pi.neg_apply]
        exact neg_nonneg.mpr (le_of_lt hneg)
      have hzero : (0 : ℝ) ∈ (-u) '' Icc s t :=
        intermediate_value_Icc hst hcont' ⟨hneg₁, hpos₂⟩
      rcases hzero with ⟨c, hc, hceq⟩
      exact hz (hsubst hc) (by rw [Pi.neg_apply] at hceq; exact neg_eq_zero.mp hceq)
    · have hsubst : Icc t s ⊆ Ioo a b := by
        intro c hc
        exact ⟨lt_of_lt_of_le ht.1 hc.1, lt_of_le_of_lt hc.2 hs.2⟩
      have hcont' : ContinuousOn (-u) (Icc t s) := (hcont.mono hsubst).neg
      have hneg₁ : (-u) s ≤ 0 := by
        rw [Pi.neg_apply]
        exact neg_nonpos.mpr (le_of_lt hspos)
      have hpos₂ : 0 ≤ (-u) t := by
        rw [Pi.neg_apply]
        exact neg_nonneg.mpr (le_of_lt hneg)
      have hmem : (0 : ℝ) ∈ Icc ((-u) s) ((-u) t) := ⟨hneg₁, hpos₂⟩
      have hzero : (0 : ℝ) ∈ (-u) '' Icc t s :=
        intermediate_value_Icc' hts hcont' hmem
      rcases hzero with ⟨c, hc, hceq⟩
      exact hz (hsubst hc) (by rw [Pi.neg_apply] at hceq; exact neg_eq_zero.mp hceq)
  · right
    intro t ht
    have hle : u t ≤ 0 := le_of_not_gt (by intro hg; exact hpos ⟨t, ht, hg⟩)
    exact lt_of_le_of_ne hle (hz ht)

/-- **Sturm comparison theorem** for the nonconstant scalar Jacobi equation.  If
`k₂ ≤ k₁` on `[a,b]`, `uᵢ'' + kᵢ·uᵢ = 0` on `(a,b)`, `u₁(a) = u₂(a) = 0`,
`u₂(b) = 0` and `u₂ > 0` on `(a,b)`, then either `u₁` has a zero in `(a,b)` or
`k₁ = k₂` identically on `(a,b)`.  The proof is division-free. -/
theorem sturm_zero_comparison {k₁ k₂ u₁ du₁ ddu₁ u₂ du₂ ddu₂ : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hk : ∀ ⦃t : ℝ⦄, t ∈ Icc a b → k₂ t ≤ k₁ t)
    (h1 : JacobiSolutionOn k₁ u₁ du₁ ddu₁ a b)
    (h2 : JacobiSolutionOn k₂ u₂ du₂ ddu₂ a b)
    (hu1a : u₁ a = 0) (hu2a : u₂ a = 0) (hu2b : u₂ b = 0)
    (hu2pos : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < u₂ t)
    (hdu2b : HasDerivAtR u₂ (du₂ b) b) :
    (∃ c ∈ Ioo a b, u₁ c = 0) ∨ (∀ ⦃t : ℝ⦄, t ∈ Ioo a b → k₁ t = k₂ t) := by
  by_cases hz : ∃ c ∈ Ioo a b, u₁ c = 0
  · exact Or.inl hz
  · right
    have hnozero : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → u₁ t ≠ 0 := by
      intro t ht he
      exact hz ⟨t, ht, he⟩
    have hsign := sign_constant_of_no_zero (h1.continuousOn_u.mono Ioo_subset_Icc_self) hnozero
    rcases hsign with hpos | hneg
    · exact sturm_zero_comparison_of_pos hab (fun t ht => hk (Ioo_subset_Icc_self ht))
        h1 h2 hu1a hu2a hu2b hpos hu2pos hdu2b
    · have hpos' : ∀ ⦃t : ℝ⦄, t ∈ Ioo a b → 0 < -u₁ t := by
        intro t ht
        exact neg_pos.mpr (hneg ht)
      have hneg₁ : JacobiSolutionOn k₁ (-u₁) (-du₁) (-ddu₁) a b := h1.neg
      have hu1a' : (-u₁) a = 0 := by rw [Pi.neg_apply, hu1a, neg_zero]
      exact sturm_zero_comparison_of_pos hab (fun t ht => hk (Ioo_subset_Icc_self ht))
        hneg₁ h2 hu1a' hu2a hu2b hpos' hu2pos hdu2b

end Poincare.D12.ComparisonGeodesics
