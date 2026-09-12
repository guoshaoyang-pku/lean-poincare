/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Poincare.D13.ToppingAdapter.Core
import Poincare.Longrun.PDE.ContinuousInterface
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Poincare.D13.ToppingAdapter.Slab

**The continuous heat weak maximum principle on the slab `[a,b] × [0,T]`, proved from the
upstream Topping compact-space core.**

The local D2 interface `Poincare.Longrun.PDE.ContinuousHeatMaximumPrincipleInterface` and the
D7 `ContinuousHeatMaximumPrincipleConjecture` are *statement-only*: the pinned-mathlib probe
(D1) found no parabolic PDE theory.  The pinned Frenzymath snapshot contains exactly the missing
argument — the compact-space weak maximum principle of
`Topping/Topping/MaximumPrinciple/Core.lean` (transcribed verbatim in `Core.lean` here) — and
this module assembles it with the classical geometric input (the second-derivative test at an
interior spatial maximizer) to prove the slab maximum principle.

**Expanded hypotheses (standard regularity of the classical weak maximum principle).**  The
literal D2 `ContinuousHeatHypotheses` package records `deriv` and `iteratedDeriv 2` *values*
(pointwise equalities that also hold through the zero-fallback convention of `deriv`/`fderiv`
at points of non-differentiability), so it does not by itself imply that the two sides are the
actual derivatives.  The theorem below therefore takes the explicit regularity package
`SlabRegularity`: the time derivative `HasDerivAt` at every `(x,t)` of the slab interior, and
the spatial first/second `HasDerivAt` at every interior spatial point.  These are exactly the
classical `C¹`-in-time / `C²`-in-space hypotheses of the weak maximum principle for
`∂ₜu = ∂ₓ²u`; they are regularity conditions, strictly weaker than and not equivalent to the
conclusion (every solution with the regularity is nonpositive — the regularity alone implies
nothing about signs).

With those hypotheses the theorem proves, for every `u`, the conclusion of the D2 interface:

    ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0

so the mathematical content of the local blocker I2 ("the continuous parabolic maximum
principle cannot be proved / is a statement-only interface") is discharged here for classical
heat solutions by the upstream Topping argument, re-verified by the local kernel.  The literal
D2/D7 statement (without `SlabRegularity`) remains statement-only and is *not* claimed closed
by this file; see the D13 result card, semantic class "local proved theorem, expanded
hypotheses".
-/

open Set Filter
open scoped Topology
open Poincare.Longrun.PDE

namespace Poincare.D13.ToppingAdapter.Slab

/-! ## The second-derivative test at a local maximum -/

/-- **Math.** If `f` has a local maximum at `x`, `f` is differentiable at `x`, and `deriv f`
is differentiable at `x` with derivative `c`, then `c ≤ 0`.  (Classical second-derivative test
in `HasDerivAt` form; the converse sign gives the second-derivative test at a local minimum.)

Proof outline (classical): Fermat gives `deriv f x = 0`.  If `c > 0`, the slope limit of
`deriv f` at `x` forces `0 < deriv f y` for all `y` in a right neighbourhood `(x, x + ε)` of
`x` — in particular `f` is genuinely differentiable at every such `y` (otherwise `deriv f y`
would be the zero fallback, `deriv_zero_of_not_differentiableAt`), and `f` is continuous on
`Ico x (x + ε)`.  The convex mean-value growth lemma
`Convex.mul_sub_lt_image_sub_of_lt_deriv` with `C = 0` then gives
`0 < f (x + h) - f x` for every small `h > 0`, contradicting the local maximum. -/
lemma deriv_deriv_nonpos_of_isLocalMax {f : ℝ → ℝ} {x c : ℝ}
    (hmax : IsLocalMax f x) (hf : HasDerivAt f (deriv f x) x)
    (hdd : HasDerivAt (deriv f) c x) : c ≤ 0 := by
  by_contra hc
  have hcpos : 0 < c := lt_of_not_ge hc
  have hderivzero : deriv f x = 0 := hmax.hasDerivAt_eq_zero hf
  have hslope : Tendsto (slope (deriv f) x) (𝓝[≠] x) (𝓝 c) :=
    (hasDerivAt_iff_tendsto_slope.1 hdd)
  have hgt : ∀ᶠ y in 𝓝[≠] x, 0 < slope (deriv f) x y :=
    (tendsto_order.1 hslope).1 0 hcpos
  have hgtIoi : ∀ᶠ y in 𝓝[>] x, 0 < slope (deriv f) x y := by
    exact hgt.filter_mono (nhdsWithin_mono x (by intro y hy; exact ne_of_gt hy))
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hgtIoi with ⟨v, hv, hvs⟩
  rcases Metric.mem_nhds_iff.1 hv with ⟨ε, hε, hball⟩
  have hεsub : ∀ h : ℝ, h ∈ Ioo 0 ε → 0 < slope (deriv f) x (x + h) := by
    intro h hh
    have hmem : x + h ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
      simpa [add_sub_cancel_left] using (abs_lt.2 ⟨lt_trans (neg_lt_zero.mpr hε) hh.1, hh.2⟩)
    exact hvs ⟨hball hmem, lt_add_of_pos_right x hh.1⟩
  have hderivpos : ∀ h : ℝ, h ∈ Ioo 0 ε → 0 < deriv f (x + h) := by
    intro h hh
    have hpos := hεsub h hh
    have hval : slope (deriv f) x (x + h) = deriv f (x + h) / h := by
      rw [slope]
      simp only [add_sub_cancel_left, hderivzero, smul_eq_mul, vsub_eq_sub, sub_zero]
      rw [div_eq_mul_inv]
      ring
    rw [hval] at hpos
    simpa using ((lt_div_iff₀ hh.1).mp hpos)
  have hdiff_on : DifferentiableOn ℝ f (Ioo x (x + ε)) := by
    intro y hy
    have hpos : 0 < deriv f y := by
      have := hderivpos (y - x) ⟨sub_pos.2 hy.1, by linarith [hy.2]⟩
      simpa [sub_add_cancel] using this
    by_contra hnd
    have hnd' : ¬ DifferentiableAt ℝ f y := by
      intro hdat
      exact hnd (hdat.differentiableWithinAt)
    exact (ne_of_gt hpos) (deriv_zero_of_not_differentiableAt hnd')
  have hcont_on : ContinuousOn f (Ico x (x + ε)) := by
    intro y hy
    rcases lt_or_eq_of_le hy.1 with hxy | hxy
    · exact ((hdiff_on.differentiableAt (isOpen_Ioo.mem_nhds ⟨hxy, hy.2⟩)).continuousAt).continuousWithinAt
    · subst y
      exact hf.continuousAt.continuousWithinAt
  have hgrowth := (convex_Ico (x : ℝ) (x + ε)).mul_sub_lt_image_sub_of_lt_deriv
    (f := f) hcont_on (by simpa [interior_Ico] using hdiff_on) (C := 0) (by
      intro y hy
      have hy' : y ∈ Ioo x (x + ε) := by simpa [interior_Ico] using hy
      have hpos : 0 < deriv f y := by
        have := hderivpos (y - x) ⟨sub_pos.2 hy'.1, by linarith [hy'.2]⟩
        simpa [sub_add_cancel] using this
      simpa [interior_Ico] using hpos)
  rcases Metric.mem_nhds_iff.1 hmax with ⟨ε', hε', hε'le⟩
  let h : ℝ := min (ε / 2) (ε' / 2)
  have hhpos : 0 < h := lt_min (half_pos hε) (half_pos hε')
  have hhltε' : h < ε' := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε')
  have hball' : x + h ∈ Metric.ball x ε' := by
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
    simpa [sub_eq_add_neg] using (abs_lt.2 ⟨by linarith [hhpos], hhltε'⟩)
  have hle' : f (x + h) ≤ f x := hε'le hball'
  have hgt' : 0 < f (x + h) - f x := by
    have := hgrowth x ⟨le_rfl, by linarith [hε]⟩ (x + h)
      ⟨by linarith, by dsimp only [h]; linarith [min_le_left (ε / 2) (ε' / 2), half_lt_self hε]⟩
      (by linarith)
    simpa using this
  linarith

/-- **Math.** If `f` has a local maximum at `x`, `f` is differentiable at `x`, and the second
iterated derivative exists in the `HasDerivAt` sense, then `iteratedDeriv 2 f x ≤ 0`. -/
lemma iteratedDeriv_two_nonpos_of_isLocalMax {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hf : HasDerivAt f (deriv f x) x)
    (hdd : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x) :
    iteratedDeriv 2 f x ≤ 0 := by
  simpa [iteratedDeriv_succ', iteratedDeriv_zero] using
    (deriv_deriv_nonpos_of_isLocalMax (f := f) (x := x) hmax hf hdd)

/-! ## The slab regularity package (expanded hypotheses) -/

/-- **The expanded regularity hypotheses of the classical weak maximum principle for the slab
heat equation** `∂ₜu = ∂ₓ²u` on `[a,b] × [0,T]`:

* time: at every slab point `(x,t)` with `t` interior, the time derivative
  `HasDerivAt (u x) (deriv (u x) t) t` holds (C¹ in time);
* space: at every interior spatial point, both `HasDerivAt (u · t) (deriv (u · t) x) x` and the
  second derivative `HasDerivAt (deriv (u · t)) (iteratedDeriv 2 (u · t) x) x` hold (C² in
  space).

Together with `ContinuousHeatHypotheses.heat_equation` these identify the recorded `deriv` /
`iteratedDeriv 2` *values* with the genuine derivatives.  These are regularity conditions only
(they say nothing about signs or bounds), and they are exactly what the classical weak maximum
principle assumes; they are strictly not equivalent to the conclusion. -/
def SlabRegularity (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop :=
  (∀ x t, x ∈ Icc a b → t ∈ Ioo 0 T →
    HasDerivAt (fun s => u x s) (deriv (fun s => u x s) t) t) ∧
  (∀ x t, x ∈ Ioo a b → t ∈ Ioo 0 T →
    HasDerivAt (fun y => u y t) (deriv (fun y => u y t) x) x ∧
    HasDerivAt (deriv (fun y => u y t)) (iteratedDeriv 2 (fun y => u y t) x) x)

/-! ## The slab maximum principle via the Topping compact-space core -/

/-- **Math.** For every end time `T' < T`, nonpositivity holds on `[a,b] × [0,T']`.  This is
the Topping compact-space argument on the spatial domain `X = Icc a b` (compact, nonempty
because `a ≤ b`), with `K = 0`: at every strictly positive time, a positive spatial maximizer
`x` of `u(·,t)` must lie in the open interval `(a,b)` (the lateral boundary data are
nonpositive), so the second-derivative test gives `∂ₓ²u ≤ 0` at `x`; by the heat equation
`∂ₜu = ∂ₓ²u ≤ 0 = 0 · u`.  The time differentiability of the core argument is available at
every maximizer time because `0 < t ≤ T' < T` puts `t` in `Ioo 0 T` (hence the positive-time
variant `nonpos_of_forall_isMax_time_deriv_le_of_pos'` of the transcribed upstream theorem). -/
theorem slab_nonpos_of_lt (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a ≤ b)
    (h : ContinuousHeatHypotheses u a b T) (hreg : SlabRegularity u a b T)
    {T' : ℝ} (hT' : 0 ≤ T') (hT'T : T' < T) :
    ∀ x, x ∈ Icc a b → ∀ t, t ∈ Icc 0 T' → u x t ≤ 0 := by
  classical
  letI : CompactSpace (Icc a b) := isCompact_iff_compactSpace.1 isCompact_Icc
  letI : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  have hmaxhyp : ∀ t ∈ Icc 0 T', 0 < t → ∀ x : Icc a b, 0 < u x.1 t →
      (∀ y : Icc a b, u y.1 t ≤ u x.1 t) → deriv (fun s => u x.1 s) t ≤ (0 : ℝ) * u x.1 t := by
    intro t ht htpos x hxpos hxmax
    have htT : t < T := lt_of_le_of_lt ht.2 hT'T
    have hlat : u a t ≤ 0 ∧ u b t ≤ 0 :=
      h.lateral_nonpos t ⟨ht.1, le_trans ht.2 hT'T.le⟩
    have hxa : x.1 ≠ a := by
      intro hxa
      rw [hxa] at hxpos
      exact (not_lt_of_ge hlat.1) hxpos
    have hxb : x.1 ≠ b := by
      intro hxb
      rw [hxb] at hxpos
      exact (not_lt_of_ge hlat.2) hxpos
    have hxIoo : x.1 ∈ Ioo a b :=
      ⟨lt_of_le_of_ne x.2.1 hxa.symm, lt_of_le_of_ne x.2.2 hxb⟩
    have hlocalmax : IsLocalMax (fun y : ℝ => u y t) x.1 := by
      filter_upwards [isOpen_Ioo.mem_nhds hxIoo] with y hy
      exact hxmax ⟨y, ⟨le_of_lt hy.1, le_of_lt hy.2⟩⟩
    have hregx := hreg.2 x.1 t hxIoo ⟨htpos, htT⟩
    have hsecond : iteratedDeriv 2 (fun y : ℝ => u y t) x.1 ≤ 0 :=
      iteratedDeriv_two_nonpos_of_isLocalMax hlocalmax hregx.1 hregx.2
    have hheat : deriv (fun s : ℝ => u x.1 s) t =
        iteratedDeriv 2 (fun y : ℝ => u y t) x.1 :=
      h.heat_equation x.1 t x.2 ⟨htpos, htT⟩
    rw [hheat, zero_mul]
    exact hsecond
  have hcontT : ContinuousOn (fun z : (Icc a b) × ℝ => u z.1.1 z.2)
      ((Set.univ : Set (Icc a b)) ×ˢ Icc 0 T') := by
    have hφ : Continuous fun z : (Icc a b) × ℝ => (z.1.1, z.2) := by
      fun_prop
    exact h.continuous_on_slab.comp hφ.continuousOn (by
      intro z hz
      exact ⟨z.1.2, ⟨hz.2.1, le_trans hz.2.2 hT'T.le⟩⟩)
  have hderivT : ∀ x : Icc a b, ∀ t ∈ Icc 0 T', 0 < t →
      HasDerivWithinAt (fun s => u x.1 s) (deriv (fun s => u x.1 s) t) (Icc 0 T') t := by
    intro x t ht htpos
    exact (hreg.1 x.1 t x.2 ⟨htpos, lt_of_le_of_lt ht.2 hT'T⟩).hasDerivWithinAt
  have hnonpos := Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'
    (X := Icc a b) (w := fun x t => u x.1 t) (wt := fun x t => deriv (fun s => u x.1 s) t)
    (T := T') (K := 0) hT' hcontT hderivT hmaxhyp (fun x => h.initial_nonpos x.1 x.2)
  intro x hx t ht
  exact hnonpos ⟨x, hx⟩ t ht

/-- **Math.** The continuous heat weak maximum principle on the slab `[a,b] × [0,T]`: every
classical (`SlabRegularity`) heat solution with nonpositive initial and lateral data stays
nonpositive.  For `t < T` this is `slab_nonpos_of_lt` on the subinterval `[0,T']` with
`t < T' < T`; at the terminal time `t = T` it follows by continuity of `s ↦ u x s` on
`Icc 0 T` from nonpositivity on `Ico 0 T` (a positive terminal value would persist on a
relative neighbourhood of `T` inside `Icc 0 T`, which meets `Ico 0 T`).  The cases `T ≤ 0`
are the initial datum (for `T = 0`) or vacuous (for `T < 0`).

This is the upstream Topping compact-space weak maximum principle assembled with the classical
second-derivative test: the mathematical content of the D2/D7 statement-only interface
`ContinuousHeatMaximumPrincipleInterface` for classical solutions. -/
theorem continuousHeatMaximumPrinciple_of_topping (u : ℝ → ℝ → ℝ) {a b T : ℝ}
    (hab : a ≤ b) (h : ContinuousHeatHypotheses u a b T) (hreg : SlabRegularity u a b T) :
    ∀ x, x ∈ Icc a b → ∀ t, t ∈ Icc 0 T → u x t ≤ 0 := by
  classical
  intro x hx t ht
  by_cases hTpos : 0 < T
  · by_cases htT : t = T
    · subst t
      have hcont_x : ContinuousOn (fun s : ℝ => u x s) (Icc 0 T) := by
        have hφ : Continuous fun s : ℝ => (x, s) := by
          fun_prop
        exact h.continuous_on_slab.comp hφ.continuousOn (by
          intro s hs
          exact ⟨hx, hs⟩)
      have hlt_all : ∀ s ∈ Ico 0 T, u x s ≤ 0 := by
        intro s hs
        by_cases hspos : 0 < s
        · let T' : ℝ := (s + T) / 2
          have hsT' : s < T' := by dsimp only [T']; linarith [hs.2]
          have hT'T : T' < T := by dsimp only [T']; linarith [hs.2]
          have hnonpos := slab_nonpos_of_lt u hab h hreg (by linarith [hs.1]) hT'T
          exact hnonpos x hx s ⟨hs.1, hsT'.le⟩
        · have hs0 : s = 0 := le_antisymm (le_of_not_gt hspos) hs.1
          subst s
          exact h.initial_nonpos x hx
      by_contra hneg
      have hposT : 0 < u x T := lt_of_not_ge hneg
      have hTend : Tendsto (fun s : ℝ => u x s) (𝓝[Icc 0 T] T) (𝓝 (u x T)) :=
        hcont_x.continuousWithinAt ⟨hTpos.le, le_rfl⟩
      have hpos_event : ∀ᶠ s in 𝓝[Icc 0 T] T, 0 < u x s := (tendsto_order.1 hTend).1 0 hposT
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpos_event with ⟨v, hv, hvs⟩
      rcases Metric.mem_nhds_iff.1 hv with ⟨ε, hε, hball⟩
      let s : ℝ := T - min ε (T / 2) / 2
      have hsneg : s - T < 0 := by
        dsimp only [s]
        linarith [half_pos (lt_min hε (half_pos hTpos))]
      have hs_ball : s ∈ Metric.ball T ε := by
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
        rw [abs_of_neg hsneg]
        dsimp only [s]
        have hmineq : -(T - min ε (T / 2) / 2 - T) = min ε (T / 2) / 2 := by ring
        rw [hmineq]
        have hle : min ε (T / 2) / 2 ≤ ε / 2 :=
          div_le_div_of_nonneg_right (min_le_left ε (T / 2)) (by norm_num : (0 : ℝ) ≤ 2)
        exact lt_of_le_of_lt hle (half_lt_self hε)
      have hspos : 0 ≤ s := by
        dsimp only [s]
        linarith [div_le_div_of_nonneg_right (min_le_right ε (T / 2))
          (by norm_num : (0 : ℝ) ≤ 2), hTpos]
      have hslt : s < T := by
        dsimp only [s]
        linarith [half_pos (lt_min hε (half_pos hTpos))]
      have hpos_s : 0 < u x s := hvs ⟨hball hs_ball, ⟨hspos, le_of_lt hslt⟩⟩
      exact (not_lt_of_ge (hlt_all s ⟨hspos, hslt⟩)) hpos_s
    · have htlt : t < T := lt_of_le_of_ne ht.2 htT
      let T' : ℝ := (t + T) / 2
      have htT' : t < T' := by dsimp only [T']; linarith [htlt]
      have hT'T : T' < T := by dsimp only [T']; linarith [htlt]
      have hnonpos := slab_nonpos_of_lt u hab h hreg (by dsimp only [T']; linarith [ht.1, hTpos]) hT'T
      exact hnonpos x hx t ⟨ht.1, htT'.le⟩
  · by_cases hT0 : T = 0
    · have ht0 : t = 0 := le_antisymm (by rw [hT0] at ht; exact ht.2) ht.1
      subst t
      exact h.initial_nonpos x hx
    · have hTneg : T < 0 := lt_of_le_of_ne (le_of_not_gt hTpos) hT0
      exact False.elim (not_lt_of_ge ht.1 (lt_of_le_of_lt ht.2 hTneg))
