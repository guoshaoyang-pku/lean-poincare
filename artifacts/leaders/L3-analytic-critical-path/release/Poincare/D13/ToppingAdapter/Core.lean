/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact

/-!
# Poincare.D13.ToppingAdapter.Core

**Upstream provenance.** This module is a verbatim transcription of the compact-space core of
the weak maximum principle from the pinned Frenzymath snapshot,

  `formalized-sources/Topping/Topping/MaximumPrinciple/Core.lean`

(commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`).  The upstream namespace `Topping` is
replaced by `Poincare.D13.ToppingAdapter.Core`; every theorem statement is unchanged, every
proof body is the upstream proof body (with the two private helpers made public so they can be
axiom-audited).  Line references below are to the upstream file.

The upstream file proves, with complete proof bodies and no `sorry`/`admit`/`axiom`:

* `time_deriv_nonneg_of_isMaxOn_Icc` (Core.lean:28);
* `nonpos_of_forall_isMax_time_deriv_le_of_pos` (Core.lean:53) — the compact-space weak
  maximum principle (the *positive-time* form: the spatial-maximizer bound is only needed at
  strictly positive times, so no evolution equation is required at the initial endpoint);
* `nonpos_of_forall_isMax_time_deriv_le` (Core.lean:159) — the all-times interface;
* `exists_nonneg_reaction_bound_on_rectangle` (Core.lean:176);
* `exists_common_value_interval` (Core.lean:200);
* `le_ode_solution_of_forall_isMax_time_deriv_le_of_pos` / `_le` (Core.lean:240/292) —
  nonlinear ODE comparison;
* `nonneg_of_forall_isMin_time_deriv_ge` (Core.lean:314) — the minimum-principle dual.

Because the transcription is kernel-checked by the local build, every one of these is an
**upstream compiled theorem, locally re-verified** (semantic class recorded in the D13 result
card).  In addition this module proves one local variant

* `nonpos_of_forall_isMax_time_deriv_le_of_pos'` — the same positive-time weak maximum
  principle with the time-differentiability hypothesis `hderiv` required only at positive
  times (the upstream proof uses `hderiv` exactly once, at a maximizer time which the argument
  proves to be positive).  This is the expanded-hypothesis form needed by the slab heat
  interface (the local D2/D7 `ContinuousHeatHypotheses` provides the time derivative only in
  `Ioo 0 T`).

This file alone does **not** prove the local `ContinuousHeatMaximumPrincipleInterface`; the
geometric second-derivative input is supplied in `Slab.lean`.
-/

open Set Filter

namespace Poincare.D13.ToppingAdapter.Core

/-- Upstream Core.lean:18-26 (there `private`; made public here for the axiom audit). -/
theorem isLocalMaxOn_of_isMaxOn {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {s : Set X} {x : X} (h : IsMaxOn f s x) :
    IsLocalMaxOn f s x := by
  rw [IsLocalMaxOn, IsMaxFilter]
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h hy

/-- Upstream Core.lean:28-48 (`time_deriv_nonneg_of_isMaxOn_Icc`). -/
theorem time_deriv_nonneg_of_isMaxOn_Icc {f : ℝ → ℝ} {f' t T : ℝ}
    (ht : t ∈ Icc 0 T) (htpos : 0 < t)
    (hmax : IsMaxOn f (Icc 0 T) t)
    (hderiv : HasDerivWithinAt f f' (Icc 0 T) t) :
    0 ≤ f' := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcone : 0 - t ∈ posTangentConeAt (Icc 0 T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 T).segment_subset ht hzero)
  have hnonpos := (isLocalMaxOn_of_isMaxOn hmax).hasFDerivWithinAt_nonpos
    hderiv.hasFDerivWithinAt hcone
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hnonpos
  nlinarith

/-- Upstream Core.lean:53-157 (`nonpos_of_forall_isMax_time_deriv_le_of_pos`). -/
theorem nonpos_of_forall_isMax_time_deriv_le_of_pos
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w wt : X → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t → (∀ y, w y t ≤ w x t) →
      wt x t ≤ K * w x t)
    (hzero : ∀ x, w x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 := by
  classical
  intro x t ht
  by_contra hle
  have hwt : 0 < w x t := lt_of_not_ge hle
  have htne : t ≠ 0 := by
    intro heq
    subst t
    exact (not_lt_of_ge (hzero x)) hwt
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
  set ε : ℝ := Real.exp (-K * t) * w x t / (2 * t) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (mul_pos (Real.exp_pos _) hwt) (mul_pos (by norm_num) htpos)
  set V : X × ℝ → ℝ :=
    fun z => Real.exp (-K * z.2) * w z.1 z.2 - ε * z.2 with hV
  have hVcont : ContinuousOn V ((Set.univ : Set X) ×ˢ Icc 0 T) := by
    rw [hV]
    have hexp : Continuous fun z : X × ℝ => Real.exp (-K * z.2) := by
      fun_prop
    have hlin : Continuous fun z : X × ℝ => ε * z.2 := by
      fun_prop
    exact (hexp.continuousOn.mul hcont).sub hlin.continuousOn
  have hcompact : IsCompact ((Set.univ : Set X) ×ˢ Icc 0 T) :=
    isCompact_univ.prod isCompact_Icc
  have hne : ((Set.univ : Set X) ×ˢ Icc 0 T).Nonempty := by
    let x₀ := Classical.choice (inferInstance : Nonempty X)
    exact ⟨(x₀, 0), ⟨mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨z, hz, hzmax⟩ :=
    hcompact.exists_isMaxOn hne hVcont
  have hVxt : 0 < V (x, t) := by
    have heq : V (x, t) = Real.exp (-K * t) * w x t / 2 := by
      rw [hV, hε]
      field_simp [htne]
      ring
    rw [heq]
    positivity
  have hVzpos : 0 < V z :=
    lt_of_lt_of_le hVxt (hzmax ⟨mem_univ _, ht⟩)
  have hzt : z.2 ∈ Icc 0 T := hz.2
  have hztne : z.2 ≠ 0 := by
    intro heq
    have hzle : V z ≤ 0 := by
      simpa [hV, heq] using hzero z.1
    exact (not_lt_of_ge hzle) hVzpos
  have hztpos : 0 < z.2 := lt_of_le_of_ne hzt.1 (Ne.symm hztne)
  have hwzpos : 0 < w z.1 z.2 := by
    rw [hV] at hVzpos
    have hεtpos : 0 < ε * z.2 := mul_pos hεpos hztpos
    nlinarith [Real.exp_pos (-K * z.2)]
  have hwmax : ∀ y, w y z.2 ≤ w z.1 z.2 := by
    intro y
    have hleV := hzmax (show (y, z.2) ∈ (Set.univ : Set X) ×ˢ Icc 0 T from
      ⟨mem_univ _, hzt⟩)
    change V (y, z.2) ≤ V z at hleV
    rw [hV] at hleV
    nlinarith [Real.exp_pos (-K * z.2)]
  have hrate : wt z.1 z.2 ≤ K * w z.1 z.2 :=
    hmax z.2 hzt hztpos z.1 hwzpos hwmax
  set vtime : ℝ → ℝ :=
    (fun s => Real.exp (-K * s)) * w z.1 - fun s => ε * id s with hvtime
  have hvtime_eq (s : ℝ) : vtime s = V (z.1, s) := by
    rw [hvtime, hV]
    rfl
  have htimeMax : IsMaxOn vtime (Icc 0 T) z.2 := by
    intro s hs
    change vtime s ≤ vtime z.2
    rw [hvtime_eq s, hvtime_eq z.2]
    exact hzmax ⟨mem_univ _, hs⟩
  have hlin : HasDerivAt (fun s : ℝ => -K * s) (-K) z.2 := by
    simpa using (hasDerivAt_id z.2).const_mul (-K)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-K * s))
      (Real.exp (-K * z.2) * (-K)) z.2 := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-K * z.2)).comp z.2 hlin
  have hVderiv : HasDerivWithinAt vtime
      (Real.exp (-K * z.2) * (-K) * w z.1 z.2
        + Real.exp (-K * z.2) * wt z.1 z.2 - ε)
      (Icc 0 T) z.2 := by
    rw [hvtime]
    simpa only [mul_one] using
      (hexp.hasDerivWithinAt.mul (hderiv z.1 z.2 hzt)).sub
        ((hasDerivAt_id z.2).const_mul ε).hasDerivWithinAt
  have hdnonneg :
      0 ≤ Real.exp (-K * z.2) * (-K) * w z.1 z.2
        + Real.exp (-K * z.2) * wt z.1 z.2 - ε :=
    time_deriv_nonneg_of_isMaxOn_Icc hzt hztpos htimeMax hVderiv
  have hmul :
      Real.exp (-K * z.2) * wt z.1 z.2 ≤
        Real.exp (-K * z.2) * (K * w z.1 z.2) :=
    mul_le_mul_of_nonneg_left hrate (Real.exp_pos _).le
  nlinarith

/-- Upstream Core.lean:159-170 (`nonpos_of_forall_isMax_time_deriv_le`). -/
theorem nonpos_of_forall_isMax_time_deriv_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w wt : X → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x, 0 < w x t → (∀ y, w y t ≤ w x t) →
      wt x t ≤ K * w x t)
    (hzero : ∀ x, w x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 :=
  nonpos_of_forall_isMax_time_deriv_le_of_pos hT hcont hderiv
    (fun t ht _htpos => hmax t ht) hzero

/-- Upstream Core.lean:176-196 (`exists_nonneg_reaction_bound_on_rectangle`). -/
theorem exists_nonneg_reaction_bound_on_rectangle
    {F : ℝ → ℝ → ℝ} {a b T : ℝ}
    (hF : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => F z.1 z.2)
      (Icc a b ×ˢ Icc 0 T)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 T, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      y ≤ x → F x t - F y t ≤ K * (x - y) := by
  obtain ⟨K, hK⟩ := hF.exists_lipschitzOnWith (by norm_num)
    (Convex.prod (convex_Icc a b) (convex_Icc 0 T))
    (IsCompact.prod isCompact_Icc isCompact_Icc)
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro t ht x hx y hy hyx
  calc
    F x t - F y t ≤ dist (F x t) (F y t) := by
      rw [Real.dist_eq]
      exact le_abs_self _
    _ ≤ (K : ℝ) * dist (x, t) (y, t) :=
      hK.dist_le_mul (x, t) ⟨hx, ht⟩ (y, t) ⟨hy, ht⟩
    _ = (K : ℝ) * (x - y) := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
        max_eq_left (abs_nonneg _), abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- Upstream Core.lean:200-233 (`exists_common_value_interval`). -/
theorem exists_common_value_interval
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {u : X → ℝ → ℝ} {φ : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : ContinuousOn (fun z : X × ℝ => u z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hφ : ContinuousOn φ (Icc 0 T)) :
    ∃ a b : ℝ,
      (∀ x t, t ∈ Icc 0 T → u x t ∈ Icc a b) ∧
      ∀ t, t ∈ Icc 0 T → φ t ∈ Icc a b := by
  let s : Set ℝ :=
    (fun z : X × ℝ => u z.1 z.2) '' ((Set.univ : Set X) ×ˢ Icc 0 T) ∪
      φ '' Icc 0 T
  have hscompact : IsCompact s := by
    apply IsCompact.union
    · exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn hu
    · exact isCompact_Icc.image_of_continuousOn hφ
  have hsne : s.Nonempty := by
    refine ⟨φ 0, Or.inr ?_⟩
    exact ⟨0, ⟨le_rfl, hT⟩, rfl⟩
  obtain ⟨a, _ha, hamin⟩ :=
    hscompact.exists_isMinOn hsne continuous_id.continuousOn
  obtain ⟨b, _hb, hbmax⟩ :=
    hscompact.exists_isMaxOn hsne continuous_id.continuousOn
  refine ⟨a, b, ?_, ?_⟩
  · intro x t ht
    have hut : u x t ∈ s :=
      Or.inl ⟨(x, t), ⟨mem_univ _, ht⟩, rfl⟩
    exact ⟨hamin hut, hbmax hut⟩
  · intro t ht
    have hφt : φ t ∈ s := Or.inr ⟨t, ht, rfl⟩
    exact ⟨hamin hφt, hbmax hφt⟩

/-- Upstream Core.lean:240-291 (`le_ode_solution_of_forall_isMax_time_deriv_le_of_pos`). -/
theorem le_ode_solution_of_forall_isMax_time_deriv_le_of_pos
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {u ut : X → ℝ → ℝ} {φ φ' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => u z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, φ t < u x t →
      (∀ y, u y t ≤ u x t) → ut x t ≤ F (u x t) t)
    (hreaction : ∀ t ∈ Icc 0 T, ∀ x, φ t < u x t →
      F (u x t) t - F (φ t) t ≤ K * (u x t - φ t))
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t := by
  let w : X → ℝ → ℝ := fun x t => u x t - φ t
  let wt : X → ℝ → ℝ := fun x t => ut x t - φ' t
  have hφcont : ContinuousOn φ (Icc 0 T) :=
    fun t ht => (hφderiv t ht).continuousWithinAt
  have hw := nonpos_of_forall_isMax_time_deriv_le_of_pos
    (w := w) (wt := wt) (T := T) (K := K) hT
    (by
      change ContinuousOn (fun z : X × ℝ => u z.1 z.2 - φ z.2)
        ((Set.univ : Set X) ×ˢ Icc 0 T)
      exact hcont.sub (hφcont.comp continuous_snd.continuousOn
        (fun z hz => hz.2)))
    (fun x t ht => (huderiv x t ht).sub (hφderiv t ht))
    (fun t ht htpos x hxpos hxmax => by
      have hφu : φ t < u x t := by
        simpa [w] using hxpos
      have humax : ∀ y, u y t ≤ u x t := by
        intro y
        have hxy := hxmax y
        dsimp [w] at hxy
        linarith
      have hut := hmax t ht htpos x hφu humax
      have hr := hreaction t ht x hφu
      dsimp [wt, w]
      rw [hode t ht]
      linarith)
    (fun x => by
      dsimp [w]
      exact sub_nonpos.mpr (hzero x))
  intro x t ht
  have h := hw x t ht
  dsimp [w] at h
  exact sub_nonpos.mp h

/-- Upstream Core.lean:292-312 (`le_ode_solution_of_forall_isMax_time_deriv_le`). -/
theorem le_ode_solution_of_forall_isMax_time_deriv_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {u ut : X → ℝ → ℝ} {φ φ' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => u z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (huderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t)
    (hφderiv : ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt φ (φ' t) (Icc 0 T) t)
    (hode : ∀ t ∈ Icc 0 T, φ' t = F (φ t) t)
    (hmax : ∀ t ∈ Icc 0 T, ∀ x, φ t < u x t →
      (∀ y, u y t ≤ u x t) → ut x t ≤ F (u x t) t)
    (hreaction : ∀ t ∈ Icc 0 T, ∀ x, φ t < u x t →
      F (u x t) t - F (φ t) t ≤ K * (u x t - φ t))
    (hzero : ∀ x, u x 0 ≤ φ 0) :
    ∀ x t, t ∈ Icc 0 T → u x t ≤ φ t :=
  le_ode_solution_of_forall_isMax_time_deriv_le_of_pos hT hcont huderiv
    hφderiv hode (fun t ht _htpos => hmax t ht) hreaction hzero

/-- Upstream Core.lean:314-346 (`nonneg_of_forall_isMin_time_deriv_ge`). -/
theorem nonneg_of_forall_isMin_time_deriv_ge
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w wt : X → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hderiv : ∀ x t, t ∈ Icc 0 T →
      HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t)
    (hmin : ∀ t ∈ Icc 0 T, ∀ x, w x t < 0 → (∀ y, w x t ≤ w y t) →
      K * w x t ≤ wt x t)
    (hzero : ∀ x, 0 ≤ w x 0) :
    ∀ x t, t ∈ Icc 0 T → 0 ≤ w x t := by
  have hneg := nonpos_of_forall_isMax_time_deriv_le
    (w := fun x => -w x) (wt := fun x => -wt x) (K := K) hT
    hcont.neg
    (fun x t ht => (hderiv x t ht).neg)
    (fun t ht x hxpos hx => by
      have hxneg : w x t < 0 := by
        simpa only [Pi.neg_apply, neg_pos] using hxpos
      have hx' : ∀ y, w x t ≤ w y t := by
        intro y
        have hxy := hx y
        simp only [Pi.neg_apply] at hxy
        linarith
      simp only [Pi.neg_apply]
      nlinarith [hmin t ht x hxneg hx'])
    (fun x => by
      simp only [Pi.neg_apply]
      linarith [hzero x])
  intro x t ht
  have h := hneg x t ht
  simp only [Pi.neg_apply] at h
  linarith

/-! ## Local variant: time differentiability only at positive times -/

/-- **Local expanded-hypothesis variant** of the upstream positive-time weak maximum principle:
the time derivative `wt` is only required to be the within-derivative of `w x` at *positive*
times.  In the upstream proof the hypothesis `hderiv` is applied exactly once, at the maximizer
time `z.2`, and the argument establishes `0 < z.2` before that application; the proof below is
the upstream proof with `hztpos` threaded through.  This is the exact form needed by the slab
heat interface of `Poincare.Longrun.PDE.ContinuousInterface`, whose `heat_equation` field gives
`deriv (u x) t` only for `t ∈ Ioo 0 T` (never at `t = 0`). -/
theorem nonpos_of_forall_isMax_time_deriv_le_of_pos'
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w wt : X → ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hderiv : ∀ x t, t ∈ Icc 0 T → 0 < t →
      HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t)
    (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t → (∀ y, w y t ≤ w x t) →
      wt x t ≤ K * w x t)
    (hzero : ∀ x, w x 0 ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 := by
  classical
  intro x t ht
  by_contra hle
  have hwt : 0 < w x t := lt_of_not_ge hle
  have htne : t ≠ 0 := by
    intro heq
    subst t
    exact (not_lt_of_ge (hzero x)) hwt
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htne)
  set ε : ℝ := Real.exp (-K * t) * w x t / (2 * t) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos (mul_pos (Real.exp_pos _) hwt) (mul_pos (by norm_num) htpos)
  set V : X × ℝ → ℝ :=
    fun z => Real.exp (-K * z.2) * w z.1 z.2 - ε * z.2 with hV
  have hVcont : ContinuousOn V ((Set.univ : Set X) ×ˢ Icc 0 T) := by
    rw [hV]
    have hexp : Continuous fun z : X × ℝ => Real.exp (-K * z.2) := by
      fun_prop
    have hlin : Continuous fun z : X × ℝ => ε * z.2 := by
      fun_prop
    exact (hexp.continuousOn.mul hcont).sub hlin.continuousOn
  have hcompact : IsCompact ((Set.univ : Set X) ×ˢ Icc 0 T) :=
    isCompact_univ.prod isCompact_Icc
  have hne : ((Set.univ : Set X) ×ˢ Icc 0 T).Nonempty := by
    let x₀ := Classical.choice (inferInstance : Nonempty X)
    exact ⟨(x₀, 0), ⟨mem_univ _, le_rfl, hT⟩⟩
  obtain ⟨z, hz, hzmax⟩ :=
    hcompact.exists_isMaxOn hne hVcont
  have hVxt : 0 < V (x, t) := by
    have heq : V (x, t) = Real.exp (-K * t) * w x t / 2 := by
      rw [hV, hε]
      field_simp [htne]
      ring
    rw [heq]
    positivity
  have hVzpos : 0 < V z :=
    lt_of_lt_of_le hVxt (hzmax ⟨mem_univ _, ht⟩)
  have hzt : z.2 ∈ Icc 0 T := hz.2
  have hztne : z.2 ≠ 0 := by
    intro heq
    have hzle : V z ≤ 0 := by
      simpa [hV, heq] using hzero z.1
    exact (not_lt_of_ge hzle) hVzpos
  have hztpos : 0 < z.2 := lt_of_le_of_ne hzt.1 (Ne.symm hztne)
  have hwzpos : 0 < w z.1 z.2 := by
    rw [hV] at hVzpos
    have hεtpos : 0 < ε * z.2 := mul_pos hεpos hztpos
    nlinarith [Real.exp_pos (-K * z.2)]
  have hwmax : ∀ y, w y z.2 ≤ w z.1 z.2 := by
    intro y
    have hleV := hzmax (show (y, z.2) ∈ (Set.univ : Set X) ×ˢ Icc 0 T from
      ⟨mem_univ _, hzt⟩)
    change V (y, z.2) ≤ V z at hleV
    rw [hV] at hleV
    nlinarith [Real.exp_pos (-K * z.2)]
  have hrate : wt z.1 z.2 ≤ K * w z.1 z.2 :=
    hmax z.2 hzt hztpos z.1 hwzpos hwmax
  set vtime : ℝ → ℝ :=
    (fun s => Real.exp (-K * s)) * w z.1 - fun s => ε * id s with hvtime
  have hvtime_eq (s : ℝ) : vtime s = V (z.1, s) := by
    rw [hvtime, hV]
    rfl
  have htimeMax : IsMaxOn vtime (Icc 0 T) z.2 := by
    intro s hs
    change vtime s ≤ vtime z.2
    rw [hvtime_eq s, hvtime_eq z.2]
    exact hzmax ⟨mem_univ _, hs⟩
  have hlin : HasDerivAt (fun s : ℝ => -K * s) (-K) z.2 := by
    simpa using (hasDerivAt_id z.2).const_mul (-K)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-K * s))
      (Real.exp (-K * z.2) * (-K)) z.2 := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-K * z.2)).comp z.2 hlin
  have hVderiv : HasDerivWithinAt vtime
      (Real.exp (-K * z.2) * (-K) * w z.1 z.2
        + Real.exp (-K * z.2) * wt z.1 z.2 - ε)
      (Icc 0 T) z.2 := by
    rw [hvtime]
    simpa only [mul_one] using
      (hexp.hasDerivWithinAt.mul (hderiv z.1 z.2 hzt hztpos)).sub
        ((hasDerivAt_id z.2).const_mul ε).hasDerivWithinAt
  have hdnonneg :
      0 ≤ Real.exp (-K * z.2) * (-K) * w z.1 z.2
        + Real.exp (-K * z.2) * wt z.1 z.2 - ε :=
    time_deriv_nonneg_of_isMaxOn_Icc hzt hztpos htimeMax hVderiv
  have hmul :
      Real.exp (-K * z.2) * wt z.1 z.2 ≤
        Real.exp (-K * z.2) * (K * w z.1 z.2) :=
    mul_le_mul_of_nonneg_left hrate (Real.exp_pos _).le
  nlinarith

end Poincare.D13.ToppingAdapter.Core
