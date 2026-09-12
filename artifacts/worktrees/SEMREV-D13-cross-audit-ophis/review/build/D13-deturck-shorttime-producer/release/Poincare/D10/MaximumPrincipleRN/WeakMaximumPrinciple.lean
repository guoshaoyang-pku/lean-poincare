/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10 builder

# D10 — Weak maximum principle for the heat equation on bounded domains of `ℝⁿ`

Main result: a classical subsolution `u` of the heat equation `u_t - Δu ≤ 0` on `Ω × (0,T]`,
continuous on the closed parabolic cylinder `Ω̄ × [0,T]` over a bounded open domain
`Ω ⊆ ℝⁿ`, is bounded on the whole cylinder by its maximum on the parabolic boundary
`(Ω̄ × {0}) ∪ (∂Ω × (0,T])`.

The proof is the classical `u - εt` trick:

* `weak_maximum_principle_strict` is the core step, for a subsolution satisfying the *strict*
  inequality `u_t - Δu ≤ -ε` with `ε > 0`.  If `u` exceeded its boundary bound at some interior
  point, the (continuous) function `u` would attain its maximum over the compact cylinder at a
  point `(x₀,t₀)` with `x₀ ∈ Ω` and `t₀ ∈ (0,T]`; at such a point the time derivative is
  `≥ 0` (`hasDerivWithinAt_nonneg_of_isMaxOn_Icc`), each second spatial derivative is `≤ 0`
  (`deriv_deriv_nonpos_of_isLocalMax`), and the resulting inequality
  `0 ≤ u_t - Δu ≤ -ε < 0` is a contradiction.
* `weak_maximum_principle` reduces the general subsolution to the strict one by replacing `u`
  with `u - εt` (this makes the differential inequality strict by `ε`, while changing the
  boundary values only downwards since `t ≥ 0` on the cylinder) and letting `ε → 0`.
-/

import Poincare.D10.MaximumPrincipleRN.SecondDerivativeTest

namespace Poincare.D10.MaximumPrincipleRN

open Set Filter Function
open scoped Topology

variable {n : ℕ}

/-- The coordinate line `s ↦ Function.update x i s` is continuous, for `ℝⁿ` with the product
topology. -/
theorem continuous_update_coord (x : Fin n → ℝ) (i : Fin n) :
    Continuous fun s : ℝ => Function.update x i s := by
  refine continuous_pi fun j => ?_
  by_cases hji : j = i
  · rw [← hji]
    have h : (fun s : ℝ => Function.update x j s j) = fun s : ℝ => s := by
      funext s
      rw [Function.update_self]
    rw [h]
    exact continuous_id
  · have h : (fun s : ℝ => Function.update x i s j) = fun _ => x j := by
      funext s
      simp [hji]
    rw [h]
    exact continuous_const

/-- **Core strict form of the weak maximum principle.**
Let `D` be subsolution data for `u` satisfying the *strict* differential inequality
`u_t - Δu ≤ -ε` with `ε > 0` on `Ω × (0,T]`.  If `u ≤ M` on the parabolic boundary then
`u ≤ M` on the whole parabolic cylinder. -/
theorem weak_maximum_principle_strict
    {Ω : Set (Fin n → ℝ)} {T M ε : ℝ} {u : (Fin n → ℝ) × ℝ → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hε : 0 < ε)
    (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (D : HeatSubsolutionData Ω T u)
    (hstrict : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ω, D.td x t - ∑ i, D.gxx x t i ≤ -ε)
    (hbd : ∀ q ∈ parabolicBoundary Ω T, u q ≤ M) :
    ∀ p ∈ parabolicCylinder Ω T, u p ≤ M := by
  intro p hp
  by_contra hle
  rw [not_le] at hle
  have hcyl_compact : IsCompact (parabolicCylinder Ω T) :=
    hΩ_bdd.isCompact_closure.prod isCompact_Icc
  have hcyl_ne : (parabolicCylinder Ω T).Nonempty :=
    ⟨(hΩ_ne.some, 0), subset_closure hΩ_ne.some_mem, le_rfl, hT.le⟩
  obtain ⟨q₀, hq₀, hmax₀⟩ := hcyl_compact.exists_isMaxOn hcyl_ne hu_cont
  have hmax₀_apply : ∀ r ∈ parabolicCylinder Ω T, u r ≤ u q₀ := fun r hr => hmax₀ hr
  have hq₀_gt : M < u q₀ := lt_of_lt_of_le hle (hmax₀_apply p hp)
  have hq₀_notbd : q₀ ∉ parabolicBoundary Ω T := fun hmem => absurd (hbd q₀ hmem) (not_le.mpr hq₀_gt)
  have hq₀_int : q₀.1 ∈ Ω ∧ q₀.2 ∈ Ioc 0 T := by
    by_contra h
    exact hq₀_notbd (by
      rw [parabolicBoundary]
      exact ⟨hq₀, by simpa [Set.mem_prod] using h⟩)
  obtain ⟨hx₀Ω, ht₀⟩ : q₀.1 ∈ Ω ∧ q₀.2 ∈ Ioc 0 T := hq₀_int
  have hmax₀' : ∀ r ∈ parabolicCylinder Ω T, u r ≤ u (q₀.1, q₀.2) := hmax₀
  -- time direction: the left derivative at the maximum is nonnegative
  have htime_nonneg : 0 ≤ D.td q₀.1 q₀.2 :=
    hasDerivWithinAt_nonneg_of_isMaxOn_Icc ht₀.1
      (fun s hs => hmax₀' (q₀.1, s) ⟨subset_closure hx₀Ω, hs.1, le_trans hs.2 ht₀.2⟩)
      (D.hasDeriv_time q₀.2 ht₀ q₀.1 hx₀Ω)
  -- space directions: the second derivatives at the maximum are nonpositive
  have hcoord_mem (i : Fin n) : ∀ᶠ s in 𝓝 (q₀.1 i), Function.update q₀.1 i s ∈ Ω :=
    (continuous_update_coord q₀.1 i).continuousAt.preimage_mem_nhds
      (show Ω ∈ 𝓝 (Function.update q₀.1 i (q₀.1 i)) by
        rw [Function.update_eq_self]
        exact hΩ_open.mem_nhds hx₀Ω)
  have hcoord_max (i : Fin n) :
      IsLocalMax (fun s : ℝ => u (Function.update q₀.1 i s, q₀.2)) (q₀.1 i) := by
    rw [IsLocalMax, IsMaxFilter]
    filter_upwards [hcoord_mem i] with s hs
    have hmem : (Function.update q₀.1 i s, q₀.2) ∈ parabolicCylinder Ω T :=
      ⟨subset_closure hs, ht₀.1.le, ht₀.2⟩
    have := hmax₀' (Function.update q₀.1 i s, q₀.2) hmem
    simpa [Function.update_eq_self] using this
  have hcoord_diff (i : Fin n) : ∀ᶠ s in 𝓝 (q₀.1 i),
      DifferentiableAt ℝ (fun r : ℝ => u (Function.update q₀.1 i r, q₀.2)) s := by
    filter_upwards [hcoord_mem i] with s hs
    have h := D.hasDeriv_space q₀.2 ht₀ (Function.update q₀.1 i s) hs i
    simpa [Function.update_idem, Function.update_self] using h.differentiableAt
  have hcoord_deriv (i : Fin n) : HasDerivAt
      (deriv (fun r : ℝ => u (Function.update q₀.1 i r, q₀.2))) (D.gxx q₀.1 q₀.2 i) (q₀.1 i) := by
    refine (D.hasDeriv_space2 q₀.2 ht₀ q₀.1 hx₀Ω i).congr_of_eventuallyEq ?_
    filter_upwards [hcoord_mem i] with s hs
    have h := D.hasDeriv_space q₀.2 ht₀ (Function.update q₀.1 i s) hs i
    simpa [Function.update_idem, Function.update_self] using h.deriv
  have hspace2_nonpos (i : Fin n) : D.gxx q₀.1 q₀.2 i ≤ 0 :=
    deriv_deriv_nonpos_of_isLocalMax (hcoord_max i) (hcoord_diff i) (hcoord_deriv i)
  have hsum_nonpos : ∑ i : Fin n, D.gxx q₀.1 q₀.2 i ≤ 0 :=
    Finset.sum_nonpos fun i _ => hspace2_nonpos i
  have hnonneg : 0 ≤ D.td q₀.1 q₀.2 - ∑ i, D.gxx q₀.1 q₀.2 i := by linarith
  have hlt : D.td q₀.1 q₀.2 - ∑ i, D.gxx q₀.1 q₀.2 i < 0 := by
    have := hstrict q₀.2 ht₀ q₀.1 hx₀Ω
    linarith
  exact absurd hnonneg (not_le.mpr hlt)

/-- **Weak maximum principle for the heat equation on a bounded domain.**
Let `Ω ⊆ ℝⁿ` be open, bounded and nonempty, let `T > 0`, and let `u` be continuous on the
closed parabolic cylinder `Ω̄ × [0,T]` and a classical subsolution of the heat equation
`u_t - Δu ≤ 0` on `Ω × (0,T]`.  If `u ≤ M` on the parabolic boundary
`(Ω̄ × {0}) ∪ (∂Ω × (0,T])`, then `u ≤ M` on the whole cylinder. -/
theorem weak_maximum_principle
    {Ω : Set (Fin n → ℝ)} {T M : ℝ} {u : (Fin n → ℝ) × ℝ → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (hu_sub : IsHeatSubsolutionOn Ω T u)
    (hbd : ∀ q ∈ parabolicBoundary Ω T, u q ≤ M) :
    ∀ p ∈ parabolicCylinder Ω T, u p ≤ M := by
  obtain ⟨D⟩ := hu_sub
  intro p hp
  by_contra hle
  rw [not_le] at hle
  set ε : ℝ := (u p - M) / (2 * T) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- the perturbed function `u - εt` still has a value `> M` at `p`
  have hεbound : ε * p.2 < u p - M := by
    have h1 : ε * p.2 ≤ ε * T :=
      mul_le_mul_of_nonneg_left (mem_parabolicCylinder.mp hp).2.2 hεpos.le
    have h2 : ε * T = (u p - M) / 2 := by
      rw [hεdef]; field_simp
    linarith
  have hp_pert : M < u p - ε * p.2 := by linarith
  -- the perturbed subsolution and its continuity
  have hcont_pert : ContinuousOn (fun r : (Fin n → ℝ) × ℝ => u r - ε * r.2)
      (parabolicCylinder Ω T) := by
    have h1 : Continuous fun r : (Fin n → ℝ) × ℝ => ε * r.2 := continuous_snd.const_mul ε
    exact hu_cont.sub h1.continuousOn
  -- the perturbed function still satisfies the boundary bound
  have hbd_pert : ∀ q ∈ parabolicBoundary Ω T, u q - ε * q.2 ≤ M := by
    intro q hq
    have hq_cyl := parabolicBoundary_subset_cylinder hq
    have ht : 0 ≤ q.2 := (mem_parabolicCylinder.mp hq_cyl).2.1
    have h1 : 0 ≤ ε * q.2 := mul_nonneg hεpos.le ht
    have h2 : u q ≤ M := hbd q hq
    linarith
  exact absurd (weak_maximum_principle_strict hΩ_open hΩ_bdd hΩ_ne hT hεpos hcont_pert
    (D.subTime ε hεpos.le)
    (fun t ht x hx => D.subTime_operator_le ε hεpos.le t ht x hx)
    hbd_pert p hp) (not_le.mpr hp_pert)

/-- **Maximum principle, supremum form.**  A subsolution is bounded on the closed parabolic
cylinder by the supremum of its values on the parabolic boundary. -/
theorem weak_maximum_principle_sSup
    {Ω : Set (Fin n → ℝ)} {T : ℝ} {u : (Fin n → ℝ) × ℝ → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (hu_sub : IsHeatSubsolutionOn Ω T u) :
    ∀ p ∈ parabolicCylinder Ω T, u p ≤ sSup (u '' parabolicBoundary Ω T) := by
  have hK : IsCompact (parabolicCylinder Ω T) :=
    hΩ_bdd.isCompact_closure.prod isCompact_Icc
  have hbdd : BddAbove (u '' parabolicBoundary Ω T) :=
    (hK.bddAbove_image hu_cont).mono (image_mono parabolicBoundary_subset_cylinder)
  exact weak_maximum_principle hΩ_open hΩ_bdd hΩ_ne hT hu_cont hu_sub
    fun q hq => le_csSup hbdd ⟨q, hq, rfl⟩

/-- **Maximum principle, attained form.**  A subsolution attains its maximum on the whole
closed parabolic cylinder at a point of the parabolic boundary. -/
theorem exists_max_on_parabolicBoundary
    {Ω : Set (Fin n → ℝ)} {T : ℝ} {u : (Fin n → ℝ) × ℝ → ℝ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (hu_sub : IsHeatSubsolutionOn Ω T u) :
    ∃ q ∈ parabolicBoundary Ω T, ∀ p ∈ parabolicCylinder Ω T, u p ≤ u q := by
  have hK : IsCompact (parabolicCylinder Ω T) :=
    hΩ_bdd.isCompact_closure.prod isCompact_Icc
  have hbd_ne : (parabolicBoundary Ω T).Nonempty :=
    ⟨(hΩ_ne.some, 0), by
      rw [parabolicBoundary]
      refine ⟨⟨subset_closure hΩ_ne.some_mem, le_rfl, hT.le⟩, ?_⟩
      simp⟩
  have hclosed : IsClosed (parabolicBoundary Ω T) := by
    rw [parabolicBoundary_eq hT.le]
    exact IsClosed.union (isClosed_closure.sdiff hΩ_open |>.prod isClosed_Icc)
      (isClosed_closure.prod isClosed_singleton)
  have hKbd : IsCompact (parabolicBoundary Ω T) :=
    hK.of_isClosed_subset hclosed parabolicBoundary_subset_cylinder
  obtain ⟨q, hq, hmax⟩ :=
    hKbd.exists_isMaxOn hbd_ne (hu_cont.mono parabolicBoundary_subset_cylinder)
  exact ⟨q, hq, fun p hp =>
    weak_maximum_principle hΩ_open hΩ_bdd hΩ_ne hT hu_cont hu_sub
      (fun r hr => hmax hr) p hp⟩

/-- End-to-end smoke test of the maximum principle on the non-vacuous example of a constant
subsolution: `u ≡ c` on the cylinder is bounded by any `M ≥ c`. -/
theorem weak_maximum_principle_const
    {Ω : Set (Fin n → ℝ)} {T M c : ℝ}
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hcM : c ≤ M) :
    ∀ p ∈ parabolicCylinder Ω T, (fun _ : (Fin n → ℝ) × ℝ => c) p ≤ M :=
  weak_maximum_principle hΩ_open hΩ_bdd hΩ_ne hT continuousOn_const
    (isHeatSubsolutionOn_const Ω T c) (fun _ _ => hcM)

end Poincare.D10.MaximumPrincipleRN
