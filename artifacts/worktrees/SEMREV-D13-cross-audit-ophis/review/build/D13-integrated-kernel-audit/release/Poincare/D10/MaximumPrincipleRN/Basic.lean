/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10 builder

# D10 — Weak maximum principle for the heat equation on bounded domains of `ℝⁿ`

This file sets up the classical objects of the parabolic maximum principle on a bounded
spatial domain `Ω ⊆ ℝⁿ` (modelled as `Fin n → ℝ`, i.e. `ℝⁿ` in coordinates):

* the **parabolic cylinder** `Ω̄ × [0,T]`;
* the **parabolic boundary** `(Ω̄ × {0}) ∪ (∂Ω × (0,T])`, defined as the complement of the
  parabolic interior `Ω × (0,T]` inside the closed cylinder;
* **classical subsolutions** of the heat equation `u_t - Δu ≤ 0` on `Ω × (0,T]`.

The time derivative is only required from the left (`HasDerivWithinAt` on `[0,t]`), which is
exactly the one-sided condition used by the maximum principle; at interior times it is
implied by the usual two-sided condition (see `HeatSubsolutionData.of_twoSided`).
-/

import Mathlib

namespace Poincare.D10.MaximumPrincipleRN

open Set Filter Function
open scoped Topology

variable {n : ℕ}

/-- The **parabolic cylinder** `Ω̄ × [0,T]`. -/
def parabolicCylinder (Ω : Set (Fin n → ℝ)) (T : ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  closure Ω ×ˢ Icc 0 T

/-- The **parabolic boundary** of `Ω × (0,T]`: the part of the closed parabolic cylinder
`Ω̄ × [0,T]` that does not belong to the parabolic interior `Ω × (0,T]`.  Classically this is
`(Ω̄ × {0}) ∪ (∂Ω × (0,T])`. -/
def parabolicBoundary (Ω : Set (Fin n → ℝ)) (T : ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  parabolicCylinder Ω T \ (Ω ×ˢ Ioc 0 T)

theorem mem_parabolicCylinder {Ω : Set (Fin n → ℝ)} {T : ℝ} {p : (Fin n → ℝ) × ℝ} :
    p ∈ parabolicCylinder Ω T ↔ p.1 ∈ closure Ω ∧ p.2 ∈ Icc 0 T := Iff.rfl

theorem mem_parabolicBoundary {Ω : Set (Fin n → ℝ)} {T : ℝ} {p : (Fin n → ℝ) × ℝ} :
    p ∈ parabolicBoundary Ω T ↔
      p.1 ∈ closure Ω ∧ p.2 ∈ Icc 0 T ∧ ¬ (p.1 ∈ Ω ∧ p.2 ∈ Ioc 0 T) := by
  simp only [parabolicBoundary, Set.mem_sdiff, mem_parabolicCylinder, mem_prod]
  tauto

theorem parabolicBoundary_subset_cylinder {Ω : Set (Fin n → ℝ)} {T : ℝ} :
    parabolicBoundary Ω T ⊆ parabolicCylinder Ω T := sdiff_subset

/-- Classical description of the parabolic boundary: `(Ω̄ \ Ω) × [0,T] ∪ Ω̄ × {0}` for
`0 ≤ T`.  When `Ω` is open, `Ω̄ \ Ω` is the topological boundary `∂Ω`. -/
theorem parabolicBoundary_eq {Ω : Set (Fin n → ℝ)} {T : ℝ} (hT : 0 ≤ T) :
    parabolicBoundary Ω T = ((closure Ω \ Ω) ×ˢ Icc 0 T) ∪ (closure Ω ×ˢ ({0} : Set ℝ)) := by
  ext p
  rw [mem_parabolicBoundary, mem_union, mem_prod, mem_prod, Set.mem_sdiff]
  constructor
  · rintro ⟨hcl, ht, hnot⟩
    by_cases h0 : p.2 = 0
    · exact Or.inr ⟨hcl, h0⟩
    · refine Or.inl ⟨⟨hcl, fun hxΩ => hnot ⟨hxΩ, ?_⟩⟩, ht⟩
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
  · rintro (⟨⟨hcl, hnotΩ⟩, ht⟩ | ⟨hcl, h0⟩)
    · exact ⟨hcl, ht, fun h => hnotΩ h.1⟩
    · refine ⟨hcl, ⟨le_of_eq h0.symm, ?_⟩, fun h => ?_⟩
      · rwa [h0]
      · exact absurd h.2.1 (by rw [h0]; exact lt_irrefl 0)

/-- Data witnessing that `u` is a classical subsolution of the heat equation on `Ω × (0,T]`.

The fields `td`, `gx`, `gxx` are the (one-sided) time derivative and the first and second
spatial partial derivatives of `u`.  The time derivative is required only from the left
(the within-set is `[0,t]`): this is the form used by the maximum principle and is implied,
at interior times, by the usual two-sided condition. -/
structure HeatSubsolutionData (Ω : Set (Fin n → ℝ)) (T : ℝ)
    (u : (Fin n → ℝ) × ℝ → ℝ) where
  td : (Fin n → ℝ) → ℝ → ℝ
  gx : (Fin n → ℝ) → ℝ → Fin n → ℝ
  gxx : (Fin n → ℝ) → ℝ → Fin n → ℝ
  hasDeriv_time : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω,
    HasDerivWithinAt (fun s => u (x, s)) (td x t) (Icc 0 t) t
  hasDeriv_space : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
    HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i)
  hasDeriv_space2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
    HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i)
  le_operator : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, td x t - ∑ i, gxx x t i ≤ 0

/-- `u` is a classical subsolution `u_t - Δu ≤ 0` of the heat equation on `Ω × (0,T]`. -/
def IsHeatSubsolutionOn (Ω : Set (Fin n → ℝ)) (T : ℝ)
    (u : (Fin n → ℝ) × ℝ → ℝ) : Prop :=
  Nonempty (HeatSubsolutionData Ω T u)

namespace HeatSubsolutionData

variable {Ω : Set (Fin n → ℝ)} {T : ℝ} {u : (Fin n → ℝ) × ℝ → ℝ}

/-- **The `u - εt` trick.**  Subtracting `ε * t` from a subsolution yields again a
subsolution, and turns the differential inequality into the *strict* inequality
`(u - εt)_t - Δ(u - εt) ≤ -ε < 0`. -/
def subTime (D : HeatSubsolutionData Ω T u) (ε : ℝ) (hε : 0 ≤ ε) :
    HeatSubsolutionData Ω T (fun p => u p - ε * p.2) where
  td := fun x t => D.td x t - ε
  gx := D.gx
  gxx := D.gxx
  hasDeriv_time := by
    intro t ht x hx
    have h1 : HasDerivWithinAt (fun s : ℝ => u (x, s)) (D.td x t) (Icc 0 t) t :=
      D.hasDeriv_time t ht x hx
    have h2 : HasDerivWithinAt (fun s : ℝ => ε * s) ε (Icc 0 t) t := by
      simpa using (hasDerivWithinAt_id t (Icc 0 t)).const_mul ε
    exact h1.sub h2
  hasDeriv_space := by
    intro t ht x hx i
    have h1 : HasDerivAt (fun s : ℝ => u (Function.update x i s, t)) (D.gx x t i) (x i) :=
      D.hasDeriv_space t ht x hx i
    exact h1.sub_const (ε * t)
  hasDeriv_space2 := D.hasDeriv_space2
  le_operator := by
    intro t ht x hx
    have h := D.le_operator t ht x hx
    show (D.td x t - ε) - ∑ i, D.gxx x t i ≤ 0
    linarith

/-- The strict differential inequality satisfied by the perturbed subsolution `u - εt`. -/
theorem subTime_operator_le (D : HeatSubsolutionData Ω T u) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ)
    (ht : t ∈ Ioc 0 T)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    (D.subTime ε hε).td x t - ∑ i, (D.subTime ε hε).gxx x t i ≤ -ε := by
  have h := D.le_operator t ht x hx
  simp only [subTime]
  linarith

/-- Constructor from the **classical formulation** of a subsolution: the time derivative is a
genuine two-sided derivative on the parabolic interior `Ω × (0,T)` and a *left* derivative at
the terminal time `t = T`.  This is exactly the textbook notion of a classical subsolution
`u ∈ C^{2,1}(Ω × (0,T]) ∩ C⁰(Ω̄ × [0,T])`, and it produces the one-sided data used by the
maximum principle. -/
def of_classical (td : (Fin n → ℝ) → ℝ → ℝ) (gx : (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (gxx : (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (htime : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω, HasDerivAt (fun s => u (x, s)) (td x t) t)
    (htime_end : ∀ x ∈ Ω, HasDerivWithinAt (fun s => u (x, s)) (td x T) (Icc 0 T) T)
    (hspace : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i))
    (hspace2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i))
    (hle : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, td x t - ∑ i, gxx x t i ≤ 0) :
    HeatSubsolutionData Ω T u where
  td := td
  gx := gx
  gxx := gxx
  hasDeriv_time := by
    intro t ht x hx
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact (htime t ⟨ht.1, hlt⟩ x hx).hasDerivWithinAt
    · subst heq
      exact htime_end x hx
  hasDeriv_space := hspace
  hasDeriv_space2 := hspace2
  le_operator := hle

/-- Constructor from a **two-sided** formulation: the time derivative is a genuine two-sided
derivative at every `t ∈ (0,T]` (in particular at the terminal time `T`, which is stronger
than the classical notion requires). -/
def of_twoSided (td : (Fin n → ℝ) → ℝ → ℝ) (gx : (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (gxx : (Fin n → ℝ) → ℝ → Fin n → ℝ)
    (htime : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, HasDerivAt (fun s => u (x, s)) (td x t) t)
    (hspace : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i))
    (hspace2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i))
    (hle : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, td x t - ∑ i, gxx x t i ≤ 0) :
    HeatSubsolutionData Ω T u where
  td := td
  gx := gx
  gxx := gxx
  hasDeriv_time := fun t ht x hx => (htime t ht x hx).hasDerivWithinAt
  hasDeriv_space := hspace
  hasDeriv_space2 := hspace2
  le_operator := hle

end HeatSubsolutionData

theorem IsHeatSubsolutionOn.subTime {Ω : Set (Fin n → ℝ)} {T : ℝ}
    {u : (Fin n → ℝ) × ℝ → ℝ} (h : IsHeatSubsolutionOn Ω T u) (ε : ℝ) (hε : 0 ≤ ε) :
    IsHeatSubsolutionOn Ω T (fun p => u p - ε * p.2) := by
  obtain ⟨D⟩ := h
  exact ⟨D.subTime ε hε⟩

/-- The classical formulation of a subsolution (two-sided on the parabolic interior, left
derivative at the terminal time) implies the one-sided notion used by the maximum principle. -/
theorem IsHeatSubsolutionOn.of_classical {Ω : Set (Fin n → ℝ)} {T : ℝ}
    {u : (Fin n → ℝ) × ℝ → ℝ}
    {td : (Fin n → ℝ) → ℝ → ℝ} {gx : (Fin n → ℝ) → ℝ → Fin n → ℝ}
    {gxx : (Fin n → ℝ) → ℝ → Fin n → ℝ}
    (htime : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω, HasDerivAt (fun s => u (x, s)) (td x t) t)
    (htime_end : ∀ x ∈ Ω, HasDerivWithinAt (fun s => u (x, s)) (td x T) (Icc 0 T) T)
    (hspace : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i))
    (hspace2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i))
    (hle : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, td x t - ∑ i, gxx x t i ≤ 0) :
    IsHeatSubsolutionOn Ω T u :=
  ⟨HeatSubsolutionData.of_classical td gx gxx htime htime_end hspace hspace2 hle⟩

/-- The two-sided formulation of a subsolution implies the one-sided notion used by the
maximum principle. -/
theorem IsHeatSubsolutionOn.of_twoSided {Ω : Set (Fin n → ℝ)} {T : ℝ}
    {u : (Fin n → ℝ) × ℝ → ℝ}
    {td : (Fin n → ℝ) → ℝ → ℝ} {gx : (Fin n → ℝ) → ℝ → Fin n → ℝ}
    {gxx : (Fin n → ℝ) → ℝ → Fin n → ℝ}
    (htime : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, HasDerivAt (fun s => u (x, s)) (td x t) t)
    (hspace : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i))
    (hspace2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, ∀ i,
      HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i))
    (hle : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Ω, td x t - ∑ i, gxx x t i ≤ 0) :
    IsHeatSubsolutionOn Ω T u :=
  ⟨HeatSubsolutionData.of_twoSided td gx gxx htime hspace hspace2 hle⟩

/-- **Non-vacuity of the subsolution notion.**  Every constant function is a subsolution of the
heat equation on every domain (`u_t = 0`, `Δu = 0`). -/
theorem isHeatSubsolutionOn_const (Ω : Set (Fin n → ℝ)) (T c : ℝ) :
    IsHeatSubsolutionOn Ω T (fun _ : (Fin n → ℝ) × ℝ => c) := by
  refine ⟨HeatSubsolutionData.of_classical (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
    (fun t _ x _ => hasDerivAt_const t c)
    (fun x _ => (hasDerivAt_const T c).hasDerivWithinAt)
    (fun t _ x _ i => hasDerivAt_const (x i) c)
    (fun t _ x _ i => hasDerivAt_const (x i) 0) ?_⟩
  intro t _ x _
  simp

end Poincare.D10.MaximumPrincipleRN
