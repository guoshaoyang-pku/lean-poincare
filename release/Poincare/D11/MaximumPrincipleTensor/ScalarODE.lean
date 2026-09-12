/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11 builder

# D11 — The scalar (1 × 1) case: forward invariance of the nonnegative half-line

The tensor maximum principle in dimension `1` is the statement that the scalar reaction ODE
`y' = q(y)` preserves nonnegativity.  This file proves it under the correct hypothesis
(`scalar_forward_invariance`), exhibits its relation to the unconditional D10 scalar
comparison principle (`scalar_forward_invariance_of_global_reaction`), and shows that the
naive one-sided hypothesis is **false** (`scalar_invariance_oneSided_false`).

## The hypothesis is two-sided

It is tempting to assume only `q(v) ≥ 0` for `v ≥ 0` ("the vector field points into the
half-line at the boundary").  This is *not* enough: the counterexample

`y(t) = -t²`,  `q(v) = -2 √(-v)` for `v < 0` and `q(v) = 0` for `v ≥ 0`

satisfies `q ≥ 0` on `[0,∞)`, `q(0) = 0`, `y(0) = 0 ≥ 0` and `y' = q ∘ y` on `[0,1]`, yet
`y(1) = -1 < 0`.  What *is* sufficient (and is what the maximum-principle argument really
uses) is positivity of `q` on a two-sided neighbourhood `(-δ, ∞)` of the boundary point:
at the first time the solution reaches `-δ/2`, the comparison argument produces a
contradiction.

The proof of `scalar_forward_invariance` follows the classical strategy.  Let
`A = {t ∈ [0,T] | ∀ s ∈ [0,t], -δ < y s}` and `t₀ = sSup A`.  On `[0,t₀]` the reaction is
nonnegative (`-δ < y`), so `y` is monotone nondecreasing there and `y t₀ ≥ y 0 ≥ 0`.  If
`t₀ < T`, continuity then extends `A` strictly past `t₀`, contradicting the definition of
`t₀`.
-/

import Poincare.D11.MaximumPrincipleTensor.Basic
import Poincare.D10.MaximumPrincipleRN.Semidiscrete

open scoped MatrixOrder Topology
open Matrix Set

namespace Poincare.D11.MaximumPrincipleTensor

/-! ## The scalar forward-invariance theorem -/

/-- **Scalar forward invariance of `[0,∞)`.**  Let `q` be nonnegative on a two-sided
neighbourhood `(-δ, ∞)` of the origin (`δ > 0`).  If `y` is differentiable on `[0,T]` with
`y' = q ∘ y` and `y 0 ≥ 0`, then `y ≥ 0` on `[0,T]`. -/
theorem scalar_forward_invariance {q y : ℝ → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (q (y t)) t)
    (hq : ∀ v, -δ < v → 0 ≤ q v) (hy0 : 0 ≤ y 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ y t := by
  have hycont : ContinuousOn y (Icc 0 T) := fun t ht => (hy t ht).continuousAt.continuousWithinAt
  -- the set of times up to which the trajectory has stayed above `-δ`
  set A : Set ℝ := {t | t ∈ Icc 0 T ∧ ∀ s ∈ Icc 0 t, -δ < y s} with hA
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, hT⟩, ?_⟩
    intro s hs
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    rw [hs0]
    linarith
  have hAne : A.Nonempty := ⟨0, h0A⟩
  have hAbdd : BddAbove A := ⟨T, fun t ht => ht.1.2⟩
  set t₀ : ℝ := sSup A with ht₀
  have ht₀_ge : 0 ≤ t₀ := le_csSup hAbdd h0A
  have ht₀_le : t₀ ≤ T := csSup_le hAne fun t ht => ht.1.2
  -- every `t < t₀` lies in `A`
  have hmemA : ∀ t, t < t₀ → t ∈ Icc 0 T → t ∈ A := by
    intro t ht htIT
    obtain ⟨u, huA, htu⟩ := exists_lt_of_lt_csSup hAne ht
    refine ⟨htIT, fun s hs => ?_⟩
    exact huA.2 s ⟨hs.1, le_trans hs.2 htu.le⟩
  -- `y` is nondecreasing on `[0,t₀]`, hence nonnegative there
  have hmono₀ : MonotoneOn y (Icc 0 t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t₀) ?_ ?_ ?_
    · exact hycont.mono (fun t ht => ⟨ht.1, le_trans ht.2 ht₀_le⟩)
    · intro t ht
      exact ((hy t ⟨(interior_subset ht).1, le_trans (interior_subset ht).2 ht₀_le⟩).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htIT : t ∈ Icc 0 T := ⟨ht.1.le, le_trans ht.2.le ht₀_le⟩
      have htA : t ∈ A := hmemA t ht.2 htIT
      rw [(hy t htIT).deriv]
      exact hq (y t) (htA.2 t ⟨ht.1.le, le_rfl⟩)
  have hy₀_nonneg : ∀ t ∈ Icc 0 t₀, 0 ≤ y t := fun t ht =>
    le_trans hy0 (hmono₀ ⟨le_rfl, ht₀_ge⟩ ht ht.1)
  have ht₀_nonneg : 0 ≤ y t₀ := hy₀_nonneg t₀ ⟨ht₀_ge, le_rfl⟩
  -- `t₀` is exactly `T`: otherwise continuity extends `A` beyond `t₀`
  have ht₀_eq : t₀ = T := by
    by_contra hne
    have ht₀_lt : t₀ < T := lt_of_le_of_ne ht₀_le hne
    have hcont : ContinuousWithinAt y (Icc 0 T) t₀ := hycont t₀ ⟨ht₀_ge, ht₀_le⟩
    rw [Metric.continuousWithinAt_iff] at hcont
    obtain ⟨η, hη, hηprop⟩ := hcont (δ / 2) (by linarith)
    set t₁ : ℝ := min (t₀ + η / 2) T with ht₁
    have ht₀_lt_t₁ : t₀ < t₁ := lt_min (by linarith) ht₀_lt
    have ht₁_le : t₁ ≤ T := min_le_right _ _
    have ht₁_mem : t₁ ∈ A := by
      refine ⟨⟨ht₀_ge.trans ht₀_lt_t₁.le, ht₁_le⟩, fun s hs => ?_⟩
      rcases le_or_gt s t₀ with hsle | hslt
      · exact lt_of_lt_of_le (by linarith [hδ]) (hy₀_nonneg s ⟨hs.1, hsle⟩)
      · have hsT : s ∈ Icc 0 T := ⟨hs.1, le_trans hs.2 ht₁_le⟩
        have hdist : dist s t₀ < η := by
          have h1 : s ≤ t₀ + η / 2 := le_trans hs.2 (min_le_left _ _)
          rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ s - t₀)]
          linarith
        have h2 := hηprop hsT hdist
        rw [Real.dist_eq] at h2
        have h3 := (abs_lt.mp h2).1
        linarith [ht₀_nonneg, hδ]
    have : t₁ ≤ t₀ := le_csSup hAbdd ht₁_mem
    exact absurd this (not_le.mpr ht₀_lt_t₁)
  -- conclude on `[0,T]`
  have hmono : MonotoneOn y (Icc 0 T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hycont ?_ ?_
    · intro t ht
      exact ((hy t (interior_subset ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htIT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
      have htlt : t < t₀ := by rw [ht₀_eq]; exact ht.2
      have htA : t ∈ A := hmemA t htlt htIT
      rw [(hy t htIT).deriv]
      exact hq (y t) (htA.2 t ⟨ht.1.le, le_rfl⟩)
  intro t ht
  exact le_trans hy0 (hmono ⟨le_rfl, hT⟩ ht ht.1)

/-- **Bridge to the D10 scalar comparison principle.**  If the reaction is nonnegative *along
the whole trajectory* (so the differential inequality `(-y)' ≤ 0` holds everywhere on
`[0,T]`), the unconditional D10 comparison principle
(`Poincare.D10.MaximumPrincipleRN.scalar_ode_comparison`) applies directly. -/
theorem scalar_forward_invariance_of_global_reaction {q y : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (q (y t)) t)
    (hq : ∀ t ∈ Icc 0 T, 0 ≤ q (y t)) (hy0 : 0 ≤ y 0) :
    ∀ t ∈ Icc 0 T, 0 ≤ y t := by
  have h := Poincare.D10.MaximumPrincipleRN.scalar_ode_comparison
    (φ := fun t => -y t) (φ' := fun t => -(q (y t))) hT
    (fun t ht => (hy t ht).neg) (by linarith)
    (fun t ht => by linarith [hq t ht])
  intro t ht
  have := h t ht
  linarith

/-- **Non-vacuity of the scalar theorem.**  The function `y t = 2 exp t - 2` solves
`y' = q ∘ y` for the reaction `q v = v + 2`, which is nonnegative on `(-2, ∞)`; moreover
`y 0 = 0 ≥ 0`, so `scalar_forward_invariance` applies and re-derives the (true) nonnegativity
`0 ≤ 2 exp t - 2` on `[0,T]`. -/
theorem exp_shift_forward_invariance {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, 0 ≤ 2 * Real.exp t - 2 :=
  scalar_forward_invariance (q := fun v => v + 2) (y := fun t => 2 * Real.exp t - 2)
    (δ := 2) (by norm_num) hT
    (fun t _ => by
      have h : HasDerivAt (fun t : ℝ => 2 * Real.exp t) (2 * Real.exp t) t :=
        (Real.hasDerivAt_exp t).const_mul 2
      have h2 : HasDerivAt (fun t : ℝ => 2 * Real.exp t - 2) (2 * Real.exp t) t := by
        simpa using h.sub_const 2
      convert h2 using 1
      ring)
    (fun v hv => by linarith) (by simp)

/-! ## The `1 × 1` tensor case -/

/-- The `1 × 1` matrix with entry `a`. -/
def oneByOne (a : ℝ) : Mat 1 := fun _ _ => a

theorem oneByOne_apply (a : ℝ) (i j : Fin 1) : oneByOne a i j = a := rfl

theorem oneByOne_injective : Function.Injective oneByOne := by
  intro a b h
  have := congrFun (congrFun h 0) 0
  simpa [oneByOne] using this

theorem oneByOne_eq_zero_iff {a : ℝ} : oneByOne a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [oneByOne] using this
  · rintro rfl
    ext i j
    simp [oneByOne]

/-- `1 × 1` positive semidefiniteness is nonnegativity of the entry. -/
theorem oneByOne_posSemidef_iff {a : ℝ} : (oneByOne a).PosSemidef ↔ 0 ≤ a := by
  constructor
  · intro h
    simpa [oneByOne] using h.diag_nonneg (i := 0)
  · intro h
    have hdiag : (Matrix.diagonal (fun _ : Fin 1 => a)).PosSemidef :=
      Matrix.PosSemidef.diagonal fun _ => h
    convert hdiag using 1
    ext i j
    fin_cases i
    fin_cases j
    simp [oneByOne, Matrix.diagonal]

theorem psdCone_oneByOne_iff {a : ℝ} : oneByOne a ∈ psdCone 1 ↔ 0 ≤ a :=
  oneByOne_posSemidef_iff

/-- **The `1 × 1` case of the tensor maximum principle.**  A `1 × 1` tensor whose scalar
component satisfies a scalar reaction ODE with reaction nonnegative on `(-δ, ∞)` stays
positive semidefinite. -/
theorem oneByOne_forward_invariance {q y : ℝ → ℝ} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (q (y t)) t)
    (hq : ∀ v, -δ < v → 0 ≤ q v) (hy0 : 0 ≤ y 0) :
    ∀ t ∈ Icc 0 T, (oneByOne (y t)).PosSemidef := fun t ht =>
  oneByOne_posSemidef_iff.mpr (scalar_forward_invariance hδ hT hy hq hy0 t ht)

/-! ## The one-sided hypothesis is not sufficient

The naive statement with `q ≥ 0` only on `[0,∞)` is false.  We formalise the counterexample
`y(t) = -t²` with `q(v) = -2√(-v)` for `v < 0` and `q(v) = 0` for `v ≥ 0`. -/

/-- The reaction of the counterexample: `q(v) = -2√(-v)` for `v < 0`, `q(v) = 0` for
`v ≥ 0`. -/
noncomputable def sqrtNegReaction (v : ℝ) : ℝ := if 0 ≤ v then 0 else -2 * Real.sqrt (-v)

/-- The trajectory of the counterexample: `y(t) = -t²`. -/
def negSquare (t : ℝ) : ℝ := -(t ^ 2)

theorem sqrtNegReaction_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ sqrtNegReaction v := by
  simp [sqrtNegReaction, hv]

theorem sqrtNegReaction_negSquare {t : ℝ} (ht : 0 ≤ t) :
    sqrtNegReaction (negSquare t) = -(2 * t) := by
  by_cases h0 : t = 0
  · subst h0
    simp [sqrtNegReaction, negSquare]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
    have hneg : ¬ 0 ≤ negSquare t := by
      simp only [negSquare, neg_nonneg]
      exact not_le.mpr (pow_pos htpos 2)
    have hsqrt : Real.sqrt (-(negSquare t)) = t := by
      rw [show -(negSquare t) = t ^ 2 by rw [negSquare]; ring, Real.sqrt_sq ht]
    simp [sqrtNegReaction, hneg, hsqrt]

theorem hasDerivAt_negSquare (t : ℝ) : HasDerivAt negSquare (-(2 * t)) t := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  exact h.neg

/-- **The naive one-sided hypothesis is false.**  There is a reaction `q` that is nonnegative
on `[0,∞)` and a differentiable `y` on `[0,1]` with `y' = q ∘ y`, `y 0 = 0 ≥ 0`, but
`y 1 < 0`.  Hence the two-sided neighbourhood hypothesis of `scalar_forward_invariance` is
the right one. -/
theorem scalar_invariance_oneSided_false :
    ¬ (∀ (q y : ℝ → ℝ) (T : ℝ), 0 < T →
        (∀ t ∈ Icc 0 T, HasDerivAt y (q (y t)) t) →
        (∀ v, 0 ≤ v → 0 ≤ q v) → 0 ≤ y 0 → ∀ t ∈ Icc 0 T, 0 ≤ y t) := by
  intro h
  have hODE : ∀ t ∈ Icc 0 (1 : ℝ), HasDerivAt negSquare (sqrtNegReaction (negSquare t)) t := by
    intro t ht
    rw [sqrtNegReaction_negSquare ht.1]
    exact hasDerivAt_negSquare t
  have hbad := h sqrtNegReaction negSquare 1 (by norm_num) hODE
    (fun v hv => sqrtNegReaction_nonneg hv) (by simp [negSquare]) 1 ⟨by norm_num, by norm_num⟩
  norm_num [negSquare] at hbad

end Poincare.D11.MaximumPrincipleTensor
