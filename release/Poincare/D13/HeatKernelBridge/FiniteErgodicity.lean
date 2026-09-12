/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteUniqueness

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.FiniteErgodicity

**D13 heat-kernel bridge, companion note 7: the Dirichlet gap and the long-time asymptotics of the
pinned finite heat kernel.**

`FiniteSpaceHeat.lean` constructs the matrix-exponential kernel of a pinned finite Laplace operator
`G` and proves its structural laws; `FiniteUniqueness.lean` proves the energy method: the `ℓ²`
energy of any solution of `∂_t u = Δ u` is antitone because the pinned quadratic form
`∑ x, u x * Δ u x` is nonpositive. Antitonicity alone gives no *rate* and no statement about the
limit at infinity. This file supplies both, and in doing so formalizes the finite-dimensional
counterpart of the two spectral facts on which the manifold heat-kernel long-time theory rests: a
Poincaré (spectral-gap) inequality and the convergence of the kernel to the equilibrium measure.

* **The Dirichlet form and its positivity.** The Dirichlet form
  `dirichletForm G u = (1/2) * ∑ x ∑ y, L x y * (u x - u y)^2` is the negative of the quadratic form
  (`dirichletForm_eq_neg_quadraticForm`) and is nonnegative. It vanishes exactly on the constants
  (`dirichletForm_eq_zero_iff`), because the pinned operator has strictly positive off-diagonal
  entries.
* **The Poincaré inequality with an explicit constant.** Because the pinned operator is a *complete*
  weighted graph (every off-diagonal entry is positive), the elementary variance identity
  `∑ x ∑ y, (u x - u y)^2 = 2 * card X * ∑ x, (u x)^2 - 2 * (∑ x, u x)^2` makes the argument
  quantitative: for every lower bound `w` on the off-diagonal entries and every mean-zero `u`,
  `card X * w * energy u ≤ dirichletForm G u` (`dirichletForm_ge_of_weight`). Taking `w` to be the
  minimum off-diagonal weight gives the *combinatorial Dirichlet gap*
  `dirichletGap G = card X * minWeight G`, which is strictly positive
  (`dirichletGap_pos`) and satisfies the Poincaré inequality
  `dirichletGap G * energy u ≤ dirichletForm G u` (`poincare_inequality`).
* **Exponential energy decay.** For a solution of `∂_t u = Δ u` whose mean vanishes at every
  positive time, the weighted energy `t ↦ exp (2 * Λ * t) * energy (u t)` is antitone for any
  `Λ` satisfying the Poincaré inequality, hence
  `energy (u T) ≤ energy (u ε) * exp (-(2 * Λ) * (T - ε))` (`energy_decay_of_meanZero`).
  The mean itself is conserved (`hasDerivAt_mean`), because the pinned Laplacian annihilates the
  constants, so the hypothesis is automatic for mean-zero initial data.
* **Convergence of the kernel to equilibrium.** For the pinned kernel and the equilibrium
  (uniform) function `equilibrium x = (card X)⁻¹`, the deviation
  `x ↦ finiteHeatKernel G x y t - equilibrium x` has zero mean for `t > 0`, solves the same
  equation, and has the Dirac energy `1 - (card X)⁻¹` as `t → 0⁺`. Consequently
  `energy (K · y T - equilibrium) ≤ (1 - (card X)⁻¹) * exp (-(2 * Λ) * T)`
  (`finiteHeatKernel_energy_decay`), the energy tends to `0` as `T → ∞`
  (`finiteHeatKernel_tendsto_equilibrium_energy`), and the kernel itself converges to the
  equilibrium value pointwise with the exponential bound
  `|K x y t - (card X)⁻¹| ≤ sqrt (1 - (card X)⁻¹) * exp (-(Λ * t))`
  (`finiteHeatKernel_pointwise_decay`).

**Scope and honesty.** This is the finite-dimensional model of the long-time (spectral-gap)
asymptotics of the heat kernel, i.e. of one of the analytic items listed as remaining manifold
content of `D7-HEAT-KERNEL-EXISTENCE`. It is *not* a proof of that blocker: the Laplace–Beltrami
operator, the manifold Poincaré inequality, parabolic regularity and the manifold heat-kernel
construction remain open, and no named blocker is closed. All proofs are complete: no `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel

/-! ## I. Mean-zero functions, the Dirichlet form and the Poincaré inequality -/

namespace FiniteHeatOperator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The mean-zero condition**: a function whose total sum vanishes. This is the orthogonality
condition to the constants that selects the fluctuating part of a function; the heat kernel's
deviation from its equilibrium value is mean-zero in the spatial variable. -/
def meanZero (u : X → ℝ) : Prop := ∑ x, u x = 0

/-- A function whose total sum is `card X * c` has mean-zero deviation from the constant `c`. -/
theorem meanZero_sub_const {u : X → ℝ} {c : ℝ} (h : ∑ x, u x = (Fintype.card X : ℝ) * c) :
    meanZero (fun x => u x - c) := by
  rw [meanZero, Finset.sum_sub_distrib, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The inner Dirichlet sum is nonnegative: the diagonal terms vanish and the off-diagonal entries
of the pinned operator are strictly positive. -/
theorem dirichlet_inner_nonneg (G : FiniteHeatOperator X) (u : X → ℝ) (x : X) :
    0 ≤ ∑ y, G.L x y * (u x - u y) ^ 2 :=
  Finset.sum_nonneg fun y _ => by
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · exact mul_nonneg (le_of_lt (G.offdiag_pos x y hxy)) (sq_nonneg _)

/-- **The Dirichlet form** of the pinned finite operator:
`(1/2) * ∑ x ∑ y, L x y * (u x - u y)^2`. It is nonnegative, vanishes exactly on the constants, and
controls the `ℓ²` energy of mean-zero functions through the combinatorial gap. -/
noncomputable def dirichletForm (G : FiniteHeatOperator X) (u : X → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2

/-- The Dirichlet form is nonnegative. -/
theorem dirichletForm_nonneg (G : FiniteHeatOperator X) (u : X → ℝ) :
    0 ≤ G.dirichletForm u :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => G.dirichlet_inner_nonneg u x)

/-- **The Dirichlet form is the negative of the quadratic form**: this is the finite-level
dissipativity identity `∑ x, u x * Δ u x = -(1/2) * ∑ x ∑ y, L x y (u x - u y)^2`. -/
theorem dirichletForm_eq_neg_quadraticForm (G : FiniteHeatOperator X) (u : X → ℝ) :
    G.dirichletForm u = -(∑ x, u x * G.laplacian u x) := by
  have h := G.laplacian_dirichlet_identity u
  simp only [dirichletForm]
  linarith

/-- **The variance identity**:
`∑ x ∑ y, (u x - u y)^2 = 2 * card X * ∑ x, (u x)^2 - 2 * (∑ x, u x)^2`.
This is the elementary computation that turns the (complete) graph structure of the pinned operator
into a *quantitative* Poincaré inequality. -/
theorem sum_sq_sub_eq (u : X → ℝ) :
    ∑ x, ∑ y, (u x - u y) ^ 2 =
      2 * (Fintype.card X : ℝ) * (∑ x, (u x) ^ 2) - 2 * (∑ x, u x) ^ 2 := by
  have hrow : ∀ x : X, ∑ y, (u x - u y) ^ 2 =
      (Fintype.card X : ℝ) * (u x) ^ 2 - 2 * u x * (∑ y, u y) + ∑ y, (u y) ^ 2 := by
    intro x
    have h1 : ∑ y, (u x - u y) ^ 2 =
        ∑ y, ((u x) ^ 2 - 2 * (u x * u y) + (u y) ^ 2) :=
      Finset.sum_congr rfl fun y _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2 : ∑ y : X, (u x) ^ 2 = (Fintype.card X : ℝ) * (u x) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : ∑ y : X, 2 * (u x * u y) = 2 * u x * ∑ y, u y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [h2, h3]
  have hA : ∑ x : X, (Fintype.card X : ℝ) * (u x) ^ 2 =
      (Fintype.card X : ℝ) * ∑ x, (u x) ^ 2 := by
    rw [Finset.mul_sum]
  have hB : ∑ x : X, 2 * u x * (∑ y, u y) = 2 * (∑ x, u x) * (∑ y, u y) := by
    rw [show (∑ x : X, 2 * u x * (∑ y, u y)) = ∑ x : X, (2 * (∑ y, u y)) * u x from
      Finset.sum_congr rfl fun x _ => by ring]
    rw [← Finset.mul_sum]
  have hC : ∑ x : X, (∑ y, (u y) ^ 2) = (Fintype.card X : ℝ) * ∑ y, (u y) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ∑ x, ∑ y, (u x - u y) ^ 2
      = ∑ x, ((Fintype.card X : ℝ) * (u x) ^ 2 - 2 * u x * (∑ y, u y) +
          ∑ y, (u y) ^ 2) :=
        Finset.sum_congr rfl fun x _ => hrow x
    _ = (∑ x : X, (Fintype.card X : ℝ) * (u x) ^ 2) - (∑ x : X, 2 * u x * (∑ y, u y)) +
          (∑ x : X, ∑ y, (u y) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 2 * (Fintype.card X : ℝ) * (∑ x, (u x) ^ 2) - 2 * (∑ x, u x) ^ 2 := by
        rw [hA, hB, hC]
        have hs : (∑ y, u y) = (∑ x, u x) := rfl
        have hs2 : (∑ y, (u y) ^ 2) = (∑ x, (u x) ^ 2) := rfl
        rw [hs, hs2]
        ring

/-- For a mean-zero function the variance identity reduces to
`∑ x ∑ y, (u x - u y)^2 = 2 * card X * energy u`. -/
theorem sum_sq_sub_eq_of_meanZero (G : FiniteHeatOperator X) {u : X → ℝ} (h : meanZero u) :
    ∑ x, ∑ y, (u x - u y) ^ 2 = 2 * (Fintype.card X : ℝ) * G.energy u := by
  rw [sum_sq_sub_eq, h]
  simp [energy]

/-- **The quantitative Poincaré inequality (weight form)**: if `w` is a lower bound for the
off-diagonal entries of the pinned operator, then for every mean-zero `u`
`card X * w * energy u ≤ dirichletForm G u`. -/
theorem dirichletForm_ge_of_weight (G : FiniteHeatOperator X) (u : X → ℝ) {w : ℝ}
    (hw : ∀ x y : X, x ≠ y → w ≤ G.L x y) (hmean : meanZero u) :
    (Fintype.card X : ℝ) * w * G.energy u ≤ G.dirichletForm u := by
  have hS : w * ∑ x, ∑ y, (u x - u y) ^ 2 ≤ ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · exact mul_le_mul_of_nonneg_right (hw x y hxy) (sq_nonneg _)
  have hvar : (∑ x, ∑ y, (u x - u y) ^ 2) = 2 * (Fintype.card X : ℝ) * G.energy u :=
    sum_sq_sub_eq_of_meanZero G hmean
  calc (Fintype.card X : ℝ) * w * G.energy u
      = (1 / 2) * (w * (2 * (Fintype.card X : ℝ) * G.energy u)) := by ring
    _ = (1 / 2) * (w * ∑ x, ∑ y, (u x - u y) ^ 2) := by rw [hvar]
    _ ≤ (1 / 2) * ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2 :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = G.dirichletForm u := by rw [dirichletForm]

/-- **The minimal off-diagonal weight** of the pinned operator, over the (nonempty, when the space
has two distinct points) set of ordered pairs of distinct points. -/
noncomputable def minWeight (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) : ℝ :=
  ((Finset.univ.filter (fun p : X × X => p.1 ≠ p.2)).image
      (fun p : X × X => G.L p.1 p.2)).min'
    (by
      obtain ⟨x, y, hxy⟩ := h
      exact ⟨G.L x y, Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩⟩)

/-- The minimal off-diagonal weight is a lower bound for every off-diagonal entry. -/
theorem minWeight_le (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) {x y : X}
    (hxy : x ≠ y) : G.minWeight h ≤ G.L x y :=
  Finset.min'_le
    ((Finset.univ.filter (fun p : X × X => p.1 ≠ p.2)).image (fun p : X × X => G.L p.1 p.2))
    (G.L x y)
    (Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩)

/-- **The minimal off-diagonal weight is strictly positive** (the pinned operator is a complete
weighted graph). -/
theorem minWeight_pos (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    0 < G.minWeight h := by
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp
    (Finset.min'_mem
      ((Finset.univ.filter (fun p : X × X => p.1 ≠ p.2)).image (fun p : X × X => G.L p.1 p.2)) _)
  obtain ⟨-, hpq⟩ := Finset.mem_filter.mp hv
  rw [minWeight, ← hveq]
  exact G.offdiag_pos v.1 v.2 hpq

/-- **The combinatorial Dirichlet gap** of the pinned operator: `card X` times the minimal
off-diagonal weight. For the complete-graph operator this is exactly `card X`, the true spectral
gap; in general it is a computable strictly positive lower bound for it. -/
noncomputable def dirichletGap (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) : ℝ :=
  (Fintype.card X : ℝ) * G.minWeight h

/-- **The Dirichlet gap is strictly positive.** -/
theorem dirichletGap_pos (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    0 < G.dirichletGap h := by
  obtain ⟨x, y, hxy⟩ := h
  haveI : Nonempty X := ⟨x⟩
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  exact mul_pos hcard (G.minWeight_pos ⟨x, y, hxy⟩)

/-- **The Poincaré (spectral-gap) inequality** of the pinned finite operator: the Dirichlet form
dominates the gap times the energy on every mean-zero function. -/
theorem poincare_inequality (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) {u : X → ℝ}
    (hmean : meanZero u) :
    G.dirichletGap h * G.energy u ≤ G.dirichletForm u := by
  have hw : ∀ x y : X, x ≠ y → G.minWeight h ≤ G.L x y := fun x y hxy => G.minWeight_le h hxy
  have := G.dirichletForm_ge_of_weight u hw hmean
  simpa only [dirichletGap, mul_assoc] using this

/-- **The Dirichlet form vanishes exactly on the constants**: the kernel of the Dirichlet form of a
pinned operator is the constants, because every off-diagonal entry is strictly positive. -/
theorem dirichletForm_eq_zero_iff [Nonempty X] (G : FiniteHeatOperator X) {u : X → ℝ} :
    G.dirichletForm u = 0 ↔ ∃ c : ℝ, u = fun _ => c := by
  constructor
  · intro h
    have hS : ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hinner : ∀ x : X, ∑ y, G.L x y * (u x - u y) ^ 2 = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg fun x _ => G.dirichlet_inner_nonneg u x).mp hS x
        (Finset.mem_univ x)
    refine ⟨u (Classical.arbitrary X), ?_⟩
    funext x
    have hterm : ∀ y : X, G.L x y * (u x - u y) ^ 2 = 0 := fun y =>
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ => by
        rcases eq_or_ne x y with rfl | hxy
        · simp
        · exact mul_nonneg (le_of_lt (G.offdiag_pos x y hxy)) (sq_nonneg _)).mp (hinner x) y
          (Finset.mem_univ y)
    rcases eq_or_ne x (Classical.arbitrary X) with hx | hx
    · rw [hx]
    · have hzero := hterm (Classical.arbitrary X)
      have hL : G.L x (Classical.arbitrary X) ≠ 0 := ne_of_gt (G.offdiag_pos x _ hx)
      have hsq : (u x - u (Classical.arbitrary X)) ^ 2 = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hL
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · rintro ⟨c, rfl⟩
    simp [dirichletForm]

/-! ## I.b Sharpness of the Poincaré constant on the complete graph

For the pinned operator of the complete graph the minimal off-diagonal weight is `1`, so the
combinatorial Dirichlet gap is exactly `card X`; moreover the Poincaré inequality is an *equality*
on every mean-zero function. Hence the constant obtained from the variance identity is optimal. -/

/-- The complete-graph operator has off-diagonal entries `1`. -/
theorem completeGraphOperator_apply_of_ne {x y : X} (hxy : x ≠ y) :
    (completeGraphOperator X).L x y = 1 := by
  simp [completeGraphOperator, hxy]

/-- The complete-graph operator has diagonal entries `1 - card X`. -/
theorem completeGraphOperator_apply_self (x : X) :
    (completeGraphOperator X).L x x = 1 - (Fintype.card X : ℝ) := by
  simp [completeGraphOperator]

/-- **The minimal off-diagonal weight of the complete graph is `1`.** -/
theorem completeGraphOperator_minWeight (h : ∃ x y : X, x ≠ y) :
    (completeGraphOperator X).minWeight h = 1 := by
  obtain ⟨x, y, hxy⟩ := h
  refine le_antisymm ?_ ?_
  · calc (completeGraphOperator X).minWeight ⟨x, y, hxy⟩ ≤ (completeGraphOperator X).L x y :=
          (completeGraphOperator X).minWeight_le ⟨x, y, hxy⟩ hxy
      _ = 1 := completeGraphOperator_apply_of_ne hxy
  · rw [minWeight]
    refine Finset.le_min' _ _ (1 : ℝ) ?_
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨-, hpq⟩ := Finset.mem_filter.mp hp
    rw [completeGraphOperator_apply_of_ne hpq]

/-- **The Dirichlet gap of the complete graph is exactly `card X`** (the true spectral gap of the
complete-graph Laplacian). -/
theorem completeGraphOperator_dirichletGap (h : ∃ x y : X, x ≠ y) :
    (completeGraphOperator X).dirichletGap h = (Fintype.card X : ℝ) := by
  rw [dirichletGap, completeGraphOperator_minWeight h, mul_one]

/-- **The Dirichlet form of the complete-graph operator is exactly `card X * energy` on mean-zero
functions**: the Poincaré inequality for the complete graph is an equality, so the combinatorial
constant `card X` is optimal. -/
theorem completeGraphOperator_dirichletForm_eq (u : X → ℝ) (hmean : meanZero u) :
    (completeGraphOperator X).dirichletForm u =
      (Fintype.card X : ℝ) * (completeGraphOperator X).energy u := by
  have hL : ∀ x y : X,
      (completeGraphOperator X).L x y * (u x - u y) ^ 2 = (u x - u y) ^ 2 := by
    intro x y
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · rw [completeGraphOperator_apply_of_ne hxy, one_mul]
  rw [dirichletForm,
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hL x y,
    sum_sq_sub_eq_of_meanZero (completeGraphOperator X) hmean]
  ring

/-- **Sharpness of the combinatorial Poincaré constant**: on the complete graph the gap times the
energy equals the Dirichlet form on every mean-zero function. -/
theorem completeGraphOperator_poincare_attained (h : ∃ x y : X, x ≠ y) (u : X → ℝ)
    (hmean : meanZero u) :
    (completeGraphOperator X).dirichletGap h * (completeGraphOperator X).energy u =
      (completeGraphOperator X).dirichletForm u := by
  rw [completeGraphOperator_dirichletGap h, completeGraphOperator_dirichletForm_eq u hmean]

/-! ## II. Mean conservation and exponential energy decay -/

/-- **The pinned Laplacian annihilates the constants, summed**: `∑ x, Δ u x = 0` for every `u`
(the column sums of the pinned operator vanish). Equivalently, the total mass is conserved by the
evolution. -/
theorem sum_laplacian_eq_zero (G : FiniteHeatOperator X) (u : X → ℝ) :
    ∑ x, G.laplacian u x = 0 := by
  simp only [laplacian_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [← Finset.sum_mul]
  have hcol : ∑ x, G.L x y = 0 := by
    rw [← G.conservative y]
    exact Finset.sum_congr rfl fun x _ => (G.symmetric_apply x y).symm
  rw [hcol, zero_mul]

/-- **The mean of a solution of `∂_t u = Δ u` is conserved** (infinitesimally): the total sum has
zero derivative at every positive time, because `Δ` annihilates the constants. -/
theorem hasDerivAt_mean (G : FiniteHeatOperator X) (u : ℝ → X → ℝ) {t : ℝ}
    (h : ∀ x, HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t) :
    HasDerivAt (fun s : ℝ => ∑ x, u s x) 0 t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ x : X, u s x)
      (∑ x : X, G.laplacian (u t) x) t := by
    have h' := HasDerivAt.sum (u := Finset.univ) (A := fun x s => u s x)
      (A' := fun x => G.laplacian (u t) x) fun x _ => h x
    have hfun : (∑ x : X, fun s : ℝ => u s x) = fun s : ℝ => ∑ x : X, u s x := by
      funext s
      simp only [Finset.sum_apply]
    rwa [hfun] at h'
  rwa [G.sum_laplacian_eq_zero (u t)] at hsum

/-- **Exponential energy decay with rate `Λ`.** If `Λ` satisfies the Poincaré inequality on
mean-zero functions and `u` is a solution of `∂_t u = Δ u` whose mean vanishes at every positive
time, then on `[ε, T]` the energy decays at rate `2 * Λ`:
`energy (u T) ≤ energy (u ε) * exp (-(2 * Λ) * (T - ε))`.
The proof is the classical Gronwall argument: the weighted energy `exp (2 * Λ * t) * energy (u t)`
has derivative `exp (2 * Λ * t) * (2 * Λ * energy - 2 * dirichletForm) ≤ 0`. -/
theorem energy_decay_of_meanZero (G : FiniteHeatOperator X) (u : ℝ → X → ℝ) {Λ : ℝ}
    (hgap : ∀ t : ℝ, 0 < t → Λ * G.energy (u t) ≤ G.dirichletForm (u t))
    (hu : ∀ t : ℝ, 0 < t → ∀ x : X,
      HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t)
    {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    G.energy (u T) ≤ G.energy (u ε) * Real.exp (-(2 * Λ) * (T - ε)) := by
  have hexp_deriv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Real.exp (2 * Λ * s)) (Real.exp (2 * Λ * t) * (2 * Λ)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (2 * Λ) * s) ((2 * Λ) * 1) t :=
      (hasDerivAt_id t).const_mul (2 * Λ)
    simpa using h1.exp
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun s : ℝ => Real.exp (2 * Λ * s) * G.energy (u s))
      (Real.exp (2 * Λ * t) *
        (2 * Λ * G.energy (u t) - 2 * G.dirichletForm (u t))) t := by
    intro t ht
    have hE := hasDerivAt_energy G u (fun x => hu t ht x)
    have h := (hexp_deriv t).mul hE
    have hval : Real.exp (2 * Λ * t) * (2 * Λ) * G.energy (u t) +
        Real.exp (2 * Λ * t) * (2 * ∑ x, u t x * G.laplacian (u t) x) =
        Real.exp (2 * Λ * t) *
          (2 * Λ * G.energy (u t) - 2 * G.dirichletForm (u t)) := by
      rw [G.dirichletForm_eq_neg_quadraticForm (u t)]
      ring
    rw [hval] at h
    exact h
  have hanti : AntitoneOn (fun t : ℝ => Real.exp (2 * Λ * t) * G.energy (u t))
      (Set.Icc ε T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc ε T) ?_ ?_ ?_
    · intro t ht
      exact (hderiv t (lt_of_lt_of_le hε ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t (lt_trans hε ht.1)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t (lt_trans hε ht.1)).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) ?_
      linarith [hgap t (lt_trans hε ht.1)]
  have hmono := hanti ⟨le_rfl, hεT⟩ ⟨hεT, le_rfl⟩ hεT
  have hmul := mul_le_mul_of_nonneg_left hmono (le_of_lt (Real.exp_pos (-(2 * Λ * T))))
  have hleft : Real.exp (-(2 * Λ * T)) *
      (Real.exp (2 * Λ * T) * G.energy (u T)) = G.energy (u T) := by
    rw [← mul_assoc, ← Real.exp_add, show -(2 * Λ * T) + 2 * Λ * T = 0 by ring, Real.exp_zero,
      one_mul]
  have hright : Real.exp (-(2 * Λ * T)) *
      (Real.exp (2 * Λ * ε) * G.energy (u ε)) =
      Real.exp (-(2 * Λ) * (T - ε)) * G.energy (u ε) := by
    rw [← mul_assoc, ← Real.exp_add, show -(2 * Λ * T) + 2 * Λ * ε = -(2 * Λ) * (T - ε) by ring]
  rw [hleft, hright] at hmul
  simpa only [mul_comm] using hmul

/-! ## III. The heat kernel converges to equilibrium exponentially -/

section Kernel

variable [TopologicalSpace X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- **The equilibrium (uniform) function** `x ↦ (card X)⁻¹`, the limit of the heat kernel as
`t → ∞` (the normalized invariant measure of the pinned finite Laplacian). -/
noncomputable def equilibrium : X → ℝ := fun _ => (Fintype.card X : ℝ)⁻¹

/-- `1 - (card X)⁻¹` is nonnegative (it is the squared `ℓ²` energy of the Dirac minus equilibrium
distribution, up to the factor `1 - (card X)⁻¹` itself). -/
theorem one_sub_inv_card_nonneg (y : X) : 0 ≤ 1 - (Fintype.card X : ℝ)⁻¹ := by
  haveI : Nonempty X := ⟨y⟩
  have hcard : (1 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < (Fintype.card X : ℝ) := by linarith
  have hinv : (Fintype.card X : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcard
  linarith

/-- The heat kernel has unit *column* mass (row sums plus symmetry). -/
theorem finiteHeatKernel_column_sum (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (y : X) :
    ∑ x, finiteHeatKernel G x y t = 1 := by
  rw [show (∑ x, finiteHeatKernel G x y t) = ∑ x, finiteHeatKernel G y x t from
    Finset.sum_congr rfl fun x _ => finiteHeatKernel_symm G x y t]
  exact finiteHeatKernel_row_sum G ht y

/-- **The deviation of the kernel from equilibrium is mean-zero** in the spatial variable. -/
theorem finiteHeatKernel_shift_meanZero (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (y : X) :
    meanZero (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x) := by
  haveI : Nonempty X := ⟨y⟩
  refine meanZero_sub_const ?_
  rw [finiteHeatKernel_column_sum G ht y]
  exact (mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)).symm

/-- **Adding a constant to a solution does not change its Laplacian**, because the pinned Laplacian
annihilates the constants. -/
theorem laplacian_sub_const (G : FiniteHeatOperator X) (u : X → ℝ) (c : ℝ) :
    G.laplacian (fun x => u x - c) = G.laplacian u := by
  have h : (fun x : X => u x - c) = u - fun _ => c := rfl
  rw [h, map_sub]
  have hc : G.laplacian (fun _ : X => c) = 0 := by
    have hconst : (fun _ : X => c) = c • (fun _ : X => (1 : ℝ)) := by
      funext x
      simp
    rw [hconst, map_smul, G.laplacian_one, smul_zero]
  rw [hc, sub_zero]

/-- The spatial PDE for the equilibrium-shifted kernel. -/
theorem finiteHeatKernel_shift_hasDerivAt (G : FiniteHeatOperator X) (y x : X) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => finiteHeatKernel G x y s - equilibrium (X := X) x)
      (G.laplacian (fun z => finiteHeatKernel G z y t - equilibrium (X := X) z) x) t := by
  have h := (finiteHeatKernel_hasDerivAt G x y ht).sub_const (equilibrium (X := X) x)
  have hlap : G.laplacian (fun z => finiteHeatKernel G z y t - equilibrium (X := X) z) =
      G.laplacian (fun z => finiteHeatKernel G z y t) := by
    rw [show (fun z : X => finiteHeatKernel G z y t - equilibrium (X := X) z) =
        (fun z : X => finiteHeatKernel G z y t - (Fintype.card X : ℝ)⁻¹) from by
      funext z
      simp [equilibrium]]
    rw [laplacian_sub_const]
  rw [hlap]
  exact h

/-- **The Dirac limit of the kernel entry**: as `t → 0⁺` the pinned kernel converges to the identity
matrix, i.e. to the pointwise Dirac initial data. -/
theorem finiteHeatKernel_tendsto_entry (G : FiniteHeatOperator X) (x y : X) :
    Tendsto (fun t : ℝ => finiteHeatKernel G x y t) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 : Matrix X X ℝ) x y)) := by
  have hev : (fun t : ℝ => finiteHeatKernel G x y t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => (NormedSpace.exp (t • G.L)) x y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact finiteHeatKernel_of_pos G ht x y
  exact Tendsto.congr' hev.symm (G.tendsto_exp_smul_entry x y)

/-- **The limit of the shifted kernel's energy as `t → 0⁺`** is the energy of the Dirac minus
equilibrium distribution, `1 - (card X)⁻¹`. -/
theorem energy_dirac_sub_equilibrium (G : FiniteHeatOperator X) (y : X) :
    G.energy (fun x => (1 : Matrix X X ℝ) x y - equilibrium (X := X) x) =
      1 - (Fintype.card X : ℝ)⁻¹ := by
  haveI : Nonempty X := ⟨y⟩
  rw [energy, ← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  have hother : ∀ x ∈ Finset.univ.erase y,
      ((1 : Matrix X X ℝ) x y - equilibrium (X := X) x) ^ 2 =
        ((Fintype.card X : ℝ)⁻¹) ^ 2 := by
    intro x hx
    rw [Finset.mem_erase] at hx
    rw [Matrix.one_apply_ne hx.1, equilibrium]
    ring
  rw [Finset.sum_congr rfl hother, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ, nsmul_eq_mul]
  rw [show ((1 : Matrix X X ℝ) y y - equilibrium (X := X) y) = 1 - (Fintype.card X : ℝ)⁻¹ from by
    rw [Matrix.one_apply_eq, equilibrium]]
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard1 : ((Fintype.card X - 1 : ℕ) : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos), Nat.cast_one]
  rw [hcard1]
  field_simp
  ring

/-- **The energy of the shifted kernel tends to the Dirac-minus-equilibrium energy** as
`t → 0⁺`. -/
theorem finiteHeatKernel_shift_tendsto_energy (G : FiniteHeatOperator X) (y : X) :
    Tendsto
      (fun t : ℝ => G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 - (Fintype.card X : ℝ)⁻¹)) := by
  have hsum : Tendsto
      (fun t : ℝ => G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (G.energy (fun x => (1 : Matrix X X ℝ) x y - equilibrium (X := X) x))) := by
    have h := tendsto_finsetSum (Finset.univ : Finset X)
      (f := fun x (t : ℝ) => (finiteHeatKernel G x y t - equilibrium (X := X) x) ^ 2)
      (a := fun x => ((1 : Matrix X X ℝ) x y - equilibrium (X := X) x) ^ 2)
      (fun x _ => ((finiteHeatKernel_tendsto_entry G x y).sub
        (tendsto_const_nhds (x := equilibrium (X := X) x))).pow 2)
    simpa only [energy] using h
  rwa [energy_dirac_sub_equilibrium G y] at hsum

/-- The kinetic part of the decay inequality: the energy of the shifted kernel is antitone up to the
Gronwall weight on every compact positive time interval. -/
theorem finiteHeatKernel_shift_energy_decay (G : FiniteHeatOperator X) (y : X) {Λ : ℝ}
    (hgap : ∀ u : X → ℝ, meanZero u → Λ * G.energy u ≤ G.dirichletForm u)
    {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
      G.energy (fun x => finiteHeatKernel G x y ε - equilibrium (X := X) x) *
        Real.exp (-(2 * Λ) * (T - ε)) :=
  energy_decay_of_meanZero G
    (fun t => fun x => finiteHeatKernel G x y t - equilibrium (X := X) x)
    (fun t ht => hgap _ (finiteHeatKernel_shift_meanZero G ht y))
    (fun t ht x => finiteHeatKernel_shift_hasDerivAt G y x ht) hε hεT

/-- **Exponential decay of the kernel's energy to equilibrium**: for every `T > 0`,
`energy (K · y T - equilibrium) ≤ (1 - (card X)⁻¹) * exp (-(2 * Λ) * T)`, obtained by letting the
lower endpoint of the Gronwall inequality tend to `0⁺` (the Dirac energy). -/
theorem finiteHeatKernel_energy_decay (G : FiniteHeatOperator X) (y : X) {Λ : ℝ}
    (hgap : ∀ u : X → ℝ, meanZero u → Λ * G.energy u ≤ G.dirichletForm u)
    {T : ℝ} (hT : 0 < T) :
    G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
      (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * Λ) * T) := by
  have hIio : Set.Iio T ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio T, Iio_mem_nhds hT, fun x hx => hx.1⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
        G.energy (fun x => finiteHeatKernel G x y ε - equilibrium (X := X) x) *
          Real.exp (-(2 * Λ) * (T - ε)) := by
    filter_upwards [self_mem_nhdsWithin, hIio] with ε hε hεT
    exact finiteHeatKernel_shift_energy_decay G y hgap hε (le_of_lt hεT)
  have hexp : Tendsto (fun ε : ℝ => Real.exp (-(2 * Λ) * (T - ε))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.exp (-(2 * Λ) * T))) := by
    have hcont : Continuous fun ε : ℝ => Real.exp (-(2 * Λ) * (T - ε)) := by fun_prop
    have h0 : Tendsto (fun ε : ℝ => Real.exp (-(2 * Λ) * (T - ε))) (𝓝 (0 : ℝ))
        (𝓝 (Real.exp (-(2 * Λ) * (T - 0)))) := hcont.continuousAt.tendsto
    rw [sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun ε : ℝ => G.energy (fun x => finiteHeatKernel G x y ε - equilibrium (X := X) x) *
        Real.exp (-(2 * Λ) * (T - ε))) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * Λ) * T))) :=
    (finiteHeatKernel_shift_tendsto_energy G y).mul hexp
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev

/-- **Decay at the combinatorial Dirichlet gap**: the previous bound with the explicit gap
`Λ = dirichletGap G`, which is strictly positive as soon as the space has two distinct points. -/
theorem finiteHeatKernel_energy_decay_gap (G : FiniteHeatOperator X) (y : X)
    (h : ∃ x y : X, x ≠ y) {T : ℝ} (hT : 0 < T) :
    G.energy (fun x => finiteHeatKernel G x y T - equilibrium (X := X) x) ≤
      (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * G.dirichletGap h) * T) :=
  finiteHeatKernel_energy_decay G y (fun u hu => G.poincare_inequality h hu) hT

/-- **The energy of the kernel's deviation from equilibrium tends to `0`** at infinity, at rate
`exp (-(2 * Λ) * t)`. -/
theorem finiteHeatKernel_tendsto_equilibrium_energy (G : FiniteHeatOperator X) (y : X) {Λ : ℝ}
    (hgap : ∀ u : X → ℝ, meanZero u → Λ * G.energy u ≤ G.dirichletForm u) (hΛ : 0 < Λ) :
    Tendsto
      (fun t : ℝ => G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x))
      atTop (𝓝 0) := by
  have hdecay : Tendsto (fun t : ℝ =>
      (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * Λ) * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (2 * Λ) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) Filter.tendsto_id
    have h2 : Tendsto (fun t : ℝ => Real.exp (-((2 * Λ) * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 : Tendsto (fun t : ℝ => Real.exp (-(2 * Λ) * t)) atTop (𝓝 0) := by
      convert h2 using 1
      funext t
      congr 1
      ring
    simpa using h3.const_mul (1 - (Fintype.card X : ℝ)⁻¹)
  have hnn := one_sub_inv_card_nonneg (X := X) y
  have htrunc : Tendsto (fun t : ℝ =>
      if 0 < t then
        G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x) else 0)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun t => ?_) (fun t => ?_) hdecay
    · by_cases ht : 0 < t
      · simp only [ht, ite_true]
        exact energy_nonneg G _
      · simp only [ht, ite_false, le_refl]
    · by_cases ht : 0 < t
      · simp only [ht, ite_true]
        exact finiteHeatKernel_energy_decay G y hgap ht
      · simp only [ht, ite_false]
        exact mul_nonneg hnn (le_of_lt (Real.exp_pos _))
  refine Tendsto.congr' ?_ htrunc
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
  have ht' : 0 < t := ht
  simp only [ht', ite_true]

/-- **Pointwise exponential convergence of the heat kernel to the equilibrium value**
`(card X)⁻¹`. -/
theorem finiteHeatKernel_pointwise_decay (G : FiniteHeatOperator X) (y : X) {Λ : ℝ}
    (hgap : ∀ u : X → ℝ, meanZero u → Λ * G.energy u ≤ G.dirichletForm u)
    {t : ℝ} (ht : 0 < t) (x : X) :
    |finiteHeatKernel G x y t - equilibrium (X := X) x| ≤
      Real.sqrt (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(Λ * t)) := by
  have hsingle : (finiteHeatKernel G x y t - equilibrium (X := X) x) ^ 2 ≤
      G.energy (fun x => finiteHeatKernel G x y t - equilibrium (X := X) x) := by
    rw [energy]
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun z : X => (finiteHeatKernel G z y t - equilibrium (X := X) z) ^ 2)
      (fun z _ => sq_nonneg _) (Finset.mem_univ x)
  have hbound : (finiteHeatKernel G x y t - equilibrium (X := X) x) ^ 2 ≤
      (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * Λ) * t) :=
    le_trans hsingle (finiteHeatKernel_energy_decay G y hgap ht)
  have hnonneg : 0 ≤ 1 - (Fintype.card X : ℝ)⁻¹ := one_sub_inv_card_nonneg (X := X) x
  calc |finiteHeatKernel G x y t - equilibrium (X := X) x|
      = Real.sqrt ((finiteHeatKernel G x y t - equilibrium (X := X) x) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(2 * Λ) * t)) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (1 - (Fintype.card X : ℝ)⁻¹) * Real.exp (-(Λ * t)) := by
        rw [Real.sqrt_mul hnonneg, ← Real.exp_half]
        ring_nf

/-! ## IV. Sharpness of the decay bound on the complete graph

For the complete-graph operator the heat kernel has the closed form
`K x y t = (card X)⁻¹ + exp (-(card X) * t) * (δ x y - (card X)⁻¹)`
(Because `K` is the unique solution of the pinned problem, this follows from the closed form
satisfying the PDE and the Dirac initial condition.) Its squared deviation from equilibrium is then
*exactly* `(1 - (card X)⁻¹) * exp (-(2 * card X) * t)`, so the exponential decay bound of
`finiteHeatKernel_energy_decay` is attained: for the complete-graph operator the combinatorial gap
is the true spectral gap and the bound is optimal. -/

/-- **The closed-form complete-graph heat kernel**
`(card X)⁻¹ + exp (-(card X) * t) * (δ x y - (card X)⁻¹)`. -/
noncomputable def completeGraphKernelForm (x y : X) (t : ℝ) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ +
    Real.exp (-((Fintype.card X : ℝ) * t)) *
      ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹)

/-- `∑ z, L x z * (1 : Matrix X X ℝ) z y = L x y` (the Dirac column picks out one entry). -/
theorem sum_mul_one_apply (G : FiniteHeatOperator X) (x y : X) :
    ∑ z, G.L x z * (1 : Matrix X X ℝ) z y = G.L x y := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    rw [Matrix.one_apply_ne hz, mul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- **The Laplacian of the closed form**: `Δ K(·,y,t) x = -card X * exp (-(card X) * t) * d`,
where `d = δ x y - (card X)⁻¹`. -/
theorem completeGraphOperator_laplacian_kernelForm (x y : X) (t : ℝ) :
    (completeGraphOperator X).laplacian (fun z => completeGraphKernelForm z y t) x =
      -((Fintype.card X : ℝ)) * Real.exp (-((Fintype.card X : ℝ) * t)) *
        ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹) := by
  haveI : Nonempty X := ⟨x⟩
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [laplacian_apply, Matrix.mulVec, dotProduct]
  have hsplit : ∀ z : X,
      (completeGraphOperator X).L x z * completeGraphKernelForm z y t =
        (Fintype.card X : ℝ)⁻¹ * (completeGraphOperator X).L x z +
          Real.exp (-((Fintype.card X : ℝ) * t)) *
            ((completeGraphOperator X).L x z *
              ((1 : Matrix X X ℝ) z y - (Fintype.card X : ℝ)⁻¹)) := by
    intro z
    simp only [completeGraphKernelForm]
    ring
  rw [Finset.sum_congr rfl fun z _ => hsplit z, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have hrow : ∑ z, (completeGraphOperator X).L x z = 0 := (completeGraphOperator X).conservative x
  have hdirac : ∑ z, (completeGraphOperator X).L x z *
        ((1 : Matrix X X ℝ) z y - (Fintype.card X : ℝ)⁻¹) =
      (completeGraphOperator X).L x y := by
    rw [Finset.sum_congr rfl fun z _ => mul_sub _ _ _, Finset.sum_sub_distrib,
      sum_mul_one_apply]
    have h2 : ∑ z, (completeGraphOperator X).L x z * (Fintype.card X : ℝ)⁻¹ =
        (Fintype.card X : ℝ)⁻¹ * ∑ z, (completeGraphOperator X).L x z := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [h2, hrow, mul_zero, sub_zero]
  rw [hrow, mul_zero, zero_add, hdirac]
  by_cases hxy : x = y
  · rcases hxy with rfl
    rw [completeGraphOperator_apply_self, Matrix.one_apply_eq]
    field_simp
    ring
  · rw [completeGraphOperator_apply_of_ne hxy, Matrix.one_apply_ne hxy]
    field_simp
    ring

/-- **The time derivative of the closed form**. -/
theorem completeGraphKernelForm_hasDerivAt (x y : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => completeGraphKernelForm x y s)
      (-((Fintype.card X : ℝ)) * Real.exp (-((Fintype.card X : ℝ) * t)) *
        ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹)) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-((Fintype.card X : ℝ) * s)))
      (Real.exp (-((Fintype.card X : ℝ) * t)) * (-((Fintype.card X : ℝ)))) t := by
    have h := ((hasDerivAt_id t).const_mul (-((Fintype.card X : ℝ)))).exp
    simpa using h
  have h2 := h1.mul_const ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹)
  have h3 := h2.const_add ((Fintype.card X : ℝ)⁻¹)
  have hfun : (fun s : ℝ => (Fintype.card X : ℝ)⁻¹ +
      Real.exp (-((Fintype.card X : ℝ) * s)) *
        ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹)) =
      fun s : ℝ => completeGraphKernelForm x y s := rfl
  rw [hfun] at h3
  exact h3.congr_deriv (by ring)

/-- **The Dirac initial condition of the closed form**. -/
theorem completeGraphKernelForm_tendsto (x y : X) :
    Tendsto (fun t : ℝ => completeGraphKernelForm x y t) (𝓝[>] (0 : ℝ))
      (𝓝 (if x = y then 1 else 0)) := by
  haveI : Nonempty X := ⟨x⟩
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcont : Continuous fun t : ℝ => completeGraphKernelForm x y t := by
    simp only [completeGraphKernelForm]
    fun_prop
  have h0 : Tendsto (fun t : ℝ => completeGraphKernelForm x y t) (𝓝 (0 : ℝ))
      (𝓝 (completeGraphKernelForm x y 0)) := hcont.continuousAt.tendsto
  have hval : completeGraphKernelForm x y 0 = (if x = y then 1 else 0) := by
    simp only [completeGraphKernelForm, mul_zero, neg_zero, Real.exp_zero, one_mul]
    by_cases hxy : x = y
    · rcases hxy with rfl
      rw [if_pos rfl, Matrix.one_apply_eq]
      ring
    · rw [if_neg hxy, Matrix.one_apply_ne hxy]
      ring
  rw [hval] at h0
  exact h0.mono_left nhdsWithin_le_nhds

/-- **The complete-graph heat kernel in closed form**: the pinned heat kernel of the complete-graph
operator equals `(card X)⁻¹ + exp (-(card X) * t) * (δ x y - (card X)⁻¹)` for `t > 0`. This is the
uniqueness theorem applied to the closed form, whose PDE and Dirac data are checked above. -/
theorem completeGraphOperator_finiteHeatKernel {t : ℝ} (ht : 0 < t) (x y : X) :
    finiteHeatKernel (completeGraphOperator X) x y t = completeGraphKernelForm x y t := by
  symm
  refine eq_finiteHeatKernel_of_pde_of_dirac (G := completeGraphOperator X)
    (K := completeGraphKernelForm) ?_ ?_ x y t ht
  · intro x y t _
    exact (completeGraphKernelForm_hasDerivAt x y t).congr_deriv
      (completeGraphOperator_laplacian_kernelForm x y t).symm
  · intro z y
    exact completeGraphKernelForm_tendsto z y

/-- **The decay bound is attained on the complete graph**: the energy of the deviation of the
complete-graph kernel from equilibrium is *exactly* `(1 - (card X)⁻¹) * exp (-(2 * card X) * t)`,
so the exponential decay theorem with the combinatorial gap is optimal. -/
theorem completeGraphOperator_energy_decay_sharp (y : X) {t : ℝ} (ht : 0 < t) :
    (completeGraphOperator X).energy
        (fun x => finiteHeatKernel (completeGraphOperator X) x y t - equilibrium (X := X) x) =
      (1 - (Fintype.card X : ℝ)⁻¹) *
        Real.exp (-(2 * (Fintype.card X : ℝ)) * t) := by
  have hterm : ∀ x : X,
      (finiteHeatKernel (completeGraphOperator X) x y t - equilibrium (X := X) x) ^ 2 =
        Real.exp (-(2 * (Fintype.card X : ℝ)) * t) *
          ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹) ^ 2 := by
    intro x
    rw [completeGraphOperator_finiteHeatKernel ht x y]
    have hexp : (Real.exp (-((Fintype.card X : ℝ) * t))) ^ 2 =
        Real.exp (-(2 * (Fintype.card X : ℝ)) * t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    simp only [completeGraphKernelForm, equilibrium]
    rw [show (Fintype.card X : ℝ)⁻¹ +
          Real.exp (-((Fintype.card X : ℝ) * t)) *
            ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹) - (Fintype.card X : ℝ)⁻¹ =
        Real.exp (-((Fintype.card X : ℝ) * t)) *
          ((1 : Matrix X X ℝ) x y - (Fintype.card X : ℝ)⁻¹) from by ring,
      mul_pow, hexp]
  rw [energy, Finset.sum_congr rfl fun x _ => hterm x, ← Finset.mul_sum]
  have hdiracenergy : (∑ i, ((1 : Matrix X X ℝ) i y - (Fintype.card X : ℝ)⁻¹) ^ 2) =
      1 - (Fintype.card X : ℝ)⁻¹ := by
    simpa only [energy, equilibrium] using energy_dirac_sub_equilibrium (completeGraphOperator X) y
  rw [hdiracenergy]
  ring

/-- **Sharpness of the exponential decay bound at the Dirichlet gap**: on the complete graph the
decay estimate of `finiteHeatKernel_energy_decay_gap` is an equality for every positive time. -/
theorem completeGraphOperator_energy_decay_attained (h : ∃ x y : X, x ≠ y) (y : X) {t : ℝ}
    (ht : 0 < t) :
    (completeGraphOperator X).energy
        (fun x => finiteHeatKernel (completeGraphOperator X) x y t - equilibrium (X := X) x) =
      (1 - (Fintype.card X : ℝ)⁻¹) *
        Real.exp (-(2 * (completeGraphOperator X).dirichletGap h) * t) := by
  rw [completeGraphOperator_dirichletGap h, completeGraphOperator_energy_decay_sharp y ht]

end Kernel

end FiniteHeatOperator

end Poincare.D13.HeatKernelBridge
