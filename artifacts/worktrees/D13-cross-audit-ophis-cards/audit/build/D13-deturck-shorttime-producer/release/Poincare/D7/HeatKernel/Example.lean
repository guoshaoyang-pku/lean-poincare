/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.Content
import Poincare.D7.HeatKernel.Instance

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.Example

**D7 heat-kernel layer, part 5: concrete non-vacuity witnesses on a two-point grid.**

On the two-point grid `Fin 2`:

* `twoPointStep` is the constant transition matrix `1/2`; its powers satisfy
  `twoPointStep ^ (n+1) = twoPointStep`, so the Gaussian bounds with `dim = 0`,
  `C_up = 1`, `C_lo = 1/4`, `c_up = c_lo = 1` hold, and `twoPointGridKernel` is an explicit
  inhabitant of `FiniteGridHeatKernel` (so the uniqueness theorem has a real target);
* `twoPointGridKernel.K 2 = twoPointStep` is the concrete instance of `eq_pow`;
* `stepSub` is the constant substochastic matrix `1/4`; the initial field `u0 = (1, 3)` evolves to
  `u1 = (1, 1)` and `u2 = (1/2, 1/2)`, with heat content `4 → 2 → 1` and `L²` energy
  `10 → 2 → 1/2`, so the monotonicity theorems are non-vacuous.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare.D7.HeatKernel

open scoped BigOperators

/-- The two-point grid. -/
abbrev TwoPoint := Fin 2

/-- The constant transition matrix `1/2` on the two-point grid. -/
noncomputable def twoPointStep : Matrix TwoPoint TwoPoint ℝ := fun _ _ => 1 / 2

/-- The trivial grid distance. -/
def twoPointDist : TwoPoint → TwoPoint → ℝ := fun _ _ => 0

/-- The constant `1/2` matrix is idempotent. -/
theorem twoPointStep_mul_self : twoPointStep * twoPointStep = twoPointStep := by
  funext i j
  simp only [Matrix.mul_apply, twoPointStep, Fin.sum_univ_two]
  norm_num

/-- Every positive power of the constant `1/2` matrix is the matrix itself. -/
theorem twoPointStep_pow_succ : ∀ n : ℕ, twoPointStep ^ (n + 1) = twoPointStep := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, twoPointStep_mul_self]

/-- The Gaussian upper bound for the powers of `twoPointStep`. -/
theorem twoPointStep_pow_upper (n : ℕ) (hn : 0 < n) (x y : TwoPoint) :
    (twoPointStep ^ n) x y ≤
      1 * (n : ℝ) ^ ((-(0 / 2 : ℝ))) * Real.exp (-(twoPointDist x y) ^ 2 / (1 * n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [twoPointStep_pow_succ k]
  simp [twoPointStep, twoPointDist, Real.rpow_zero]
  norm_num

/-- The Gaussian lower bound for the powers of `twoPointStep`. -/
theorem twoPointStep_pow_lower (n : ℕ) (hn : 0 < n) (x y : TwoPoint)
    (hxy : twoPointDist x y ≤ 1) :
    (1 / 4 : ℝ) * (n : ℝ) ^ ((-(0 / 2 : ℝ))) * Real.exp (-(twoPointDist x y) ^ 2 / (1 * n)) ≤
      (twoPointStep ^ n) x y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [twoPointStep_pow_succ k]
  simp [twoPointStep, twoPointDist, Real.rpow_zero]
  norm_num

/-- **The two-point grid heat kernel**: the constant `1/2` matrix power, with the stated Gaussian
bounds. -/
noncomputable def twoPointGridKernel :
    FiniteGridHeatKernel twoPointStep twoPointDist 0 1 1 (1 / 4) 1 :=
  gridKernel twoPointStep twoPointDist 0 1 1 (1 / 4) 1
    (fun n hn x y => twoPointStep_pow_upper n hn x y)
    (fun n hn x y hxy => twoPointStep_pow_lower n hn x y hxy)

/-- The generator of the two-point grid heat kernel. -/
theorem twoPointGridKernel_generator : twoPointGridKernel.K 1 = twoPointStep :=
  twoPointGridKernel.generator

/-- Concrete instance of `eq_pow`: the value at time `2` is the generator itself. -/
theorem twoPointGridKernel_K_two : twoPointGridKernel.K 2 = twoPointStep := by
  rw [FiniteGridHeatKernel.apply_unique twoPointGridKernel 2]
  exact twoPointStep_pow_succ 1

/-- **Concrete uniqueness**: every finite-grid heat kernel with the same generator, distance and
bounds has the kernel of `twoPointGridKernel`. -/
theorem twoPointGridKernel_unique
    (K : FiniteGridHeatKernel twoPointStep twoPointDist 0 1 1 (1 / 4) 1) :
    K.K = twoPointGridKernel.K :=
  FiniteGridHeatKernel.unique K twoPointGridKernel

/-! ## The substochastic heat flow on the two-point grid -/

/-- The constant substochastic transition matrix `1/4`. -/
noncomputable def stepSub : Matrix TwoPoint TwoPoint ℝ := fun _ _ => 1 / 4

/-- The initial temperature field `(1, 3)`. -/
noncomputable def u0 : TwoPoint → ℝ := fun i => if i = 0 then 1 else 3

/-- The field after one heat step: `(1, 1)`. -/
noncomputable def u1 : TwoPoint → ℝ := fun _ => 1

/-- The field after two heat steps: `(1/2, 1/2)`. -/
noncomputable def u2 : TwoPoint → ℝ := fun _ => 1 / 2

/-- The unit mass density. -/
noncomputable def massOne : TwoPoint → ℝ := fun _ => 1

/-- One heat step sends `u0` to `u1`. -/
theorem heatStep_stepSub_u0 : heatStep stepSub u0 = u1 := by
  funext x
  fin_cases x <;>
    simp [heatStep, stepSub, u0, u1, Fin.sum_univ_two] <;> norm_num

/-- A second heat step sends `u1` to `u2`. -/
theorem heatStep_stepSub_u1 : heatStep stepSub u1 = u2 := by
  funext x
  fin_cases x <;>
    simp [heatStep, stepSub, u1, u2] <;> norm_num

/-- The heat flow starting from `u0`. -/
noncomputable def uFlow : ℕ → TwoPoint → ℝ
  | 0 => u0
  | n + 1 => heatStep stepSub (uFlow n)

@[simp]
theorem uFlow_zero : uFlow 0 = u0 := rfl

theorem uFlow_succ (n : ℕ) : uFlow (n + 1) = heatStep stepSub (uFlow n) := rfl

theorem uFlow_one : uFlow 1 = u1 := heatStep_stepSub_u0

theorem uFlow_two : uFlow 2 = u2 := by
  show heatStep stepSub (uFlow 1) = u2
  rw [uFlow_one]
  exact heatStep_stepSub_u1

/-! ## Numeric heat-content and energy values -/

theorem heatContent_u0 : heatContent massOne u0 = 4 := by
  norm_num [heatContent, massOne, u0, Fin.sum_univ_two]

theorem heatContent_u1 : heatContent massOne u1 = 2 := by
  norm_num [heatContent, massOne, u1, Fin.sum_univ_two]

theorem heatContent_u2 : heatContent massOne u2 = 1 := by
  norm_num [heatContent, massOne, u2, Fin.sum_univ_two]

theorem l2Energy_u0 : l2Energy u0 = 10 := by
  norm_num [l2Energy, u0, Fin.sum_univ_two]

theorem l2Energy_u1 : l2Energy u1 = 2 := by
  norm_num [l2Energy, u1, Fin.sum_univ_two]

theorem l2Energy_u2 : l2Energy u2 = 1 / 2 := by
  norm_num [l2Energy, u2, Fin.sum_univ_two]

/-! ## Hypotheses of the monotonicity theorems, discharged concretely -/

theorem stepSub_nonneg : ∀ x y : TwoPoint, 0 ≤ stepSub x y := by
  intro x y
  simp [stepSub]

theorem massOne_nonneg : ∀ x : TwoPoint, 0 ≤ massOne x := by
  intro x
  simp [massOne]

theorem u0_nonneg : ∀ x : TwoPoint, 0 ≤ u0 x := by
  intro x
  fin_cases x <;> simp [u0]

theorem stepSub_col : ∀ y : TwoPoint, ∑ x, massOne x * stepSub x y ≤ massOne y := by
  intro y
  fin_cases y <;> simp [massOne, stepSub] <;> norm_num

theorem stepSub_row : ∀ x : TwoPoint, ∑ y, stepSub x y ≤ 1 := by
  intro x
  fin_cases x <;> simp [stepSub] <;> norm_num

theorem stepSub_col' : ∀ y : TwoPoint, ∑ x, stepSub x y ≤ 1 := by
  intro y
  fin_cases y <;> simp [stepSub] <;> norm_num

theorem uFlow_nonneg : ∀ n x, 0 ≤ uFlow n x := by
  intro n
  induction n with
  | zero =>
      intro x
      exact u0_nonneg x
  | succ n ih =>
      intro x
      rw [uFlow_succ, heatStep]
      exact Finset.sum_nonneg (fun y _ => mul_nonneg (stepSub_nonneg x y) (ih y))

/-! ## Concrete monotonicity -/

/-- The one-step heat-content monotonicity theorem, instantiated at `u0`. -/
theorem heatContent_oneStep_le :
    heatContent massOne (heatStep stepSub u0) ≤ heatContent massOne u0 :=
  heatContent_heatStep_le stepSub massOne u0 stepSub_nonneg massOne_nonneg u0_nonneg stepSub_col

/-- **The discrete heat content decreases** along the two-point flow. -/
theorem heatContent_uFlow_antitone : Antitone (fun n => heatContent massOne (uFlow n)) :=
  heatContent_antitone stepSub massOne uFlow stepSub_nonneg massOne_nonneg uFlow_nonneg
    stepSub_col uFlow_succ

/-- **The `L²` energy decreases** along the two-point flow. -/
theorem l2Energy_uFlow_antitone : Antitone (fun n => l2Energy (uFlow n)) :=
  l2Energy_antitone stepSub uFlow stepSub_nonneg stepSub_row stepSub_col' uFlow_succ

/-- Numeric heat-content monotonicity: `1 ≤ 4`. -/
theorem heatContent_two_le_zero : heatContent massOne (uFlow 2) ≤ heatContent massOne (uFlow 0) := by
  rw [uFlow_two, uFlow_zero, heatContent_u2, heatContent_u0]
  norm_num

/-- Numeric `L²` energy monotonicity: `1/2 ≤ 10`. -/
theorem l2Energy_two_le_zero : l2Energy (uFlow 2) ≤ l2Energy (uFlow 0) := by
  rw [uFlow_two, uFlow_zero, l2Energy_u2, l2Energy_u0]
  norm_num

end Poincare.D7.HeatKernel
