/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11 builder

# D11 — The discrete tensor maximum principle (explicit Euler scheme)

The **tensor maximum principle** of Hamilton controls the evolution of a symmetric 2-tensor
`S` under a reaction-diffusion equation `∂_t S = ΔS + Q(S)`: if `S ≥ 0` (positive semidefinite)
at time `0` and the *reaction* `Q` maps the PSD cone into itself (or, in the sharp form, maps
the boundary of the cone into the cone), then `S ≥ 0` for all later times.

This file isolates the part of the argument that is pure finite-dimensional convexity, namely
the invariance of the PSD cone under the **explicit Euler step**

`eulerStep Q ε A = A + ε • Q A`.

The discrete statement is unconditional:

* `eulerStep_posSemidef` — if `Q` preserves the cone then one Euler step does;
* `eulerIterate_posSemidef` — hence every Euler iterate of a PSD initial matrix is PSD;
* `eulerStep_mono` — in the Loewner order the step moves `A` upwards, `A ≤ A + ε • Q A`.

The hypotheses are not vacuous: `Q = 0`, `Q = id`, `Q A = c • A` (`c ≥ 0`), `Q A = A * A` and
finite sums of such are all positivity preserving (`PositivityPreserving.zero`, `.id`,
`.const_smul`, `.sq`, `.add`, `.comp`), while `Q A = -A` is not
(`not_positivityPreserving_neg`).

Finally, `boundary_condition_strictly_weaker` shows that Hamilton's *boundary* form of the
condition (`BoundaryPositivityPreserving`, checked only at PSD matrices with a non-trivial
kernel) does **not** imply the global condition.  This is why the explicit Euler scheme above
is only a discrete shadow of the tensor maximum principle: the continuous flow cannot jump
from the interior of the cone to a point where the reaction is negative, and the sharp theorem
requires the parabolic maximum principle at the first touching time (see `Flow.lean`).
-/

import Poincare.D11.MaximumPrincipleTensor.Basic

open scoped MatrixOrder
open Matrix

namespace Poincare.D11.MaximumPrincipleTensor

variable {n : ℕ}

/-! ## The Euler step -/

/-- One step of the explicit Euler scheme for the reaction ODE `S' = Q(S)`. -/
def eulerStep (Q : Mat n → Mat n) (ε : ℝ) (A : Mat n) : Mat n := A + ε • Q A

/-- The `k`-th Euler iterate of `A` with step size `ε`. -/
def eulerIterate (Q : Mat n → Mat n) (ε : ℝ) (k : ℕ) (A : Mat n) : Mat n :=
  (eulerStep Q ε)^[k] A

@[simp]
theorem eulerIterate_zero (Q : Mat n → Mat n) (ε : ℝ) (A : Mat n) :
    eulerIterate Q ε 0 A = A := rfl

@[simp]
theorem eulerIterate_succ (Q : Mat n → Mat n) (ε : ℝ) (k : ℕ) (A : Mat n) :
    eulerIterate Q ε (k + 1) A = eulerStep Q ε (eulerIterate Q ε k A) :=
  Function.iterate_succ_apply' _ _ _

/-- **Discrete tensor maximum principle (one step).**  A positivity-preserving reaction keeps
the PSD cone invariant under the explicit Euler step with nonnegative step size. -/
theorem eulerStep_posSemidef {Q : Mat n → Mat n} (hQ : PositivityPreserving Q)
    {ε : ℝ} (hε : 0 ≤ ε) {A : Mat n} (hA : A.PosSemidef) :
    (eulerStep Q ε A).PosSemidef :=
  hA.add ((hQ A hA).smul hε)

/-- **Discrete tensor maximum principle (all iterates).**  Every Euler iterate of a PSD
initial matrix is PSD. -/
theorem eulerIterate_posSemidef {Q : Mat n → Mat n} (hQ : PositivityPreserving Q)
    {ε : ℝ} (hε : 0 ≤ ε) {A : Mat n} (hA : A.PosSemidef) (k : ℕ) :
    (eulerIterate Q ε k A).PosSemidef := by
  induction k with
  | zero => simpa using hA
  | succ k ih => simpa using eulerStep_posSemidef hQ hε ih

/-- The Euler step moves upwards in the Loewner order: `A ≤ eulerStep Q ε A` whenever the
reaction at `A` is nonnegative and `ε ≥ 0`. -/
theorem eulerStep_mono {Q : Mat n → Mat n} {A : Mat n} (hQ : (Q A).PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) : A ≤ eulerStep Q ε A := by
  rw [le_iff_sub_posSemidef]
  have h : eulerStep Q ε A - A = ε • Q A := by
    simp [eulerStep]
  rw [h]
  exact hQ.smul hε

/-! ## Closure properties and examples of positivity-preserving reactions -/

theorem PositivityPreserving.zero : PositivityPreserving (fun _ : Mat n => 0) :=
  fun _ _ => Matrix.PosSemidef.zero

theorem PositivityPreserving.id : PositivityPreserving (fun A : Mat n => A) := fun _ hA => hA

theorem PositivityPreserving.const_smul (c : ℝ) (hc : 0 ≤ c) :
    PositivityPreserving (fun A : Mat n => c • A) := fun _ hA => hA.smul hc

theorem PositivityPreserving.add {Q₁ Q₂ : Mat n → Mat n}
    (h₁ : PositivityPreserving Q₁) (h₂ : PositivityPreserving Q₂) :
    PositivityPreserving (fun A => Q₁ A + Q₂ A) := fun A hA => (h₁ A hA).add (h₂ A hA)

theorem PositivityPreserving.comp {Q₁ Q₂ : Mat n → Mat n}
    (h₁ : PositivityPreserving Q₁) (h₂ : PositivityPreserving Q₂) :
    PositivityPreserving (fun A => Q₁ (Q₂ A)) := fun A hA => h₁ _ (h₂ A hA)

/-- The quadratic reaction `Q A = A * A` preserves the PSD cone: the square of a Hermitian
matrix is PSD (`Matrix.posSemidef_conjTranspose_mul_self` together with `Aᴴ = A`). -/
theorem PositivityPreserving.sq : PositivityPreserving (fun A : Mat n => A * A) := by
  intro A hA
  have h : A * A = Aᴴ * A := by rw [hA.1.eq]
  show (A * A).PosSemidef
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self A

/-- A concrete positivity-preserving reaction combining all the closure rules: the Riccati-type
nonlinearity `Q A = c • A + A * A` with `c ≥ 0`. -/
theorem positivityPreserving_const_smul_add_sq (c : ℝ) (hc : 0 ≤ c) :
    PositivityPreserving (fun A : Mat n => c • A + A * A) :=
  (PositivityPreserving.const_smul c hc).add PositivityPreserving.sq

/-- Consistency check for the linear reaction `Q A = c • A` (`c ≥ 0`): the explicit solution
`S t = exp (c t) • S 0` of `S' = c S` is PSD for all `t ≥ 0`, as the maximum principle
predicts. -/
theorem exp_smul_posSemidef {c : ℝ} (_hc : 0 ≤ c) {A : Mat n} (hA : A.PosSemidef)
    {t : ℝ} (_ht : 0 ≤ t) : (Real.exp (c * t) • A).PosSemidef :=
  hA.smul (Real.exp_nonneg _)

/-! ## Sharpness: `Q A = -A` does not preserve the cone -/

/-- The reaction `Q A = -A` is *not* positivity preserving: the identity matrix is PSD but its
negative is not (its diagonal entry is `-1`). -/
theorem not_positivityPreserving_neg :
    ¬ PositivityPreserving (fun A : Mat 1 => -A) := by
  intro h
  have h1 : (-1 : Mat 1).PosSemidef := h 1 Matrix.PosSemidef.one
  have h2 := h1.diag_nonneg (i := 0)
  simp at h2
  linarith

/-! ## The boundary condition is strictly weaker

Hamilton's sharp hypothesis is checked only on the *boundary* of the PSD cone.  The next
example shows that this is genuinely weaker than global positivity preservation: for `1 × 1`
matrices the only PSD matrix with a null vector is `0`, so the boundary condition constrains
only `Q 0`, while `Q A` may be negative at the interior point `A = 1`. -/

/-- The reaction `Q A = -1` unless `A = 0`, where `Q 0 = 0`. -/
noncomputable def boundaryOnlyReaction : Mat 1 → Mat 1 := fun A => if A 0 0 = 0 then 0 else -1

theorem boundaryOnlyReaction_boundary :
    BoundaryPositivityPreserving boundaryOnlyReaction := by
  intro A hA hnull
  by_cases h : A 0 0 = 0
  · simpa [boundaryOnlyReaction, h] using Matrix.PosSemidef.zero
  · exfalso
    obtain ⟨x, hxne, hAx⟩ := hnull
    have hx0 : x 0 ≠ 0 := fun hx0 =>
      hxne (funext fun i => by fin_cases i; simpa using hx0)
    have h0 : (A *ᵥ x) 0 = A 0 0 * x 0 := by simp [mulVec, dotProduct]
    have : A 0 0 * x 0 = 0 := by rw [← h0, hAx]; rfl
    exact h (mul_eq_zero.mp this |>.resolve_right hx0)

theorem boundaryOnlyReaction_not_positivityPreserving :
    ¬ PositivityPreserving boundaryOnlyReaction := by
  intro h
  have h1 : (boundaryOnlyReaction 1).PosSemidef := h 1 Matrix.PosSemidef.one
  have h2 : boundaryOnlyReaction 1 = (-1 : Mat 1) := by simp [boundaryOnlyReaction]
  rw [h2] at h1
  have h3 := h1.diag_nonneg (i := 0)
  simp at h3
  linarith

/-- **Hamilton's boundary condition does not imply global positivity preservation.**  Hence the
Euler scheme with a global hypothesis is strictly weaker than the continuous tensor maximum
principle; the continuous statement needs the parabolic maximum principle at the first
touching time of the cone (formalised conditionally in `Flow.lean`). -/
theorem boundary_condition_strictly_weaker :
    ∃ Q : Mat 1 → Mat 1, BoundaryPositivityPreserving Q ∧ ¬ PositivityPreserving Q :=
  ⟨boundaryOnlyReaction, boundaryOnlyReaction_boundary,
    boundaryOnlyReaction_not_positivityPreserving⟩

end Poincare.D11.MaximumPrincipleTensor
