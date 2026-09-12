import Poincare.Longrun.CurvatureODE.State

/-!
# Poincare.Longrun.CurvatureODE.Evolution

**Stage 2 / curvature-ODE cluster: the evolution relation.**

This module is part of the `D2-ricci-ode-cluster` task. It defines the finite-dimensional
**reaction field** and the **evolution relation** for the finite state of
`Poincare.Longrun.CurvatureODE.State`.

## The model

Hamilton's ODE for the curvature operator under Ricci flow is
`∂ₜ Rm = ΔRm + Rm² + Rm#` (Laplacian + quadratic reaction). This cluster isolates the
**reaction part** in a finite diagonal model: for a finite state `lam : ι → ℝ`,

`d lamᵢ/dt = aᵢ * lamᵢ² + gᵢ(lam)`, with `aᵢ ≥ 0` and `gᵢ(lam) ≥ 0`.

* `ReactionField ι` packages `a`, `g` and the two nonnegativity hypotheses.
* `ReactionField.hamilton` is the canonical Ricci-flow-inspired field
  `lamᵢ' = lamᵢ² + ∑ⱼ lamⱼ²`, which is the diagonal special case of a quadratic reaction
  with nonnegative coefficients (the exact `Rm#` coefficients depend on the Lie-algebra
  structure and are **not** formalized here).
* `EvolutionRelation F T traj` is the continuous-time relation: on `[0,T]`, each component
  is continuous and has right derivative `Fᵢ(traj t)`.
* `eulerStep` / `DiscreteEvolution` are the explicit-Euler finite analogue, which needs no
  analysis and is used for the discrete invariant/monotonicity theorems.

## Honest boundary

The field is a **model**, not Hamilton's operator: the spatial Laplacian is dropped and the
`Rm#` coefficients are replaced by an abstract nonnegative reaction. The exact missing bridge
to tensor Ricci flow is the explicit interface in `Poincare.Longrun.CurvatureODE.Bridge`.
All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

open Set

namespace Poincare
namespace Longrun
namespace CurvatureODE

universe w

variable {ι : Type w} [Fintype ι]

/-- **Finite reaction field.** A diagonal quadratic reaction `Fᵢ(lam) = aᵢ * lamᵢ² + gᵢ(lam)`
with `aᵢ ≥ 0` and `gᵢ(lam) ≥ 0` for every state. The nonnegativity is what makes the
nonnegative orthant invariant and the scalar functional monotone. -/
structure ReactionField (ι : Type w) [Fintype ι] where
  /-- The quadratic self-coupling coefficients. -/
  a : ι → ℝ
  /-- The remaining nonnegative reaction terms. -/
  g : (ι → ℝ) → ι → ℝ
  /-- The self-coupling coefficients are nonnegative. -/
  a_nonneg : ∀ i, 0 ≤ a i
  /-- The remaining reaction terms are nonnegative in every state. -/
  g_nonneg : ∀ lam i, 0 ≤ g lam i

namespace ReactionField

/-- Evaluation of the reaction field at a state. -/
def eval (F : ReactionField ι) (lam : ι → ℝ) (i : ι) : ℝ :=
  F.a i * (lam i) ^ 2 + F.g lam i

/-- **The reaction is nonnegative in every state.** This is the sign condition behind both the
invariant-region and the monotonicity theorems; no region restriction is needed. -/
theorem eval_nonneg (F : ReactionField ι) (lam : ι → ℝ) (i : ι) : 0 ≤ F.eval lam i :=
  add_nonneg (mul_nonneg (F.a_nonneg i) (sq_nonneg (lam i))) (F.g_nonneg lam i)

/-- **The canonical Ricci-flow-inspired reaction field**
`lamᵢ' = lamᵢ² + ∑ⱼ lamⱼ²`. It is the diagonal model of `∂ₜ Rm = Rm² + Rm#` with all
quadratic coefficients set to `1`; the honest approximation boundary is in the module
docstring and in `Poincare.Longrun.CurvatureODE.Bridge`. -/
def hamilton : ReactionField ι where
  a := fun _ => 1
  g := fun lam _ => ∑ j : ι, (lam j) ^ 2
  a_nonneg := by intro i; norm_num
  g_nonneg := by intro lam i; positivity

/-- Evaluation of the canonical field: `lamᵢ² + ∑ⱼ lamⱼ²`. -/
@[simp]
theorem hamilton_eval (lam : ι → ℝ) (i : ι) :
    (hamilton : ReactionField ι).eval lam i = (lam i) ^ 2 + ∑ j : ι, (lam j) ^ 2 := by
  simp [eval, hamilton]

/-- The canonical field evaluated at the zero state is zero. -/
@[simp]
theorem hamilton_eval_zero (i : ι) :
    (hamilton : ReactionField ι).eval (fun _ => 0) i = 0 := by
  simp [eval, hamilton]

end ReactionField

/-! ## The continuous-time evolution relation -/

/-- **Continuous-time evolution relation.** On the time interval `[0,T]`, every component of
the trajectory is continuous and has right derivative given by the reaction field. -/
structure EvolutionRelation (F : ReactionField ι) (T : ℝ) (traj : ℝ → ι → ℝ) : Prop where
  /-- Componentwise continuity on `[0,T]`. -/
  continuous : ∀ i, ContinuousOn (fun t => traj t i) (Icc 0 T)
  /-- Componentwise right derivative `trajᵢ' = Fᵢ(traj)`. -/
  hasDeriv : ∀ i, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => traj s i) (F.eval (traj t) i) (Ici t) t

/-- **The zero trajectory solves the canonical reaction ODE.** This witness shows the
evolution relation is satisfiable (non-vacuous), without asserting anything geometric. -/
theorem zero_evolutionRelation (T : ℝ) :
    EvolutionRelation (ReactionField.hamilton : ReactionField ι) T (fun _ _ => 0) where
  continuous := by intro i; exact continuousOn_const
  hasDeriv := by
    intro i t _
    simpa using hasDerivWithinAt_const (c := (0 : ℝ)) (s := Ici t) (x := t)

/-! ## The explicit-Euler discrete analogue -/

/-- One explicit-Euler step of the reaction ODE. -/
def eulerStep (F : ReactionField ι) (h : ℝ) (lam : ι → ℝ) : ι → ℝ :=
  fun i => lam i + h * F.eval lam i

/-- **Discrete evolution relation** (explicit Euler): `traj (n+1) = eulerStep F h (traj n)`. -/
structure DiscreteEvolution (F : ReactionField ι) (h : ℝ) (traj : ℕ → ι → ℝ) : Prop where
  /-- The one-step recurrence. -/
  step : ∀ n i, traj (n + 1) i = traj n i + h * F.eval (traj n) i

/-- The zero trajectory solves the discrete canonical recurrence for every step size. -/
theorem zero_discreteEvolution (h : ℝ) :
    DiscreteEvolution (ReactionField.hamilton : ReactionField ι) h (fun _ _ => 0) where
  step := by intro n i; simp

end CurvatureODE
end Longrun
end Poincare
