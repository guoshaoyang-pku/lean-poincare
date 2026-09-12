/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.Convergence

/-!
# Poincare.D7.Limit.Blocked

**D7 discrete-to-continuous limit, part 6: the state-only unconditional theorem
and its exact missing dependencies.**

The checked content of this layer reduces mesh convergence to two explicit
inputs: a refining mesh (`IsRefiningMesh`) and vanishing of the discretization
error (`HasVanishingError`).  The second input is the one that cannot be
discharged at the pinned mathlib revision.  This file records:

* `HeatMeshConvergenceTheorem` — the unconditional convergence statement, as a
  `Prop` (imported from `Poincare.D7.Limit.Convergence`);
* `ContinuousHeatMaximumPrincipleConjecture` — the unconditional D2 continuous
  interface, as a `Prop`;
* the named blockers, with the two headline gaps being **compactness**
  (no Arzelà–Ascoli for the family of discrete solutions; `#check_failure`
  in `Poincare.D7.Limit.Probe` records that `ArzelaAscoli` is absent) and
  **parabolic regularity** (no Schauder estimates and no uniform `C²/C⁴`
  a priori bounds, without which the Taylor-remainder truncation constant
  cannot be shown to vanish);
* the exact missing mathlib dependencies.

Nothing here is an axiom: the statements are `def … : Prop`, and the only
"proof" content is the consistency check that they are propositions and that
the blocker lists are nonempty.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

namespace Poincare.D7.Limit

/-! ## The state-only statements -/

/-- **The unconditional continuous maximum principle (statement only).**  For
every slab solution `u` satisfying the D2 `ContinuousHeatHypotheses`, the
conclusion of the D2 `ContinuousHeatMaximumPrincipleInterface` holds.  This is
the interface that D2 recorded as statement-only; the checked conditional
recovery is
`continuousHeatMaximumPrincipleInterface_of_meshConvergence`. -/
def ContinuousHeatMaximumPrincipleConjecture (a b T : ℝ) : Prop :=
  ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
    ContinuousHeatMaximumPrincipleInterface u a b T

/-- The state-only continuous interface is a `Prop`. -/
theorem continuousHeatMaximumPrincipleConjecture_isProp (a b T : ℝ) :
    ∀ h : ContinuousHeatMaximumPrincipleConjecture a b T, h = h := fun _ => rfl

/-- **The continuous interface from a convergent nonpositive mesh sequence.**
If every slab solution admits a convergent mesh sequence whose discrete values
are nonpositive, then the state-only continuous maximum principle follows.
This isolates the missing input: the construction of such a mesh sequence with
vanishing discretization error. -/
theorem continuousHeatMaximumPrincipleConjecture_of_meshConvergence
    (a b T : ℝ)
    (hmesh : ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
      ∃ S : HeatMeshSequence u a b T,
        HeatMeshConvergence S ∧
        (∀ n k i, i ≤ S.N n + 1 → (S.grid n).v k i ≤ 0) ∧
        (∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∃ (i k : ℕ → ℕ),
          (∀ n, i n ≤ S.N n + 1) ∧
          Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) ∧
          Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t))) :
    ContinuousHeatMaximumPrincipleConjecture a b T := by
  intro u hu
  obtain ⟨S, hconv, hdiscrete, hdense⟩ := hmesh u hu
  exact continuousHeatMaximumPrincipleInterface_of_meshConvergence S hconv hdiscrete hdense

/-! ## Named blockers -/

/-- A named blocker: a reason why the unconditional convergence theorem is not
available at the pinned mathlib revision. -/
structure Blocker where
  /-- The identifier of the blocker. -/
  name : String
  /-- The content of the blocker. -/
  reason : String

/-- The named blockers of `HeatMeshConvergenceTheorem` and
`ContinuousHeatMaximumPrincipleConjecture`. -/
def blockers : List Blocker :=
  [ ⟨"B-D7-LIMIT-COMPACTNESS",
      "no compactness theorem for the family of discrete solutions: mathlib has `Equicontinuous` \
and `IsCompact` but no Arzelà-Ascoli theorem (`#check_failure @ArzelaAscoli` in \
Poincare.D7.Limit.Probe), no sequential compactness of bounded families of functions on the slab, \
and no closedness of the limit set under the discrete heat operator; the compactness step needed to \
extract a convergent subsequence and identify its limit with a heat solution is absent"⟩,
    ⟨"B-D7-LIMIT-REGULARITY",
      "no parabolic regularity theory: no Schauder estimates, no Hölder spaces C^{k,α}, no uniform \
C²/C⁴ a priori bounds on the slab solution; without a uniform bound on |u_tt| and |u_xxxx| the \
Taylor-remainder constant `truncationConstant Δt α A B h` cannot be shown to tend to 0"⟩,
    ⟨"B-D7-LIMIT-CONSISTENCY",
      "no uniform a priori bounds turning the local Taylor expansion into the truncation estimate: \
mathlib has `taylor_mean_remainder` and `HasFTaylorSeriesUpTo`, but no theorem bounds the Lagrange \
remainder `Δt²/2 * u_tt - α h⁴/12 * u_xxxx` uniformly on the slab; the local estimate is recorded \
as the explicit hypothesis `truncationConstant` in the consistency certificate, not as a theorem"⟩,
    ⟨"B-D7-LIMIT-WELLPOSED",
      "no existence or uniqueness theory for the continuous heat equation: the D2 \
`ContinuousHeatHypotheses` interface is statement-only, so the continuous slab solution `u` is an \
input of every theorem in this layer, never a constructed object"⟩,
    ⟨"B-D7-LIMIT-MESH-DENSITY",
      "no construction of refining mesh sequences with the density property used by \
`IsRefiningMesh`; for uniform meshes this is provable from `Nat.floor` and `h → 0`, but no such \
sequence is constructed here"⟩]

theorem blockers_length : blockers.length = 5 := rfl

theorem blockers_ne_nil : blockers ≠ [] := by simp [blockers]

/-- The **missing mathlib dependencies** of the unconditional convergence
theorem, one entry per analytic input. -/
def MissingMathlibDependencies : List String :=
  [ "Arzelà-Ascoli compactness for equicontinuous families of functions on a compact metric space \
(mathlib has `Equicontinuous` and `IsCompact` but no Arzelà-Ascoli theorem)",
    "sequential compactness of bounded families of functions on the slab and closedness of the \
limit under the discrete heat operator",
    "parabolic regularity: Schauder estimates, Hölder spaces C^{k,α}, and smoothness of weak \
solutions of the heat equation",
    "uniform C²/C⁴ a priori bounds on the slab solution (needed for the Taylor remainder of the \
truncation error)",
    "existence and uniqueness of the continuous heat equation solution with prescribed Dirichlet \
and initial data (the D2 `ContinuousHeatHypotheses` is statement-only)",
    "Taylor's theorem with an explicit Lagrange remainder in the form consumed by the truncation \
estimate, together with the uniform derivative bounds that make the remainder small \
(`taylor_mean_remainder` is present; the uniform estimate is not)",
    "a constructive refining mesh sequence with the density property (provable for uniform meshes, \
not formalized here)" ]

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 7 := rfl

/-- The **present mathlib dependencies** reused by this layer. -/
def PresentMathlibDependencies : List String :=
  [ "continuous functions, `ContinuousOn` and `ContinuousWithinAt`",
    "filter limits: `Tendsto`, `le_of_tendsto'`, `Metric.tendsto_atTop`",
    "the D2 finite-grid heat evolution and its maximum principle \
(`Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le`)",
    "the D2 continuous heat interface `Poincare.Longrun.PDE.ContinuousHeatHypotheses`",
    "the D4 statement-only `Poincare.Longrun.Evolution.FiniteMeshConvergence` predicate",
    "finite sums and extrema: `Finset.sum`, `Finset.sup'`" ]

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 6 := rfl

end Poincare.D7.Limit
