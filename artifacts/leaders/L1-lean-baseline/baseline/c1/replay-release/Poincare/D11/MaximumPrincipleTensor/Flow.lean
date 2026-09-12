/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11 builder

# D11 — The tensor maximum principle: the continuum interface

The full tensor maximum principle (Hamilton) concerns a symmetric 2-tensor `S` on a manifold
evolving by `∂_t S = ΔS + Q(S)`; its analytic core is that the positive-semidefinite cone is
forward invariant along the flow.  Solving the parabolic equation and running the maximum
principle at the first touching time of the cone is a substantial analytic development (the
scalar version on a bounded domain is in the sibling task `D10-maximum-principle-rn`), so this
file separates the two layers explicitly:

* `ConeInvariantUnderReaction Q` — a **statement-only `Prop`** naming exactly the analytic
  content of the tensor maximum principle for the reaction ODE `S' = Q(S)`.  No proof is
  claimed for it in general.
* `tensor_maximum_principle_ode` — the conditional tensor maximum principle: from the
  statement-only `Prop` the PSD preservation follows.
* `quadForm_monotone_of_reaction_posSemidef` — **unconditional**: if the reaction is PSD along
  a flow, every quadratic form `xᵀ S(t) x` is nondecreasing in `t`.  This is the estimate that
  the maximum-principle proof consumes.
* `coneInvariantUnderReaction_oneByOne` — **unconditional**: in dimension `1` the cone
  invariance is a theorem, because the tensor ODE reduces to the scalar reaction ODE handled by
  `ScalarODE.scalar_forward_invariance` (it is here that the two-sided hypothesis `(-δ, ∞)` on
  the reaction enters genuinely).

Hamilton's sharp hypothesis on the reaction is the *null-eigenvector condition*
(`BoundaryPositivityPreserving`, see `Basic.lean`): `Q A` is PSD whenever `A` is PSD and has a
non-trivial kernel.  `Euler.lean` shows that the condition is strictly weaker than global
positivity preservation, and that a violation of it at a PSD matrix with null vector `x` makes
the *Euler step* leave the cone; the corresponding statement for the continuous flow is the
unformalised analytic core named by `ConeInvariantUnderReaction`.
-/

import Poincare.D11.MaximumPrincipleTensor.ScalarODE

open scoped MatrixOrder
open Matrix Set

namespace Poincare.D11.MaximumPrincipleTensor

variable {m : ℕ}

/-- **The conclusion of the tensor maximum principle** for the reaction ODE `S' = Q(S)`:
the positive-semidefinite cone is forward invariant.

This is a *statement-only* `Prop`: it names the analytic content of Hamilton's tensor maximum
principle (forward viability of the PSD cone, proved from the null-eigenvector condition via
the parabolic maximum principle at the first touching time).  It is not proved here; it is used
as an explicit hypothesis in `tensor_maximum_principle_ode`. -/
def ConeInvariantUnderReaction (Q : Mat m → Mat m) : Prop :=
  ∀ S : ℝ → Mat m, (∀ t, 0 ≤ t → HasDerivAt S (Q (S t)) t) →
    (S 0).PosSemidef → ∀ t, 0 ≤ t → (S t).PosSemidef

/-- **Conditional tensor maximum principle (ODE form).**  Taking the cone-invariance statement
as an explicit hypothesis, a solution of `S' = Q(S)` with PSD initial value stays PSD. -/
theorem tensor_maximum_principle_ode {Q : Mat m → Mat m}
    (h : ConeInvariantUnderReaction Q) {S : ℝ → Mat m}
    (hflow : ∀ t, 0 ≤ t → HasDerivAt S (Q (S t)) t) (hS0 : (S 0).PosSemidef) :
    ∀ t, 0 ≤ t → (S t).PosSemidef :=
  h S hflow hS0

/-- If the reaction is PSD along a flow, every quadratic form of the flow is nondecreasing.
This is the estimate the maximum principle consumes: differentiating `t ↦ xᵀ S(t) x` gives
`xᵀ Q(S t) x ≥ 0` (`hasDerivAt_quadForm`), so the scalar function is monotone
(`monotoneOn_of_deriv_nonneg`). -/
theorem quadForm_monotone_of_reaction_posSemidef {S : ℝ → Mat m} {Q : Mat m → Mat m} {T : ℝ}
    (hS : ∀ t ∈ Icc 0 T, HasDerivAt S (Q (S t)) t)
    (hreact : ∀ t ∈ Icc 0 T, (Q (S t)).PosSemidef) (x : Fin m → ℝ) :
    MonotoneOn (fun t => quadForm (S t) x) (Icc 0 T) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 T) ?_ ?_ ?_
  · intro t ht
    exact (hasDerivAt_quadForm (hS t ht) x).continuousAt.continuousWithinAt
  · intro t ht
    exact ((hasDerivAt_quadForm (hS t (interior_subset ht)) x).differentiableAt).differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have htIT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    rw [(hasDerivAt_quadForm (hS t htIT) x).deriv]
    exact quadForm_nonneg (hreact t htIT) x

/-- Every `1 × 1` matrix is determined by its entry. -/
theorem mat_one_eq_oneByOne (A : Mat 1) : A = oneByOne (A 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

/-- **The tensor maximum principle in dimension `1` (unconditional).**  If the reaction on
`1 × 1` matrices is induced by a scalar reaction `q` which is nonnegative on a two-sided
neighbourhood `(-δ, ∞)` of `0`, then the PSD cone (`a ≥ 0`) is forward invariant.  The proof is
the reduction of the `1 × 1` tensor ODE to the scalar ODE `y' = q(y)` plus
`scalar_forward_invariance`; it shows that the statement-only `Prop`
`ConeInvariantUnderReaction` is inhabited in a nontrivial case. -/
theorem coneInvariantUnderReaction_oneByOne {q : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ v, -δ < v → 0 ≤ q v) :
    ConeInvariantUnderReaction (fun A : Mat 1 => oneByOne (q (A 0 0))) := by
  intro S hflow hS0 t ht
  have hScal : ∀ s, 0 ≤ s → HasDerivAt (fun u : ℝ => S u 0 0) (q (S s 0 0)) s := by
    intro s hs
    have h1 : HasDerivAt (fun u : ℝ => S u 0) ((fun A : Mat 1 => oneByOne (q (A 0 0))) (S s) 0) s :=
      (hasDerivAt_pi.mp (hflow s hs)) 0
    exact (hasDerivAt_pi.mp h1) 0
  have hy0 : 0 ≤ S 0 0 0 := hS0.diag_nonneg (i := 0)
  have hnonneg := scalar_forward_invariance (q := q) (y := fun u => S u 0 0) hδ ht
    (fun s hs => hScal s hs.1) hq hy0
  rw [mat_one_eq_oneByOne (S t)]
  exact oneByOne_posSemidef_iff.mpr (hnonneg t ⟨ht, le_rfl⟩)

end Poincare.D11.MaximumPrincipleTensor
