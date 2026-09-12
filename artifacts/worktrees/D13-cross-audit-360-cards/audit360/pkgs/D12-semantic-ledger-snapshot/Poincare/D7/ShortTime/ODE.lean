import Poincare.D7.ShortTime.Basic

/-!
# Poincare.D7.ShortTime.ODE

**D7 Hamilton 1982 short-time existence layer, part 2: the Lipschitz ODE interface and
uniqueness.**

The DeTurck trick converts the (uniqueness part of the) short-time existence problem for the
Ricci flow into an ODE uniqueness statement for the gauge-fixed equation. This file isolates
that statement as a reusable interface:

* `LipschitzVectorField E` — a time-dependent vector field `v : ℝ → E → E` on a normed space
  that is globally Lipschitz in the state variable at each time, with explicit Lipschitz
  constant `K : ℝ≥0`.
* `LipschitzVectorField.solution_unique` — **uniqueness of the ODE `y' = v(t, y)`** for two
  global solutions with the same initial value, proved from mathlib's
  `ODE_solution_unique_univ` (a Grönwall-type theorem).
* `RicciLipschitzInterface D` — the specialization to the Ricci flow vector field
  `G ↦ -2 Ric(G)` of a `RicciFlowData`; `RicciLipschitzInterface.solution_unique` is the
  uniqueness statement used by the DeTurck equivalence.

Nothing analytic is assumed silently: the Lipschitz hypothesis is an explicit field of the
interface, and every proof is complete (no `sorry`, `axiom`, `unsafe`, `native_decide`,
`proof_wanted`).
-/

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

/-! The analysis on matrices uses the product (sup) norm. It is definitionally the topology
that `HasDerivAt` picks up from the global matrix topology, so the derivative statements of
`Basic.lean` (elaborated with the global topology) and mathlib's ODE uniqueness theorem (which
uses the norm-induced topology) refer to the same notion of derivative. -/
attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

/-! ## The Lipschitz ODE interface -/

/-- **A time-dependent vector field that is globally Lipschitz in the state variable.** The
field `toFun t : E → E` has Lipschitz constant `K` for every `t`. This is the interface under
which the ODE `y' = v(t, y)` has at most one solution through a given initial value. -/
structure LipschitzVectorField (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The time-dependent vector field. -/
  toFun : ℝ → E → E
  /-- The global Lipschitz constant in the state variable. -/
  K : NNReal
  /-- The field is `K`-Lipschitz in the state variable at every time. -/
  lipschitz : ∀ t : ℝ, LipschitzWith K (toFun t)

namespace LipschitzVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The field is `K`-Lipschitz on the whole state space at every time. -/
theorem lipschitzOnWith (V : LipschitzVectorField E) (t : ℝ) :
    LipschitzOnWith V.K (V.toFun t) Set.univ :=
  (V.lipschitz t).lipschitzOnWith

/-- **Uniqueness of solutions of a Lipschitz ODE.** Two global solutions `f`, `g` of
`y' = v(t, y)` with the same value at time `0` are equal. This is mathlib's
`ODE_solution_unique_univ` (Grönwall) specialized to the interface. -/
theorem solution_unique (V : LipschitzVectorField E) {f g : ℝ → E}
    (hf : ∀ t : ℝ, HasDerivAt f (V.toFun t (f t)) t)
    (hg : ∀ t : ℝ, HasDerivAt g (V.toFun t (g t)) t)
    (h0 : f 0 = g 0) : f = g :=
  ODE_solution_unique_univ (s := fun _ => Set.univ)
    (fun t => V.lipschitzOnWith t)
    (fun t => ⟨hf t, trivial⟩) (fun t => ⟨hg t, trivial⟩) h0

/-- Pointwise form of `LipschitzVectorField.solution_unique`. -/
theorem solution_eq (V : LipschitzVectorField E) {f g : ℝ → E}
    (hf : ∀ t : ℝ, HasDerivAt f (V.toFun t (f t)) t)
    (hg : ∀ t : ℝ, HasDerivAt g (V.toFun t (g t)) t)
    (h0 : f 0 = g 0) (t : ℝ) : f t = g t :=
  congrFun (V.solution_unique hf hg h0) t

end LipschitzVectorField

/-! ## The Ricci flow Lipschitz interface -/

variable {n : ℕ} {D : RicciFlowData n}

/-- **The Lipschitz interface for the Ricci flow vector field** `G ↦ -2 Ric(G)` of a
`RicciFlowData`. The constant `K` is an explicit field, so the uniqueness conclusion below is
conditional on a hypothesis that is stated, not hidden. -/
structure RicciLipschitzInterface (D : RicciFlowData n) where
  /-- The Lipschitz constant of the Ricci flow vector field. -/
  K : NNReal
  /-- The Ricci flow vector field is `K`-Lipschitz in the state variable at every time. -/
  lipschitz : ∀ t : ℝ, LipschitzWith K (D.ricciVectorField t)

namespace RicciLipschitzInterface

/-- View the Ricci Lipschitz interface as a `LipschitzVectorField` on matrices. -/
def toLipschitzVectorField (L : RicciLipschitzInterface D) :
    LipschitzVectorField (Matrix (Fin n) (Fin n) ℝ) where
  toFun := D.ricciVectorField
  K := L.K
  lipschitz := L.lipschitz

/-- **Uniqueness for the Ricci flow ODE** under the Lipschitz interface: two global solutions
of `G' = -2 Ric(G)` with the same initial metric agree for all times. -/
theorem solution_unique (L : RicciLipschitzInterface D) {f g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ t : ℝ, HasDerivAt f ((-2 : ℝ) • D.ricci (f t)) t)
    (hg : ∀ t : ℝ, HasDerivAt g ((-2 : ℝ) • D.ricci (g t)) t)
    (h0 : f 0 = g 0) : f = g := by
  refine ODE_solution_unique_univ (v := fun _ G => (-2 : ℝ) • D.ricci G)
    (s := fun _ => Set.univ) (K := L.K)
    (fun t => (L.lipschitz t).lipschitzOnWith) ?_ ?_ h0
  · intro t
    exact ⟨hf t, trivial⟩
  · intro t
    exact ⟨hg t, trivial⟩

/-- Pointwise form of `RicciLipschitzInterface.solution_unique`. -/
theorem solution_eq (L : RicciLipschitzInterface D) {f g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ t : ℝ, HasDerivAt f ((-2 : ℝ) • D.ricci (f t)) t)
    (hg : ∀ t : ℝ, HasDerivAt g ((-2 : ℝ) • D.ricci (g t)) t)
    (h0 : f 0 = g 0) (t : ℝ) : f t = g t :=
  congrFun (L.solution_unique hf hg h0) t

end RicciLipschitzInterface

end

end ShortTime
end D7
end Poincare
