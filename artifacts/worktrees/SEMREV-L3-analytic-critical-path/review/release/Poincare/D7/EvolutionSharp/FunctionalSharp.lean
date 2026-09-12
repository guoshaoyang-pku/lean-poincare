/-
# Poincare.D7.EvolutionSharp.FunctionalSharp

**D7 evolution sharp restatement: the finite Perelman functional strict step.**

This module consumes the D4 adversarial audit (`D4-counterexample-audit`, finding #5) and
restates the promoted strict-decrease theorem `Poincare.Longrun.Evolution.perelmanF_step_lt`
under the **weakest curvature hypothesis the audit proved sufficient**:

* promoted: `∀ i, 1 < c i`;
* sharpened: `∀ i, 1 ≤ c i`.

The proof is the promoted `Finset.sum_lt_sum` argument, with the single-component strict
inequality supplied by the sharpened one-variable theorem
`Poincare.D7.EvolutionSharp.gibbsTerm_step_lt_of_one_le` and every other component bounded
by the promoted non-strict inequality `gibbsTerm_step_le` (which already assumes only
`1 ≤ c`). The hypotheses `0 < h` and `0 < F.eval (traj n) i` are retained: the audit's
`strict_step_needs_pos_step` and `strict_step_needs_pos_reaction` show both are necessary,
and the D2 `ReactionField` sign condition `F.eval ≥ 0` is built into the structure.

## Analytic boundary (explicit)

The conclusion is a strict decrease of the **finite** functional along the **finite**
explicit-Euler recurrence, not of Perelman's `F`-functional along a Ricci flow. The
curvature data `c` is abstract, the step `h` is an explicit real parameter, and the
strictness is produced by a single strictly positive reaction component. No `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.GibbsSharp

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-- **Sharpened strict decrease (discrete time).** The hypothesis `∀ i, 1 < c i` of the
promoted `perelmanF_step_lt` is overstrong: `∀ i, 1 ≤ c i` suffices. The strict decrease is
driven by the single component `i` with `0 < F.eval (traj n) i`; all other components are
bounded by the promoted non-strict one-step inequality. -/
theorem perelmanF_step_lt_of_one_le (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) := by
  unfold perelmanF
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [ev.step n j]
    exact gibbsTerm_step_le (hc j) (mul_nonneg (le_of_lt hh) (F.eval_nonneg (traj n) j))
  · rw [ev.step n i]
    exact gibbsTerm_step_lt_of_one_le (hc i) (mul_pos hh hi)

/-! ## Axiom audit -/

#print axioms perelmanF_step_lt_of_one_le

end EvolutionSharp
end D7
end Poincare
