/-
# Poincare.D7.EvolutionSharp.SharpOnlyConsumers

**D7 evolution sharp restatement: consumers that require the sharp hypothesis.**

The A1 upstream restatement (`Poincare.Longrun.Evolution.gibbsTerm_strictAnti`,
`gibbsTerm_step_lt`, `perelmanF_step_lt` now assume `1 ≤ c`) gives the promoted theorems a
kernel-checked downstream consumer that the *old* `1 < c` statements could not serve: the
threshold configuration `c ≡ 1`. For `c = 1` the derivative of the Gibbs term vanishes at
the isolated flat spot `x = 1`, so the strict statements are not instances of the old
`1 < c` theorems; they are genuine consequences of the sharpened hypothesis.

This module records:

* `gibbsTerm_strictAnti_at_threshold_one` — the promoted restated theorem applied at
  `c = 1` (an application that does not typecheck against the old statement);
* `perelmanF_step_lt_at_threshold_one` — the finite Perelman functional strictly decreases
  along a non-static explicit-Euler step when every `c i = 1`; a `1 < c i` hypothesis is
  unavailable at this configuration;
* `perelmanF_step_lt_sharp_of_lt` — backward compatibility: every old-format application is
  recovered from the restated theorem.

## Analytic boundary (explicit)

These are statements about the finite D4 model, not about Perelman's functional along a
Ricci flow. The driver is deliberately small: it is a consumer of the restated promoted
theorems, not a new mathematical development. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.Implications

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

universe w

variable {ι : Type w} [Fintype ι]

/-! ## The flat-spot consumer -/

/-- **The restated promoted theorem at the flat spot `c = 1`.** The old promoted statement
required `1 < c` and therefore did not apply here; the sharpened hypothesis `1 ≤ c` does. -/
theorem gibbsTerm_strictAnti_at_threshold_one : StrictAnti (gibbsTerm 1) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti 1 le_rfl

/-- **Sharp-only downstream consumer.** If every component of the curvature data equals `1`
(the threshold excluded by the old statements), the step size is positive and some reaction
component is strictly positive, then the finite Perelman functional strictly decreases in
one explicit-Euler step. This application is impossible against the old `∀ i, 1 < c i`
statement. -/
theorem perelmanF_step_lt_at_threshold_one (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, c i = 1) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {n : ℕ} {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_eq (hc i).symm) hh ev hi

/-- **Backward compatibility of the restatement.** Every application in the old
`∀ i, 1 < c i` format is recovered from the restated promoted theorem. -/
theorem perelmanF_step_lt_sharp_of_lt (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_lt (hc i)) hh ev hi

/-! ## Axiom audit -/

#print axioms gibbsTerm_strictAnti_at_threshold_one
#print axioms perelmanF_step_lt_at_threshold_one
#print axioms perelmanF_step_lt_sharp_of_lt

end EvolutionSharp
end D7
end Poincare
