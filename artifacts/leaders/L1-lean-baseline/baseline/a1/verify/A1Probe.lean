/-
# A1 restatement probe (run inside `baseline/a1/patched-release`)

Evidence probe for the A1 upstream restatement.  It is run with

    cd baseline/a1/patched-release && lake env lean ../../../baseline/a1/verify/A1Probe.lean

and its output is preserved verbatim in `baseline/a1/logs/a1-probe.log`.

The `#check`s below are *positive* evidence for the restated signatures: the first two
succeed only if `gibbsTerm_strictAnti` accepts the sharp hypothesis `1 ≤ c`, and the third
succeeds only if `perelmanF_step_lt` accepts `∀ i, 1 ≤ c i`.  The `#print axioms` lines are
the kernel cone of the restated declarations and of the sharp-only consumers.
-/

import Poincare.D7.EvolutionSharp.AxiomAudit
import Audit.CounterexampleAudit

open Poincare.Longrun.Evolution

/-! ## Positive signature checks (sharp hypothesis accepted) -/

example (c : ℝ) (hc : 1 ≤ c) : StrictAnti (gibbsTerm c) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti c hc

example {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) : gibbsTerm c (x + u) < gibbsTerm c x :=
  Poincare.Longrun.Evolution.gibbsTerm_step_lt hc hu

example {ι : Type} [Fintype ι] (F : Poincare.Longrun.CurvatureODE.ReactionField ι)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 < h)
    {traj : ℕ → ι → ℝ} (ev : Poincare.Longrun.CurvatureODE.DiscreteEvolution F h traj) {n : ℕ} {i : ι}
    (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F hc hh ev hi

/-! ## Printed signatures (machine-readable) -/

#check @Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#check @Poincare.Longrun.Evolution.gibbsTerm_step_lt
#check @Poincare.Longrun.Evolution.perelmanF_step_lt

/-! ## Axiom cones -/

#print axioms Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_lt
#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt
#print axioms Poincare.D7.EvolutionSharp.gibbsTerm_strictAnti_at_threshold_one
#print axioms Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one
#print axioms Poincare.D7.EvolutionSharp.perelmanF_step_lt_sharp_of_lt
#print axioms D4Audit.gibbsTerm_strictAnti_of_one_le
#print axioms D4Audit.perelmanF_step_lt_of_one_le
