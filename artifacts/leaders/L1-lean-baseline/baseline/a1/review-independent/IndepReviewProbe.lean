/-
# Independent adversarial probe for the A1 review (NOT author-produced)

Run from `baseline/a1/patched-release`:

    lake env lean ../../../baseline/a1/review-independent/IndepReviewProbe.lean

Checks that the reviewer performed beyond the author's A1Probe:

* `old_hyp_refuted`: the old hypothesis `∀ i, 1 < c i` is *refutable* at the threshold
  configuration `c ≡ 1` (not merely non-unifiable), so no term can supply it.
* `one_lt_one_false`: the literal `1 < 1` is false, which is what the old one-variable
  statement would need at `c = 1`.
* `consumer_nonvacuous`: the new sharp-only consumer
  `perelmanF_step_lt_at_threshold_one` is instantiated at a concrete D2 field, a concrete
  discrete trajectory with a strictly positive reaction component, so its hypotheses are
  simultaneously satisfiable and it is not vacuously true.
* `crosscheck_d4audit`: the same proposition is proved by the pre-existing, independently
  written `D4Audit.strict_step_positive_control`.
* `sharp_strictAnti_at_one` / `sharp_step_at_one`: the restated promoted theorems applied at
  the exact threshold via `le_rfl`.
-/
import Poincare.D7.EvolutionSharp.AxiomAudit
import Audit.CounterexampleAudit

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

namespace IndepReview

/-- The old hypothesis `∀ i, 1 < c i` is refutable at `c ≡ 1`. -/
theorem old_hyp_refuted {ι : Type} [Fintype ι] [Nonempty ι] {c : ι → ℝ}
    (hc : ∀ i, c i = 1) : ¬ (∀ i, 1 < c i) := by
  intro h
  have h1 : (1 : ℝ) < 1 := by
    have hi := h (Classical.arbitrary ι)
    rwa [hc] at hi
  exact lt_irrefl 1 h1

/-- What the old one-variable statement would require at `c = 1`. -/
theorem one_lt_one_false : ¬ ((1 : ℝ) < 1) := lt_irrefl 1

/-- The pre-existing D4Audit route to strict decrease at the threshold configuration. -/
theorem crosscheck_d4audit :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (D4Audit.sqTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (D4Audit.sqTraj 0) :=
  D4Audit.strict_step_positive_control

/-- The new consumer, instantiated at the same concrete threshold configuration. -/
theorem consumer_nonvacuous :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (D4Audit.sqTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (D4Audit.sqTraj 0) :=
  Poincare.D7.EvolutionSharp.perelmanF_step_lt_at_threshold_one
    (squareField : ReactionField (Fin 1)) (c := fun _ : Fin 1 => (1 : ℝ))
    (fun _ => rfl) (h := 1) (by norm_num) (traj := D4Audit.sqTraj)
    D4Audit.sqTraj_evolution (n := 0) (i := 0)
    (by simp [D4Audit.sqTraj, squareField_eval])

/-- Restated promoted theorem at the exact threshold, via `le_rfl`. -/
theorem sharp_strictAnti_at_one : StrictAnti (gibbsTerm 1) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti 1 le_rfl

/-- Restated promoted step theorem at the exact threshold, via `le_rfl`. -/
theorem sharp_step_at_one : gibbsTerm 1 (0 + 1) < gibbsTerm 1 0 :=
  Poincare.Longrun.Evolution.gibbsTerm_step_lt le_rfl (by norm_num)

#print axioms old_hyp_refuted
#print axioms consumer_nonvacuous
#print axioms crosscheck_d4audit
#print axioms sharp_strictAnti_at_one
#print axioms sharp_step_at_one

end IndepReview
