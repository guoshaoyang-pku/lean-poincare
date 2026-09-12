/-
# Poincare.D7.EvolutionSharp.Witnesses

**D7 evolution sharp restatement: the sharpened statements strictly generalize the
promoted ones.**

The implication lemmas of `Poincare.D7.EvolutionSharp.Implications` show that the old
statements follow from the sharpened ones. This module shows the other half: the sharpened
hypotheses are **strictly weaker**, and the sharpened conclusions are genuinely non-vacuous
at the newly admitted boundary.

For each of the three sharpened theorems the witness is the threshold `c = 1` (or
`c ≡ 1` for the finite functional):

* the new hypothesis `1 ≤ c` (respectively `∀ i, 1 ≤ c i`) holds;
* the discarded old hypothesis `1 < c` (respectively `∀ i, 1 < c i`) **fails**;
* the sharpened theorem applies and produces a strict decrease, while the promoted theorem
  is inapplicable at the witness because its hypothesis is false there.

The last point is the formal, kernel-checked content of "strictly generalizes": Lean cannot
prove unprovability of the old statement from its own hypotheses, so strictness is
exhibited by a concrete witness at which the old hypothesis is refuted and the new
conclusion is independently checked (the `..._by_values` lemmas recompute the conclusion
numerically without invoking the sharpened theorem).

## Analytic boundary (explicit)

The witnesses are finite, explicit and computable: the one-point square reaction field
`lam ↦ lam²` on `Fin 1`, the explicit-Euler trajectory `1 → 2` with step `1`, and the
threshold data `c = 1`. The trajectory solves the D2 discrete recurrence by construction.
No continuous-time or manifold-level claim is made. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.Implications

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

/-! ## The one-variable threshold witness `c = 1` -/

/-- At the threshold `c = 1` the new hypothesis `1 ≤ c` holds and the discarded old
hypothesis `1 < c` fails. -/
theorem one_le_one_and_not_one_lt_one : (1 : ℝ) ≤ 1 ∧ ¬ (1 : ℝ) < 1 :=
  ⟨le_refl 1, lt_irrefl 1⟩

/-- The sharpened strict-antitonicity theorem applies at the threshold `c = 1`. -/
theorem gibbsTerm_strictAnti_at_one : StrictAnti (gibbsTerm 1) :=
  gibbsTerm_strictAnti_of_one_le 1 le_rfl

/-- The sharpened conclusion at the threshold is a genuine strict decrease. -/
theorem gibbsTerm_strict_decrease_at_one : gibbsTerm 1 1 < gibbsTerm 1 0 :=
  gibbsTerm_strictAnti_at_one (by norm_num)

/-- The sharpened strict-step theorem applies at the threshold `c = 1`. -/
theorem gibbsTerm_step_lt_at_one : gibbsTerm 1 (0 + 1) < gibbsTerm 1 0 :=
  gibbsTerm_step_lt_of_one_le (c := 1) (x := 0) (u := 1) le_rfl (by norm_num)

/-- **Strict generalization, one-variable strict antitonicity.** The new hypothesis holds,
the old one fails, and the new conclusion is non-vacuous. -/
theorem gibbsTerm_strictAnti_strictly_generalizes :
    (1 : ℝ) ≤ 1 ∧ ¬ (1 : ℝ) < 1 ∧ StrictAnti (gibbsTerm 1) ∧ gibbsTerm 1 1 < gibbsTerm 1 0 :=
  ⟨one_le_one_and_not_one_lt_one.1, one_le_one_and_not_one_lt_one.2,
    gibbsTerm_strictAnti_at_one, gibbsTerm_strict_decrease_at_one⟩

/-- **Strict generalization, one-variable strict step.** The new hypothesis holds, the old
one fails, and the new conclusion is non-vacuous. -/
theorem gibbsTerm_step_lt_strictly_generalizes :
    (1 : ℝ) ≤ 1 ∧ ¬ (1 : ℝ) < 1 ∧ gibbsTerm 1 (0 + 1) < gibbsTerm 1 0 :=
  ⟨one_le_one_and_not_one_lt_one.1, one_le_one_and_not_one_lt_one.2, gibbsTerm_step_lt_at_one⟩

/-! ## The finite-functional threshold witness `c ≡ 1` -/

/-- The explicit-Euler trajectory of the promoted one-point square reaction field
`lam ↦ lam²` with step `1`, starting at `lam = 1`: `0 ↦ 1`, `1 ↦ 2`. -/
def sharpWitnessTraj : ℕ → Fin 1 → ℝ
  | 0 => fun _ => (1 : ℝ)
  | n + 1 => eulerStep (squareField : ReactionField (Fin 1)) 1 (sharpWitnessTraj n)

/-- The witness trajectory solves the D2 explicit-Euler recurrence by construction. -/
theorem sharpWitnessTraj_evolution :
    DiscreteEvolution (squareField : ReactionField (Fin 1)) 1 sharpWitnessTraj where
  step := fun _ _ => rfl

/-- The trajectory at time `0` is the constant state `lam = 1`. -/
theorem sharpWitnessTraj_zero : sharpWitnessTraj 0 = fun _ : Fin 1 => (1 : ℝ) := rfl

/-- The trajectory at time `1` is the constant state `lam = 2`. -/
theorem sharpWitnessTraj_one : sharpWitnessTraj 1 = fun _ : Fin 1 => (2 : ℝ) := by
  funext i
  fin_cases i
  simp [sharpWitnessTraj, eulerStep, squareField_eval]
  norm_num

/-- The threshold curvature data `c ≡ 1` satisfies the sharpened hypothesis `∀ i, 1 ≤ c i`. -/
theorem sharpWitness_c_new : ∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => (1 : ℝ)) i :=
  fun _ => le_rfl

/-- The threshold curvature data `c ≡ 1` fails the discarded hypothesis `∀ i, 1 < c i`. -/
theorem sharpWitness_c_old_fails : ¬ (∀ i : Fin 1, 1 < (fun _ : Fin 1 => (1 : ℝ)) i) :=
  fun h => absurd (h 0) (lt_irrefl 1)

/-- The reaction of the square field at the initial witness state is strictly positive, so
the sharpened theorem's remaining side condition holds. -/
theorem sharpWitness_reaction_pos : 0 < (squareField : ReactionField (Fin 1)).eval (sharpWitnessTraj 0) 0 := by
  rw [squareField_eval]
  norm_num [sharpWitnessTraj]

/-- **The sharpened theorem applies at the threshold `c ≡ 1`.** The promoted
`perelmanF_step_lt` is inapplicable here (`1 < 1` is false), but the sharpened theorem
produces a strict decrease. -/
theorem sharpWitness_strict_decrease :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0) :=
  perelmanF_step_lt_of_one_le (squareField : ReactionField (Fin 1))
    (c := fun _ : Fin 1 => (1 : ℝ)) (fun _ => le_rfl) (h := 1) (by norm_num)
    (traj := sharpWitnessTraj) sharpWitnessTraj_evolution (n := 0) (i := 0)
    sharpWitness_reaction_pos

/-- The explicit values of the witness functional: `5 e^{-2}` at time `1` and `2 e^{-1}`
at time `0`. -/
theorem sharpWitness_values :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) = 5 * Real.exp (-2) ∧
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0) = 2 * Real.exp (-1) := by
  constructor
  · rw [sharpWitnessTraj_one]
    simp [perelmanF, gibbsTerm]
    norm_num
  · simp [perelmanF, gibbsTerm, sharpWitnessTraj]
    norm_num

/-- **Independent numerical check of the witness conclusion.** The strict decrease
`5 e^{-2} < 2 e^{-1}` is proved directly from the values, without invoking the sharpened
theorem; it is equivalent to `5 < 2 e`. -/
theorem sharpWitness_strict_decrease_by_values :
    perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) <
      perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0) := by
  rw [sharpWitness_values.1, sharpWitness_values.2]
  have h1 : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmain : (5 : ℝ) * Real.exp (-2) < 2 * Real.exp (-1) := by
    rw [Real.exp_neg, Real.exp_neg]
    have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [hexp2]
    have hpos : 0 < Real.exp 1 := Real.exp_pos 1
    field_simp
    nlinarith
  exact hmain

/-- **Strict generalization, finite-functional strict step.** The new hypothesis holds, the
old one fails, and the new conclusion is non-vacuous (and independently recomputed). -/
theorem perelmanF_step_lt_strictly_generalizes :
    (∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => (1 : ℝ)) i) ∧
      ¬ (∀ i : Fin 1, 1 < (fun _ : Fin 1 => (1 : ℝ)) i) ∧
      (perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) <
        perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0)) :=
  ⟨sharpWitness_c_new, sharpWitness_c_old_fails, sharpWitness_strict_decrease⟩

/-- The same strict generalization with the conclusion supplied by the independent
numerical check rather than by the sharpened theorem. -/
theorem perelmanF_step_lt_strictly_generalizes_by_values :
    (∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => (1 : ℝ)) i) ∧
      ¬ (∀ i : Fin 1, 1 < (fun _ : Fin 1 => (1 : ℝ)) i) ∧
      (perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 1) <
        perelmanF (fun _ : Fin 1 => (1 : ℝ)) (sharpWitnessTraj 0)) :=
  ⟨sharpWitness_c_new, sharpWitness_c_old_fails, sharpWitness_strict_decrease_by_values⟩

/-! ## The hypothesis sets are strictly nested -/

/-- **The sharpened hypothesis set is strictly larger than the old one**, already on an
index type with two components: `c = (1, 2)` satisfies `∀ i, 1 ≤ c i` but not
`∀ i, 1 < c i`. -/
theorem sharp_hypothesis_strictly_weaker :
    ∃ c : Fin 2 → ℝ, (∀ i, 1 ≤ c i) ∧ ¬ (∀ i, 1 < c i) := by
  refine ⟨fun i => if i = 0 then 1 else 2, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro h
    have h0 := h 0
    norm_num at h0

/-! ## Axiom audit -/

#print axioms one_le_one_and_not_one_lt_one
#print axioms gibbsTerm_strictAnti_at_one
#print axioms gibbsTerm_strict_decrease_at_one
#print axioms gibbsTerm_step_lt_at_one
#print axioms gibbsTerm_strictAnti_strictly_generalizes
#print axioms gibbsTerm_step_lt_strictly_generalizes
#print axioms sharpWitnessTraj
#print axioms sharpWitnessTraj_evolution
#print axioms sharpWitnessTraj_zero
#print axioms sharpWitnessTraj_one
#print axioms sharpWitness_c_new
#print axioms sharpWitness_c_old_fails
#print axioms sharpWitness_reaction_pos
#print axioms sharpWitness_strict_decrease
#print axioms sharpWitness_values
#print axioms sharpWitness_strict_decrease_by_values
#print axioms perelmanF_step_lt_strictly_generalizes
#print axioms perelmanF_step_lt_strictly_generalizes_by_values
#print axioms sharp_hypothesis_strictly_weaker

end EvolutionSharp
end D7
end Poincare
