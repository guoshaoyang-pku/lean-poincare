/-
# Poincare.D7.EvolutionSharp.AxiomAudit

**D7 evolution sharp restatement: consolidated kernel axiom report.**

This driver imports every authored D7 module and prints the kernel axiom cone of every new
declaration, together with the three promoted D4 declarations that were sharpened. The
expected cone for every entry is a subset of
`[propext, Classical.choice, Quot.sound]`; in particular there is no `sorryAx`, no project
`axiom`, no `unsafe` declaration, no `native_decide` and no `proof_wanted`.

This file is an audit driver, not mathematical content; the sharpened statements and their
proofs live in `GibbsSharp`, `FunctionalSharp`, `Implications`, `Witnesses` and
`Certificates`. No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in
this file.
-/

import Poincare.D7.EvolutionSharp.Certificates

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

/-! ## Statement shapes (probe) -/

#check @gibbsTerm_strictAnti_of_one_le
#check @gibbsTerm_step_lt_of_one_le
#check @perelmanF_step_lt_of_one_le
#check @perelmanAntitoneCertificate_discrete_sharp
#check @perelmanAntitoneCertificate_sharp
#check @continuousPerelmanCertificate_sharp

/-! ## Sharpened declarations -/

#print axioms gibbsTerm_strictAnti_one
#print axioms gibbsTerm_strictAnti_of_one_le
#print axioms gibbsTerm_step_lt_of_one_le
#print axioms perelmanF_step_lt_of_one_le

/-! ## Implication lemmas -/

#print axioms GibbsStrictAntiSharp
#print axioms GibbsStrictAntiOld
#print axioms gibbsStrictAnti_old_of_sharp
#print axioms gibbsTerm_strictAnti_old_of_sharp
#print axioms gibbsTerm_strictAnti_promoted
#print axioms gibbsTerm_strictAnti_old_recovered
#print axioms GibbsStepLtSharp
#print axioms GibbsStepLtOld
#print axioms gibbsStepLt_old_of_sharp
#print axioms gibbsTerm_step_lt_old_of_sharp
#print axioms gibbsTerm_step_lt_promoted
#print axioms gibbsTerm_step_lt_old_recovered
#print axioms PerelmanFStepLtSharp
#print axioms PerelmanFStepLtOld
#print axioms perelmanFStepLt_old_of_sharp
#print axioms perelmanF_step_lt_old_of_sharp
#print axioms perelmanF_step_lt_promoted
#print axioms perelmanF_step_lt_old_recovered

/-! ## Strict-generalization witnesses -/

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

/-! ## Certificate instantiations -/

#print axioms perelmanAntitoneCertificate_discrete_sharp
#print axioms perelmanAntitoneCertificate_discrete_sharp_strict_step
#print axioms perelmanAntitoneCertificate_discrete_sharp_compare
#print axioms perelmanAntitoneCertificate_discrete_sharp_lower
#print axioms perelmanAntitoneCertificate_discrete_sharp_no_strict_step_of_eq
#print axioms perelmanAntitoneCertificate_discrete_of_old
#print axioms perelmanAntitoneCertificate_discrete_sharp_nonvacuous
#print axioms perelmanAntitoneCertificate_sharp
#print axioms continuousPerelmanCertificate_sharp
#print axioms continuousPerelmanCertificate_sharp_le_initial
#print axioms continuousPerelmanCertificate_sharp_nonvacuous
#print axioms perelmanAntitoneCertificate_discrete_sharp_at_one
#print axioms perelmanAntitoneCertificate_discrete_sharp_strict_at_one

/-! ## Promoted D4 declarations (cross-reference) -/

#print axioms Poincare.Longrun.Evolution.gibbsTerm_strictAnti
#print axioms Poincare.Longrun.Evolution.gibbsTerm_step_lt
#print axioms Poincare.Longrun.Evolution.perelmanF_step_lt

end EvolutionSharp
end D7
end Poincare
