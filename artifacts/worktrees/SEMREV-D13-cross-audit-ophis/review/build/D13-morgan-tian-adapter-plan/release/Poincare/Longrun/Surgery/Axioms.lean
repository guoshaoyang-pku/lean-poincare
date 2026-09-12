/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom ledger for the surgery module tree

This file runs `#print axioms` on every main declaration of `Poincare.Longrun.Surgery`.  It
contains no declarations of its own: it is the machine-checkable record required by the
`D3-surgery-ledger` result card.  A successful run reports only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) and never `sorryAx`.

The output is captured by

```text
lake env lean Poincare/Longrun/Surgery/Axioms.lean
```
-/

import Poincare.Longrun.Surgery

set_option autoImplicit false

namespace Poincare.Longrun.Surgery

/-! ## Basic interfaces -/

#print axioms TopSpace
#print axioms LedgerPredicates
#print axioms canonicalLedger
#print axioms SurgeryDatum
#print axioms SurgeryDatum.pre
#print axioms SurgeryDatum.post
#print axioms SurgeryDatum.trivial
#print axioms SurgeryCertificate
#print axioms SurgeryCertificate.trivial
#print axioms SurgeryCertificate.ofHomeomorph
#print axioms SurgeryCertificate.ofHomotopyEquiv

/-! ## Chains -/

#print axioms SurgeryChain
#print axioms SurgeryChain.append
#print axioms SurgeryChain.append_assoc
#print axioms ChainCertificate
#print axioms ChainCertificate.append
#print axioms ChainCertificate.preservation
#print axioms ChainCertificate.compact_preserved
#print axioms ChainCertificate.orientable_preserved
#print axioms ChainCertificate.simplyConnected_preserved

/-! ## Toy surgery relation -/

#print axioms ToyRel
#print axioms toyRel_functional
#print axioms toyRel_lt
#print axioms toyRel_succ
#print axioms toyRel_not_refl
#print axioms toyRel_nonempty
#print axioms toyRel_odd_iff
#print axioms ToyChain
#print axioms ToyChain.value
#print axioms ToyChain.le
#print axioms ToyChain.no_infinite
#print axioms ToyChain.reflTransGen
#print axioms toyLedger
#print axioms toyDatum
#print axioms toyCertificate
#print axioms toyChain321
#print axioms toyChain321Certificate
#print axioms toyChain321_preserves
#print axioms toyChain321_compact

/-! ## Missing geometric inputs (statement-only) -/

#print axioms NeckAnalysis
#print axioms NeckAnalysis.deltaNeck_of_highCurvature
#print axioms NeckAnalysis.admissible_of_highCurvature
#print axioms NeckAnalysis.realizes_of_highCurvature
#print axioms NeckAnalysis.target_preserved_of_highCurvature
#print axioms NeckAnalysis.certificate
#print axioms ExtinctionTheorem
#print axioms ExtinctionTheorem.finitelyMany_of_complexity
#print axioms ExtinctionTheorem.extincts_of_complexity
#print axioms ExtinctionTheorem.terminalSphere_of_complexity
#print axioms MissingInputs
#print axioms extincts_and_target
#print axioms target_of_neckAnalysis
#print axioms toy_extinction_skeleton
#print axioms toy_chain_value

end Poincare.Longrun.Surgery
