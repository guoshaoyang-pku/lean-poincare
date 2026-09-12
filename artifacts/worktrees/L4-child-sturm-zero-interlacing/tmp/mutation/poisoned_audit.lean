/-
Pass-6 gate-sensitivity mutation artifact — **not part of the release tree**.

`tools/acceptance_pass6.py` compiles this file and feeds the elaboration output through the
same parser/allow-list logic that `tools/run_sturm_gates.py` uses for the deliverable axiom
audit.  The file deliberately introduces a *new axiom* (`p6_mutation_axiom`) and a theorem
that depends on it, so the audit must report a violation (an axiom outside
`{propext, Classical.choice, Quot.sound}`).  If the audit machinery were vacuous, this file
would pass it; the pass-6 check requires that it does not.

This file lives under `tmp/`, is never part of `release/`, and is never scanned by the
release gate.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacing

namespace Poincare.L4.GeodesicComparison

axiom p6_mutation_axiom : False

theorem p6_mutation_poisoned : False := p6_mutation_axiom

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.p6_mutation_axiom
#print axioms Poincare.L4.GeodesicComparison.p6_mutation_poisoned
#print axioms Poincare.L4.GeodesicComparison.modelJacobiSolutionOn
#print axioms Poincare.L4.GeodesicComparison.exists_zero_of_curvature_lt
