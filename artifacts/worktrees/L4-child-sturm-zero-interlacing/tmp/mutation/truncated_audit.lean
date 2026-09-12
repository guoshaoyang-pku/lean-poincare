/-
Pass-6 gate-sensitivity mutation artifact — **not part of the release tree**.

This is the truncation mutant: it covers only two of the deliverable's declarations
(`p6_mutation_poisoned`, `p6_mutation_axiom`) and omits every other `#print axioms` line
that the real audit module contains.  The naive "expected declarations are those listed in
the audited source" check of `tools/run_sturm_gates.py` cannot see this truncation (the
expected list shrinks together with the report); the fail-closed *coverage* check used by
the independent acceptance passes — every declaration of the two deliverable modules must
appear in the audit report — must reject it.  `tools/acceptance_pass6.py` requires that the
coverage detector fires on this file.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacing

namespace Poincare.L4.GeodesicComparison

axiom p6_mutation_axiom : False

theorem p6_mutation_poisoned : False := p6_mutation_axiom

end Poincare.L4.GeodesicComparison

#print axioms Poincare.L4.GeodesicComparison.p6_mutation_poisoned
#print axioms Poincare.L4.GeodesicComparison.modelJacobiSol_pos
