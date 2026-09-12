/-
L5-topology-audit — fresh negative-control module (authored for this audit, NOT part of
`release/`: it lives outside the package so it cannot pollute the release build).

It declares a forbidden axiom and a theorem whose cone reaches it.  The audit detector
`L5Audit.runAudit` must reject it with a nonzero exit when the declaration is not excused.
-/

axiom l5FreshNegControlAxiom : False

theorem l5FreshNegControlTheorem : False := l5FreshNegControlAxiom
