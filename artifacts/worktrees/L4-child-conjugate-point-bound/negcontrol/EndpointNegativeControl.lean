/-
Endpoint-bound negative control for the fail-closed axiom audit.

This file is intentionally NOT part of the release package (it lives outside `release/` and
is never imported by `ConjugatePointAxiomAudit.lean`).  It exists so that the acceptance
predicate used by `tools/l4cp_verify.py` is exercised on genuinely tainted declarations and
shown to reject them:

* `negControl_sorry` depends on `sorryAx`;
* `negControl_axiom` depends on the unapproved axiom `negControl_axiom`.

Run from the release directory:

    lake env lean ../negcontrol/EndpointNegativeControl.lean

A correct audit must parse both cones and reject both, because neither is a subset of
`{propext, Classical.choice, Quot.sound}`.
-/
theorem negControl_sorry : True := by sorry

axiom negControl_axiom : True

#print axioms negControl_sorry
#print axioms negControl_axiom
