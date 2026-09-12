/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

NEGATIVE CONTROL for the D12 fail-closed axiom audit.  This module is intentionally NOT
imported by any proof module.  It declares a forbidden axiom and a theorem depending on it;
`tools/d12_axiom_audit.py` must reject this file (and its self-check must succeed), proving
that the audit detects unapproved axioms.
-/

/-- NEGATIVE CONTROL: forbidden axiom.  Exists only to test audit detection. -/
axiom d12NegControlBadAxiom : False

/-- NEGATIVE CONTROL: theorem depending on the forbidden axiom. -/
theorem d12NegControlBadTheorem : False :=
  d12NegControlBadAxiom

#print axioms d12NegControlBadTheorem
