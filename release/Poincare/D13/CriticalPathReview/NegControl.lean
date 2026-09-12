/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Intentional negative control (NOT part of any proof)

This module declares a forbidden axiom so that the fail-closed detector can be shown to
fire.  It is **never imported by any proof module**; the driver
`audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean` imports it together with
`AxiomAudit` and requires `#d13_axiom_audit` to FAIL and to name exactly this axiom.
-/

namespace Poincare.D13.CriticalPathReview.NegControl

/-- NEGATIVE CONTROL ONLY: an intentionally unapproved axiom.  Do not use in any proof. -/
axiom negControlBadAxiom : False

/-- NEGATIVE CONTROL ONLY: a theorem depending on the unapproved axiom. -/
theorem negControlBadTheorem : False := negControlBadAxiom

end Poincare.D13.CriticalPathReview.NegControl
