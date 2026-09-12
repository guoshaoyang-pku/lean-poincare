/-
D13-critical-path-review — intentional negative-control root.

This root imports the deliberate negative control and runs the same fail-closed axiom
audit used by the positive root.  It MUST fail with exit code 1 and must name
`Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom`.
-/
import Poincare.D13.CriticalPathReview.AxiomAudit
import Poincare.D13.CriticalPathReview.NegControl

open Poincare.D13.CriticalPathReview

#d13_axiom_audit
