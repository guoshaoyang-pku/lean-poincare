/-
L5-topology-audit — negative control A: a *fresh* forbidden axiom outside the release.

The detector is pointed at the single module `L5NegControlFresh` (declaring
`l5FreshNegControlAxiom`) with nothing excused.  It must FAIL (nonzero exit) and name
exactly `l5FreshNegControlAxiom`.  This proves the fail-closed path of the detector is
live end-to-end, independently of the release's own negative controls.
-/
import L5DetectorA
import L5NegControlFresh

open L5Audit

run_cmd runAudit ["L5NegControlFresh".toName] [] false
