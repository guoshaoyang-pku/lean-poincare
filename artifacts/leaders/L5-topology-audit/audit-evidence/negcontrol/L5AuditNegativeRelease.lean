/-
L5-topology-audit — negative control B: the release's own negative-control module
`Poincare.D12.VolumeIBP.Audit` (declares `axiom negativeControl`), audited with nothing
excused.  Must FAIL (nonzero exit) and name exactly `Poincare.D12.VolumeIBP.negativeControl`.

This is the same detector and the same import closure as positive pass A; only the exclusion
list differs, so the pair (positive passes / negative fails) is a controlled experiment on
the audit itself.
-/
import L5DetectorA

open L5Audit

run_cmd runAudit ["Poincare.D12.VolumeIBP".toName] [] false
