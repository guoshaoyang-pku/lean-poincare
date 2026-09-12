/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fail-closed audit for `Poincare.L4.Compactness.RicciToDoubling`

This driver is **not** mathematical content.  It

1. prints the full signature of every declaration added by
   `Poincare/L4/Compactness/RicciToDoubling.lean` (`#check`), and
2. runs `Lean.collectAxioms` on every one of them and **fails closed** (non-zero exit) if any
   axiom cone is not a subset of `{propext, Classical.choice, Quot.sound}`.

The declaration list is written out literally; a missing/renamed declaration makes the
`#check` line fail, so the audit cannot silently skip a declaration.
-/
import Poincare.L4.Compactness.RicciToDoubling
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.L4.Compactness.Audit

-- Full signatures (the `#check` output is the "compiling modules with full signatures" evidence).
#check @euclidModel_volumeRatio_closedForm
#check @euclidModel_volume_doubling_closedForm
#check @euclid_volume_ratio_le_of_ricci_nonneg
#check @euclid_volumeRatio_div_le_of_ricci_nonneg
#check @euclid_volume_doubling_of_ricci_nonneg
#check @euclidModel_hypotheses_witness
#check @radialVolume_euclidModel_one_doubling_witness
#check @radialVolume_euclidModel_one_value_witness
#check @IsRadialBallMeasure
#check @isRadialBallMeasure_real_witness
#check @coveringNumber_le_measure_ratio_of_radialBallMeasure
#check @coveringNumber_le_of_radialBallMeasure_doubling
#check @coveringNumber_le_of_ricci_nonneg_radialBallMeasure

/-- The exact declaration list the audit must cover. -/
def auditedDeclarations : List Name :=
  [ ``euclidModel_volumeRatio_closedForm
  , ``euclidModel_volume_doubling_closedForm
  , ``euclid_volume_ratio_le_of_ricci_nonneg
  , ``euclid_volumeRatio_div_le_of_ricci_nonneg
  , ``euclid_volume_doubling_of_ricci_nonneg
  , ``euclidModel_hypotheses_witness
  , ``radialVolume_euclidModel_one_doubling_witness
  , ``radialVolume_euclidModel_one_value_witness
  , ``IsRadialBallMeasure
  , ``isRadialBallMeasure_real_witness
  , ``coveringNumber_le_measure_ratio_of_radialBallMeasure
  , ``coveringNumber_le_of_radialBallMeasure_doubling
  , ``coveringNumber_le_of_ricci_nonneg_radialBallMeasure ]

run_cmd do
  let approved : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : List (Name × List Name) := []
  for d in auditedDeclarations do
    let axs ← Lean.collectAxioms d
    let axl := axs.toList
    logInfo m!"AXIOM-JSON {d}: {String.intercalate "," (axl.map Name.toString)}"
    let unapproved := axl.filter (fun a => !approved.contains a)
    if !unapproved.isEmpty then
      bad := (d, unapproved) :: bad
  if !bad.isEmpty then
    throwError m!"AXIOM-AUDIT FAIL-CLOSED: unapproved axiom cones: {bad.map (fun p => (p.1.toString, p.2.map Name.toString))}"
  logInfo m!"AXIOM-AUDIT PASS: {auditedDeclarations.length} declarations, every cone is a subset of the approved classical trio (propext, Classical.choice, Quot.sound)"

end Poincare.L4.Compactness.Audit
