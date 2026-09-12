/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

Literal `#print axioms` evidence for every declaration authored in this task.  The
programmatic fail-closed audit is `Poincare.D13.CriticalPathReview.AxiomAudit`; this file is
the independent literal printout, parsed by `audit-evidence/tools/d13_cp_audit.py`.

Expected: every cone is a subset of `{propext, Classical.choice, Quot.sound}` (many are
empty).
-/
import Poincare.D13.CriticalPathReview.AxiomAudit

#print axioms Poincare.D13.CriticalPathReview.exists_last_zero
#print axioms Poincare.D13.CriticalPathReview.scalar_forward_invariance
#print axioms Poincare.D13.CriticalPathReview.scalar_forward_invariance_of_locallyLipschitz
#print axioms Poincare.D13.CriticalPathReview.scalar_forward_invariance_witness
#print axioms Poincare.D13.CriticalPathReview.scalarMat
#print axioms Poincare.D13.CriticalPathReview.scalarField
#print axioms Poincare.D13.CriticalPathReview.eq_scalarMat_of_fin_one
#print axioms Poincare.D13.CriticalPathReview.scalarMat_posSemidef_iff
#print axioms Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff
#print axioms Poincare.D13.CriticalPathReview.b1_dimension_one
#print axioms Poincare.D13.CriticalPathReview.kernelTangent_scalarField_id
#print axioms Poincare.D13.CriticalPathReview.statementConstants
#print axioms Poincare.D13.CriticalPathReview.transitiveProofConstants
#print axioms Poincare.D13.CriticalPathReview.runCriticalPathAudit
#print axioms Poincare.D13.CriticalPathReview.directDependencies
#print axioms Poincare.D13.CriticalPathReview.consumerCount
#print axioms Poincare.D13.CriticalPathReview.runUsageProbe
#print axioms Poincare.D13.CriticalPathReview.approvedAxioms
#print axioms Poincare.D13.CriticalPathReview.auditedDeclarations
#print axioms Poincare.D13.CriticalPathReview.runAxiomAudit
