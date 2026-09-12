/-
Copyright (c) 2026 Poincare Longrun D12 semantic-ledger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-semantic-ledger)
-/

import Poincare.D12.SemanticLedger.Defect
import Poincare.D7.HeatKernel.Basic
import Poincare.D7.HeatKernel.Blocked
import Poincare.D7.HeatKernel.Grid
import Poincare.D7.HeatKernel.Instance
import Poincare.D7.HeatKernel.Example
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Homeomorphism
import Poincare.D10.HeatKernelEuclidean.Basic
import Poincare.D10.HeatKernelEuclidean.Mass
import Poincare.D10.HeatKernelEuclidean.HeatEquation
import Poincare.D10.HeatKernelEuclidean.Semigroup
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# D12RealModuleProbe — audit probe against the independently rebuilt snapshot oleans

This task-local module imports the **real** builder modules
`Poincare.D7.HeatKernel.*`, `Poincare.D7.Recognition.*` and
`Poincare.D10.HeatKernelEuclidean.*`, whose oleans were recompiled by
`tools/d12_rebuild_snapshot.py` from the pristine snapshot sources (hashes in
`manifest/d12-rebuild-manifest.json`).  It

1. `#check`s the real declaration types recorded in the semantic ledger,
2. proves, against the **real** `HeatKernelData.initialCondition` field type,
   that no heat-kernel datum on `ℝ` whose volume is Lebesgue measure and whose
   kernel is the standard Gaussian can exist — the kernel-checked validation of
   the D11 heat test-function defect,
3. re-runs a fail-closed programmatic axiom audit over the real D7/D10
   declarations it cites.

This file is NOT part of the release package build (it lives in
`audit_probes/`); it compiles with `lake env lean audit_probes/D12RealModuleProbe.lean`
from `release/` (or from the worktree root via the root wrapper package), where
`release/.lake/build/lib/lean` contains both the package oleans and the
rebuilt snapshot oleans.
-/

open MeasureTheory Filter
open scoped Topology
open Lean Elab Command

namespace Poincare.D12.SemanticLedger

/-! ## 1. Real declaration types -/

#check Poincare.D7.HeatKernel.HeatKernelData
#check Poincare.D7.HeatKernel.HeatKernelData.initialCondition
#check Poincare.D7.HeatKernel.HeatKernelExistenceStatement
#check Poincare.D7.HeatKernel.FiniteGridHeatKernel.unique
#check Poincare.D7.HeatKernel.finiteGrid_heatKernel_unique
#check Poincare.D7.HeatKernel.GridHeatSolution.unique
#check Poincare.D7.Recognition.SphericalPiece
#check Poincare.D7.Recognition.ConnectedSumDecomposition
#check Poincare.D7.Recognition.ExtinctionCertificate
#check Poincare.D7.Recognition.CanonicalNeighborhoodInput
#check Poincare.D7.Recognition.SphericalPieceRecognition
#check Poincare.D7.Recognition.RecognitionHypotheses
#check Poincare.D7.Recognition.stage6Target_of_certificates
#check Poincare.D7.Recognition.missingFinalHomeomorphismConstruction
#check Poincare.D7.Recognition.finalHomeomorphismDependencies
#check Poincare.D10.HeatKernelEuclidean.gaussianKernel
#check Poincare.D10.HeatKernelEuclidean.heat_equation
#check Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral
#check Poincare.D10.HeatKernelEuclidean.semigroupConvolutionIdentity

/-! ## 2. The defect theorem against the REAL field -/

/-- The real `HeatKernelData.initialCondition` field, verbatim: for every continuous test
function, the kernel integral against `D.volume` converges to the Dirac delta. -/
theorem real_initialCondition_specializes (D : Poincare.D7.HeatKernel.HeatKernelData ℝ)
    (x : ℝ) : ∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun t : ℝ => ∫ y, D.kernel x y t * f y ∂D.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  intro f hf
  exact D.initialCondition x f hf

/-- **Main defect theorem against the real D7 structure.**  There is no
`HeatKernelData ℝ` whose reference measure is Lebesgue measure and whose kernel
is the standard 1D Gaussian heat kernel: the `initialCondition` field would
require the convergence `∫ y, K x y t * f y → f x` for EVERY continuous `f`,
and the continuous test function `f y = exp (y⁴)` makes the integrand
non-integrable for every `t > 0` (so the Bochner integral is `0`, while
`f 0 = 1`). -/
theorem realField_unsatisfiable_by_gaussian :
    ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData ℝ,
        D.volume = volume ∧ D.kernel = Poincare.D12.SemanticLedger.gaussianKernelXY := by
  rintro ⟨D, hvol, hker⟩
  have hIC := D.initialCondition 0 testFunction testFunction_continuous
  have htest : Poincare.D12.SemanticLedger.D7InitialConditionAt
      Poincare.D12.SemanticLedger.gaussianKernelXY 0 := by
    intro f hf
    have h' := D.initialCondition 0 f hf
    simpa [hvol, hker] using h'
  exact Poincare.D12.SemanticLedger.not_initialCondition_gaussian htest

/-! ## 3. Programmatic axiom re-check of the cited REAL declarations -/

/-- The real D7/D10 declarations cited by this audit. -/
private def realAuditedDeclarations : List Name :=
  [ ``Poincare.D7.HeatKernel.HeatKernelData.kernel_pos_of_lowerBound,
    ``Poincare.D7.HeatKernel.HeatKernelExistenceStatement,
    ``Poincare.D7.Recognition.isSurgeryAdmissible_or_compactSpherical,
    ``Poincare.D7.Recognition.not_isSurgeryAdmissible_of_compactSpherical,
    ``Poincare.D7.Recognition.SphericalPiece.ofCertificate,
    ``Poincare.D7.Recognition.ExtinctionCertificate.toConclusion,
    ``Poincare.D7.Recognition.RecognitionHypotheses.pieces_simplyConnected,
    ``Poincare.D7.Recognition.RecognitionHypotheses.pieces_homeomorph_sphere,
    ``Poincare.D7.Recognition.RecognitionHypotheses.homeomorph_sphere,
    ``Poincare.D7.Recognition.RecognitionHypotheses.stage6Target,
    ``Poincare.D7.Recognition.stage6Target_of_certificates,
    ``Poincare.D7.Recognition.extinctionWithSphericalPieces_of_certificates,
    ``Poincare.D10.HeatKernelEuclidean.heat_equation,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral,
    ``Poincare.D10.HeatKernelEuclidean.semigroupConvolutionIdentity,
    ``Poincare.D12.SemanticLedger.real_initialCondition_specializes,
    ``Poincare.D12.SemanticLedger.realField_unsatisfiable_by_gaussian ]

/-- The approved axiom cone. -/
private def realApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in realAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !realApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D12RealModuleAxiomCheck: PASS — all {realAuditedDeclarations.length} cited \
      real D7/D10 declarations depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D12RealModuleAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D12RealModuleAxiomCheck: FAIL"

end Poincare.D12.SemanticLedger


-- A3 appended independent axiom probe
#print axioms Poincare.D12.SemanticLedger.real_initialCondition_specializes
#print axioms Poincare.D12.SemanticLedger.realField_unsatisfiable_by_gaussian
