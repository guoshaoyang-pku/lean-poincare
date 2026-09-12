/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Critical-path statement audit (machine-checked input inventory)

This module derives the **exact residual inputs** of the load-bearing end-game chain from
the *compiled environment*, not from prose: for each declaration it prints and checks the
constants occurring in its **type** (the hypotheses) and in the **transitive proof-term
closure** (the constructors actually consumed).

Fail-closed checks performed by `#d13_cp_audit`:

1. every expected declaration exists;
2. every `requiredInType` constant occurs in the declaration's type (for structures: in the
   type of the constructor, i.e. the field telescope);
3. every `forbiddenInType` constant does **not** occur in the declaration's type
   (the machine-checked form of "input X was eliminated from the statement");
4. every claimed closure pair `(constructor, downstream)` has the constructor occurring in
   the downstream *type* or *transitive proof-term closure* (constructor + downstream
   checked use);
5. the top-level assembly type still mentions the root target
   `Poincare.Stage6.poincareConjectureTopologicalThree`.

Any failure raises an elaboration error: the command is fail-closed.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SemanticLedger.Defect
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D13.CriticalPathReview.ScalarViability
import Poincare.D13.CriticalPathReview.B1DimensionOne
import Lean.Elab.Command

set_option linter.unusedVariables false
set_option autoImplicit false

open Lean Elab Command

namespace Poincare.D13.CriticalPathReview

/-! ## The reviewed critical-path declarations -/

/-- The load-bearing declarations whose expanded statements are reviewed. -/
def mainChainDecls : List Name :=
  [ ``Poincare.D7.Recognition.stage6Target_of_certificates
  , ``Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition
  , ``Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses
  , ``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses
  , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypotheses
  , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2
  , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3
  , ``Poincare.D12.SurgeryRecognition.endGame_finalTopology
  , ``Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2
  , ``Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere
  , ``Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient
  , ``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm
  , ``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of
  , ``Poincare.D12.TensorMaximumBochner.KernelTangent
  , ``Poincare.D12.TensorMaximumBochner.hamiltonField
  , ``Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent
  , ``Poincare.D13.CriticalPathReview.scalar_forward_invariance
  , ``Poincare.D13.CriticalPathReview.scalar_forward_invariance_witness
  , ``Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff
  , ``Poincare.D13.CriticalPathReview.b1_dimension_one
  ]

/-- Residual inputs that must occur in the type of the given declaration. -/
def requiredInType : List (Name × List Name) :=
  [ (``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses,
      [ ``Poincare.D7.Recognition.ExtinctionCertificate
      , ``Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2
      , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3
      , ``Poincare.D7.Recognition.CanonicalNeighborhoodInput
      , ``Poincare.Stage6.poincareConjectureTopologicalThree ])
  , (``Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses,
      [ ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2 ])
  , (``Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition,
      [ ``Poincare.D7.Recognition.SphericalPieceRecognition ])
  , (``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3,
      [ ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel
      , ``Poincare.D7.Recognition.SphericalPiece ])
  , (``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2,
      [ ``Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel ])
  ]

/-- Inputs that were eliminated from the named statement (must NOT occur in its type). -/
def forbiddenInType : List (Name × List Name) :=
  [ (``Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses,
      [ ``Poincare.D7.Recognition.SphericalPieceRecognition ])
  , (``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses,
      [ ``Poincare.D7.Recognition.SphericalPieceRecognition
      , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2
      , ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypotheses ])
  ]

/-- Claimed closure pairs `(constructor, downstream)`: the constructor must occur in the
downstream's type or transitive proof-term closure. -/
def closurePairs : List (Name × Name) :=
  [ (``Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2,
      ``Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition)
  , (``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of,
      ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2.toRemaining)
  , (``Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient,
      ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.toRemainingV2)
  , (``Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm,
      ``Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.toRemaining)
  , (``Poincare.D12.SurgeryRecognition.iteratedSphereSum,
      ``Poincare.D12.SurgeryRecognition.endGame_finalTopology)
  , (``Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere,
      ``Poincare.D12.SurgeryRecognition.sphereConnectSum_transported)
  , (``Poincare.D12.TensorMaximumBochner.hamiltonField_kernelTangent,
      ``Poincare.D12.TensorMaximumBochner.Audit.d12_hamilton_field_kernel_tangent_audited)
  , (``Poincare.D13.CriticalPathReview.scalar_forward_invariance,
      ``Poincare.D13.CriticalPathReview.scalar_forward_invariance_witness)
  , (``Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff,
      ``Poincare.D13.CriticalPathReview.b1_dimension_one)
  , (``Poincare.D12.TensorMaximumBochner.KernelTangent,
      ``Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff)
  ]

/-! ## The auditor -/

/-- Constants occurring in the *statement* of `n`.  For an inductive type (in particular a
structure) the type former carries no field information, so the type of the constructor
(the field telescope) is used instead. -/
def statementConstants (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    match ci with
    | .inductInfo v =>
      match v.ctors with
      | c :: _ => match env.find? c with
        | some cci => cci.type.getUsedConstants
        | none => #[]
      | [] => ci.type.getUsedConstants
    | _ => ci.type.getUsedConstants

/-- Transitive closure of the constants occurring in the value (proof term) of `n`, with a
fuel bound so that the audit terminates on large environments. -/
def transitiveProofConstants (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut acc : Array Name := #[]
  let mut todo : List Name := [root]
  let mut fuel : Nat := 400000
  while !todo.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let n := todo.head!
    todo := todo.tail!
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      match ci.value? true with
      | none => pure ()
      | some v =>
        for c in v.getUsedConstants do
          if !visited.contains c then
            acc := acc.push c
            todo := c :: todo
  return acc

/-- Fail-closed critical-path audit.  Emits `D13CP_*` lines and raises an elaboration error
unless every check passes. -/
def runCriticalPathAudit : CommandElabM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  for n in mainChainDecls do
    if (env.find? n).isNone then
      failures := failures.push s!"missing declaration {n}"
    else
      IO.println s!"D13CP_DECL\t{n}"
  for (n, reqs) in requiredInType do
    let cs := statementConstants env n
    for r in reqs do
      if cs.contains r then
        IO.println s!"D13CP_REQ_OK\t{n}\t{r}"
      else
        failures := failures.push s!"required input {r} absent from type of {n}"
  for (n, bad) in forbiddenInType do
    let cs := statementConstants env n
    for r in bad do
      if cs.contains r then
        failures := failures.push s!"eliminated input {r} still occurs in type of {n}"
      else
        IO.println s!"D13CP_ELIMINATED_OK\t{n}\t{r}"
  for (ctor, down) in closurePairs do
    let cs := statementConstants env down
    let ps := transitiveProofConstants env down
    let inType := cs.contains ctor
    let inProof := ps.contains ctor
    IO.println s!"D13CP_PAIR\t{ctor}\t{down}\tin_type={inType}\tin_proof={inProof}"
    if !(inType || inProof) then
      failures := failures.push s!"constructor {ctor} not consumed by {down}"
  if !(statementConstants env
      ``Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses).contains
      ``Poincare.Stage6.poincareConjectureTopologicalThree then
    failures := failures.push "top assembly does not mention the Stage6 root target"
  if failures.isEmpty then
    IO.println "D13CP_VERDICT\tPASS"
  else
    IO.println "D13CP_VERDICT\tFAIL"
    for f in failures do
      IO.println s!"D13CP_FAIL\t{f}"
    throwError "D13CriticalPathReview: statement audit FAILED ({failures.size} failures)"

/-- The fail-closed critical-path statement audit. -/
elab "#d13_cp_audit" : command => runCriticalPathAudit

end Poincare.D13.CriticalPathReview

open Poincare.D13.CriticalPathReview

#d13_cp_audit
