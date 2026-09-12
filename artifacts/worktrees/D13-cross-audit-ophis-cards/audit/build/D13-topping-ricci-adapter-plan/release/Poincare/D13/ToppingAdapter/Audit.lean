/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)

# Axiom audit for the D13 Topping adapter module set

Every declaration authored by `Poincare.D13.ToppingAdapter` is printed with `#print axioms`
and re-checked programmatically with `Lean.collectAxioms`.  The expected (and enforced)
outcome is that every declaration depends only on the three standard Lean axioms `propext`,
`Classical.choice`, `Quot.sound` (or on none); in particular no `sorryAx`, no user axiom, no
`unsafe`, no `Lean.ofReduceBool` from `native_decide`, and no `proof_wanted` may appear.  The
`#print axioms` lines are informational transcripts; the enforceable fail-closed gate is the
programmatic `run_cmd` re-check at the end, which aborts the build on any axiom outside the
approved cone.

The upstream transcriptions (the Topping `MaximumPrinciple/Core` theorems, the
`ParabolicPDE/Scalar` definitions and theorems) are re-proved locally from mathlib; no
upstream axiom is imported (the snapshot survey found 0 `sorry`/`admit`/`axiom` declarations
in the quoted upstream files).  All local proofs are complete.
-/

import Poincare.D13.ToppingAdapter.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
open Poincare.D13.ToppingAdapter

/-! ## Downstream-use checks (kernel-checked consumers of the adapter theorems) -/

open MeasureTheory Filter
open scoped Topology

/-! ## Downstream-use notes (the uses are inside the module set itself)

The adapter theorems are consumed by the module set itself and by the imported local layers:

* `Slab.continuousHeatMaximumPrinciple_of_topping` consumes the transcribed Topping
  compact-space core (`Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'`) and discharges the
  mathematical content of the D2/D7 statement-only interface I2 for classical solutions;
* `Volume.hasVolumeDerivativeOn_of_weightedDensity_local` consumes the D12 deliverable
  `Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight` (downstream use of
  the D12-entropy-variation result in the upstream Topping statement's form);
* `Scalar.flowSymbol_eq_neg_heatPrincipalSymbol` consumes the D9 deliverable
  `Poincare.Longrun.DeTurck.flowSymbol` (downstream use of the D9 symbol computation);
* `ShortTime.shortTimeRicciFlow_of_splitInputs` consumes the D7 interfaces
  `DeTurckShortTimeExistence` / `DeTurckToRicciConversion` exactly as the upstream Topping
  split theorem consumes `RicciDeTurckLocalSolution` / `HamiltonGaugeTransport`;
* the D7 matrix-model gauge conversion is the *proved* `gaugeConversion` antecedent of
  `SplitShortTimeInputs` (`Poincare.D7.ShortTime.matrixProblem_deTurckToRicciConversion`); the
  analytic antecedent remains the named missing input, recorded in the D13 result card.
-/

/-! ## Transcribed upstream definitions and adapter theorems -/

#print axioms Poincare.D13.ToppingAdapter.Core.isLocalMaxOn_of_isMaxOn
#print axioms Poincare.D13.ToppingAdapter.Core.time_deriv_nonneg_of_isMaxOn_Icc
#print axioms Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le_of_pos
#print axioms Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le
#print axioms Poincare.D13.ToppingAdapter.Core.exists_nonneg_reaction_bound_on_rectangle
#print axioms Poincare.D13.ToppingAdapter.Core.exists_common_value_interval
#print axioms Poincare.D13.ToppingAdapter.Core.le_ode_solution_of_forall_isMax_time_deriv_le_of_pos
#print axioms Poincare.D13.ToppingAdapter.Core.le_ode_solution_of_forall_isMax_time_deriv_le
#print axioms Poincare.D13.ToppingAdapter.Core.nonneg_of_forall_isMin_time_deriv_ge
#print axioms Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'
#print axioms Poincare.D13.ToppingAdapter.Slab.deriv_deriv_nonpos_of_isLocalMax
#print axioms Poincare.D13.ToppingAdapter.Slab.iteratedDeriv_two_nonpos_of_isLocalMax
#print axioms Poincare.D13.ToppingAdapter.Slab.SlabRegularity
#print axioms Poincare.D13.ToppingAdapter.Slab.slab_nonpos_of_lt
#print axioms Poincare.D13.ToppingAdapter.Slab.continuousHeatMaximumPrinciple_of_topping
#print axioms Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderCoefficients
#print axioms Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderJet
#print axioms Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol
#print axioms Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderCoefficients.principalSymbol
#print axioms Poincare.D13.ToppingAdapter.Scalar.IsPositiveDefinite
#print axioms Poincare.D13.ToppingAdapter.Scalar.PointwiseParabolic
#print axioms Poincare.D13.ToppingAdapter.Scalar.UniformlyParabolic
#print axioms Poincare.D13.ToppingAdapter.Scalar.pointwiseParabolic_iff_symbol_positive
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol_zero
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol_add
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol_smul
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol_one
#print axioms Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq_nonneg
#print axioms Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq_pos
#print axioms Poincare.D13.ToppingAdapter.Scalar.uniformlyParabolic_pointwiseParabolic
#print axioms Poincare.D13.ToppingAdapter.Scalar.heatCoefficients
#print axioms Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_principalSymbol
#print axioms Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_uniformlyParabolic
#print axioms Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_pointwiseParabolic
#print axioms Poincare.D13.ToppingAdapter.Scalar.symbol_congruence
#print axioms Poincare.D13.ToppingAdapter.Scalar.IsPositiveDefinite.congruence
#print axioms Poincare.D13.ToppingAdapter.Scalar.euclideanMetricData
#print axioms Poincare.D13.ToppingAdapter.Scalar.covectorOf
#print axioms Poincare.D13.ToppingAdapter.Scalar.covectorNormSq_euclidean_eq_euclideanNormSq
#print axioms Poincare.D13.ToppingAdapter.Scalar.heatPrincipalSymbol_eq_localLaplacianCoeff
#print axioms Poincare.D13.ToppingAdapter.Scalar.flowSymbol_eq_neg_heatPrincipalSymbol
#print axioms Poincare.D13.ToppingAdapter.ShortTime.SplitShortTimeInputs
#print axioms Poincare.D13.ToppingAdapter.ShortTime.shortTimeRicciFlow_of_splitInputs
#print axioms Poincare.D13.ToppingAdapter.ShortTime.bilinPairing
#print axioms Poincare.D13.ToppingAdapter.ShortTime.bilinPairing_pos_of_ne_zero
#print axioms Poincare.D13.ToppingAdapter.ShortTime.localDeTurckStrictParabolic
#print axioms Poincare.D13.ToppingAdapter.ShortTime.deTurckLinearisationSymbol_strictParabolic_heatCoefficients
#print axioms Poincare.D13.ToppingAdapter.Volume.HasVolumeDerivativeOn
#print axioms Poincare.D13.ToppingAdapter.Volume.hasVolumeDerivativeOn_of_weightedDensity_local

/-! ## The fail-closed programmatic gate -/

private def d13ToppingAuditedDeclarations : List Name :=
  [ ``Poincare.D13.ToppingAdapter.Core.isLocalMaxOn_of_isMaxOn,
    ``Poincare.D13.ToppingAdapter.Core.time_deriv_nonneg_of_isMaxOn_Icc,
    ``Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le_of_pos,
    ``Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le,
    ``Poincare.D13.ToppingAdapter.Core.exists_nonneg_reaction_bound_on_rectangle,
    ``Poincare.D13.ToppingAdapter.Core.exists_common_value_interval,
    ``Poincare.D13.ToppingAdapter.Core.le_ode_solution_of_forall_isMax_time_deriv_le_of_pos,
    ``Poincare.D13.ToppingAdapter.Core.le_ode_solution_of_forall_isMax_time_deriv_le,
    ``Poincare.D13.ToppingAdapter.Core.nonneg_of_forall_isMin_time_deriv_ge,
    ``Poincare.D13.ToppingAdapter.Core.nonpos_of_forall_isMax_time_deriv_le_of_pos',
    ``Poincare.D13.ToppingAdapter.Slab.deriv_deriv_nonpos_of_isLocalMax,
    ``Poincare.D13.ToppingAdapter.Slab.iteratedDeriv_two_nonpos_of_isLocalMax,
    ``Poincare.D13.ToppingAdapter.Slab.SlabRegularity,
    ``Poincare.D13.ToppingAdapter.Slab.slab_nonpos_of_lt,
    ``Poincare.D13.ToppingAdapter.Slab.continuousHeatMaximumPrinciple_of_topping,
    ``Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderCoefficients,
    ``Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderJet,
    ``Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol,
    ``Poincare.D13.ToppingAdapter.Scalar.ScalarSecondOrderCoefficients.principalSymbol,
    ``Poincare.D13.ToppingAdapter.Scalar.IsPositiveDefinite,
    ``Poincare.D13.ToppingAdapter.Scalar.PointwiseParabolic,
    ``Poincare.D13.ToppingAdapter.Scalar.UniformlyParabolic,
    ``Poincare.D13.ToppingAdapter.Scalar.pointwiseParabolic_iff_symbol_positive,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol_zero,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol_add,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol_smul,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol_one,
    ``Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq_nonneg,
    ``Poincare.D13.ToppingAdapter.Scalar.euclideanNormSq_pos,
    ``Poincare.D13.ToppingAdapter.Scalar.uniformlyParabolic_pointwiseParabolic,
    ``Poincare.D13.ToppingAdapter.Scalar.heatCoefficients,
    ``Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_principalSymbol,
    ``Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_uniformlyParabolic,
    ``Poincare.D13.ToppingAdapter.Scalar.heatCoefficients_pointwiseParabolic,
    ``Poincare.D13.ToppingAdapter.Scalar.symbol_congruence,
    ``Poincare.D13.ToppingAdapter.Scalar.IsPositiveDefinite.congruence,
    ``Poincare.D13.ToppingAdapter.Scalar.euclideanMetricData,
    ``Poincare.D13.ToppingAdapter.Scalar.covectorOf,
    ``Poincare.D13.ToppingAdapter.Scalar.covectorNormSq_euclidean_eq_euclideanNormSq,
    ``Poincare.D13.ToppingAdapter.Scalar.heatPrincipalSymbol_eq_localLaplacianCoeff,
    ``Poincare.D13.ToppingAdapter.Scalar.flowSymbol_eq_neg_heatPrincipalSymbol,
    ``Poincare.D13.ToppingAdapter.ShortTime.SplitShortTimeInputs,
    ``Poincare.D13.ToppingAdapter.ShortTime.shortTimeRicciFlow_of_splitInputs,
    ``Poincare.D13.ToppingAdapter.ShortTime.bilinPairing,
    ``Poincare.D13.ToppingAdapter.ShortTime.bilinPairing_pos_of_ne_zero,
    ``Poincare.D13.ToppingAdapter.ShortTime.localDeTurckStrictParabolic,
    ``Poincare.D13.ToppingAdapter.ShortTime.deTurckLinearisationSymbol_strictParabolic_heatCoefficients,
    ``Poincare.D13.ToppingAdapter.Volume.HasVolumeDerivativeOn,
    ``Poincare.D13.ToppingAdapter.Volume.hasVolumeDerivativeOn_of_weightedDensity_local ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def d13ToppingApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in d13ToppingAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !d13ToppingApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D13ToppingAdapterAxiomCheck: PASS — all {d13ToppingAuditedDeclarations.length} declarations \
      of the D13 Topping adapter module set depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D13ToppingAdapterAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D13ToppingAdapterAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
