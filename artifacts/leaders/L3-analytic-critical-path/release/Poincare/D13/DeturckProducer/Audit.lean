/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)

# Axiom audit for the D13 DeturckProducer module set

Every declaration authored by `Poincare.D13.DeturckProducer` is printed with `#print axioms`
and re-checked programmatically with `Lean.collectAxioms`.  The enforced outcome is that
every declaration depends only on the three standard Lean axioms `propext`,
`Classical.choice`, `Quot.sound` (or on none).  The `#print axioms` lines are informational
transcripts; the enforceable fail-closed gate is the `run_cmd` re-check at the end, which
aborts the build on any axiom outside the approved cone.
-/

import Poincare.D13.DeturckProducer.FlatInstance

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
open Poincare.D13.DeturckProducer

/-! ## Downstream-use notes (kernel-checked consumers inside the module set)

* `PicardModel.RicciDeTurckPicardModel.of_metric` consumes the D12 deliverable
  `Poincare.D12.ParabolicLocal.DuhamelSetup` (the semigroup + Banach fixed-point setup);
* `PicardModel.existsUnique_mildSolution_of_model` is literally
  `DuhamelSetup.existsUnique_mildSolution` applied to the produced model;
* `FlatInstance.flatMildSolution_eq_heatMildSolution` consumes the D12
  `gaussianSetup`/`heatMildSolution` (the flat model's mild solution IS the D12 heat mild
  solution — constructed downstream use);
* `PicardModel.ricciFlow_of_model` consumes the D7 proved conversion
  `matrixProblem_deTurckToRicciConversion` and the D13
  `shortTimeRicciFlow_of_splitInputs` assembly;
* the strict-parabolicity certificates consume the D9 index-form identity
  `flowSymbolMat`/`deTurckLinSymbolMat_eq_smul` (the D9 `flowSymbol` transcription) and
  the D13 `euclideanMetricData`-layer correspondence on the flat model;
* the reaction bound theorems consume the coordinate reaction defined in `Reaction`.
-/

/-! ## Axiom transcripts -/

#print axioms Poincare.D13.DeturckProducer.dotProduct_self_nonneg
#print axioms Poincare.D13.DeturckProducer.dotProduct_self_pos_of_ne_zero
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.form_pos
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.det_ne_zero
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.isUnit_det
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.inv_transpose
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.flatSmoothMetric
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.metricSharpMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.covectorNormSqMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.bilinTraceMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.deTurckFieldSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.lieSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.laplacianSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat_apply
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat_eq_smul
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.flowSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat_eq
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat_eq_smul
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_symm
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.lieSymbolMat_symm
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.laplacianSymbolMat_symm
#print axioms Poincare.D13.DeturckProducer.SymbolMatrix.form_cauchySchwarz
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.mul_inv_self
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.inv_mul_self
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.mulVec_inv_mulVec
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.inv_mulVec_eq_zero_iff
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.coercive_covectorNormSqMat
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.covectorNormSqMat_pos
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.symbolLowerBound
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_self_nonneg
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_self_pos_of_ne_zero
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_smul
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.producerStrictParabolic
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.producerStrictParabolic_lower
#print axioms Poincare.D13.DeturckProducer.SmoothMetricData.deTurckSymbolMat_injective
#print axioms Poincare.D13.DeturckProducer.Reaction.christoffelMat
#print axioms Poincare.D13.DeturckProducer.Reaction.christoffelLowered
#print axioms Poincare.D13.DeturckProducer.Reaction.ricciTensorMat
#print axioms Poincare.D13.DeturckProducer.Reaction.lieDerivativeCorrectionMat
#print axioms Poincare.D13.DeturckProducer.Reaction.deTurckReactionMat
#print axioms Poincare.D13.DeturckProducer.Reaction.christoffelMat_zero_of_flat
#print axioms Poincare.D13.DeturckProducer.Reaction.christoffelLowered_zero_of_flat
#print axioms Poincare.D13.DeturckProducer.Reaction.ricciTensorMat_zero_of_flatJets
#print axioms Poincare.D13.DeturckProducer.Reaction.lieDerivativeCorrectionMat_zero_of_flat
#print axioms Poincare.D13.DeturckProducer.Reaction.deTurckReaction_at_initial
#print axioms Poincare.D13.DeturckProducer.Reaction.deTurckReaction_flat_zero
#print axioms Poincare.D13.DeturckProducer.Reaction.abs_ricciEntry_le
#print axioms Poincare.D13.DeturckProducer.Reaction.abs_lieCorrectionEntry_le
#print axioms Poincare.D13.DeturckProducer.Reaction.deTurckReaction_entry_le
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.of_metric
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.existsUnique_mildSolution_of_model
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_duhamel_eq
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_initial
#print axioms Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_continuous
#print axioms Poincare.D13.DeturckProducer.PicardModel.clampC
#print axioms Poincare.D13.DeturckProducer.PicardModel.clampC_mem
#print axioms Poincare.D13.DeturckProducer.PicardModel.clampC_eq_self_of_mem
#print axioms Poincare.D13.DeturckProducer.PicardModel.clampC_lipschitz
#print axioms Poincare.D13.DeturckProducer.PicardModel.truncatedSetup
#print axioms Poincare.D13.DeturckProducer.PicardModel.duhamelMap_congr_of_projection
#print axioms Poincare.D13.DeturckProducer.PicardModel.mildSolution_of_truncated
#print axioms Poincare.D13.DeturckProducer.PicardModel.MildClassicalOutput
#print axioms Poincare.D13.DeturckProducer.PicardModel.deTurckShortTimeExistence_of_classicalOutput
#print axioms Poincare.D13.DeturckProducer.PicardModel.ricciFlow_of_model
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel_duhamel_eq_gaussianSetup
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel_duhamelMap_eq_gaussianSetup
#print axioms Poincare.D13.DeturckProducer.FlatInstance.existsUnique_mildSolution_of_flatModel
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_eq_heatMildSolution
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_duhamel_eq
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_initial
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatCertificate_positive
#print axioms Poincare.D13.DeturckProducer.FlatInstance.euclideanNormSq_eq_dotProduct
#print axioms Poincare.D13.DeturckProducer.FlatInstance.one_inv_mulVec
#print axioms Poincare.D13.DeturckProducer.FlatInstance.flatDeTurckLinSymbol_eq_euclideanNormSq_smul

/-! ## The fail-closed programmatic gate -/

private def deturckProducerAuditedDeclarations : List Name :=
  [ ``Poincare.D13.DeturckProducer.dotProduct_self_nonneg,
    ``Poincare.D13.DeturckProducer.dotProduct_self_pos_of_ne_zero,
    ``Poincare.D13.DeturckProducer.SmoothMetricData,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.form_pos,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.det_ne_zero,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.isUnit_det,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.inv_transpose,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.flatSmoothMetric,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.metricSharpMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.covectorNormSqMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.bilinTraceMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.deTurckFieldSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.lieSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.laplacianSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat_apply,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_sub_half_lieSymbolMat_eq_smul,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.flowSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat_eq,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.deTurckLinSymbolMat_eq_smul,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.ricciSymbolMat_symm,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.lieSymbolMat_symm,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.laplacianSymbolMat_symm,
    ``Poincare.D13.DeturckProducer.SymbolMatrix.form_cauchySchwarz,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.mul_inv_self,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.inv_mul_self,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.mulVec_inv_mulVec,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.inv_mulVec_eq_zero_iff,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.coercive_covectorNormSqMat,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.covectorNormSqMat_pos,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.symbolLowerBound,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_self_nonneg,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_self_pos_of_ne_zero,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.bilinPairingMat_smul,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.producerStrictParabolic,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.producerStrictParabolic_lower,
    ``Poincare.D13.DeturckProducer.SmoothMetricData.deTurckSymbolMat_injective,
    ``Poincare.D13.DeturckProducer.Reaction.christoffelMat,
    ``Poincare.D13.DeturckProducer.Reaction.christoffelLowered,
    ``Poincare.D13.DeturckProducer.Reaction.ricciTensorMat,
    ``Poincare.D13.DeturckProducer.Reaction.lieDerivativeCorrectionMat,
    ``Poincare.D13.DeturckProducer.Reaction.deTurckReactionMat,
    ``Poincare.D13.DeturckProducer.Reaction.christoffelMat_zero_of_flat,
    ``Poincare.D13.DeturckProducer.Reaction.christoffelLowered_zero_of_flat,
    ``Poincare.D13.DeturckProducer.Reaction.ricciTensorMat_zero_of_flatJets,
    ``Poincare.D13.DeturckProducer.Reaction.lieDerivativeCorrectionMat_zero_of_flat,
    ``Poincare.D13.DeturckProducer.Reaction.deTurckReaction_at_initial,
    ``Poincare.D13.DeturckProducer.Reaction.deTurckReaction_flat_zero,
    ``Poincare.D13.DeturckProducer.Reaction.abs_ricciEntry_le,
    ``Poincare.D13.DeturckProducer.Reaction.abs_lieCorrectionEntry_le,
    ``Poincare.D13.DeturckProducer.Reaction.deTurckReaction_entry_le,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.of_metric,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.existsUnique_mildSolution_of_model,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_duhamel_eq,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_initial,
    ``Poincare.D13.DeturckProducer.PicardModel.RicciDeTurckPicardModel.mildSolution_of_model_continuous,
    ``Poincare.D13.DeturckProducer.PicardModel.clampC,
    ``Poincare.D13.DeturckProducer.PicardModel.clampC_mem,
    ``Poincare.D13.DeturckProducer.PicardModel.clampC_eq_self_of_mem,
    ``Poincare.D13.DeturckProducer.PicardModel.clampC_lipschitz,
    ``Poincare.D13.DeturckProducer.PicardModel.truncatedSetup,
    ``Poincare.D13.DeturckProducer.PicardModel.duhamelMap_congr_of_projection,
    ``Poincare.D13.DeturckProducer.PicardModel.mildSolution_of_truncated,
    ``Poincare.D13.DeturckProducer.PicardModel.MildClassicalOutput,
    ``Poincare.D13.DeturckProducer.PicardModel.deTurckShortTimeExistence_of_classicalOutput,
    ``Poincare.D13.DeturckProducer.PicardModel.ricciFlow_of_model,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel_duhamel_eq_gaussianSetup,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatPicardModel_duhamelMap_eq_gaussianSetup,
    ``Poincare.D13.DeturckProducer.FlatInstance.existsUnique_mildSolution_of_flatModel,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_eq_heatMildSolution,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_duhamel_eq,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatMildSolution_initial,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatCertificate_positive,
    ``Poincare.D13.DeturckProducer.FlatInstance.euclideanNormSq_eq_dotProduct,
    ``Poincare.D13.DeturckProducer.FlatInstance.one_inv_mulVec,
    ``Poincare.D13.DeturckProducer.FlatInstance.flatDeTurckLinSymbol_eq_euclideanNormSq_smul ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def deturckProducerApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in deturckProducerAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !deturckProducerApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"DeturckProducerAxiomCheck: PASS — all {deturckProducerAuditedDeclarations.length} declarations \
      of the D13 DeturckProducer module set depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"DeturckProducerAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "DeturckProducerAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
