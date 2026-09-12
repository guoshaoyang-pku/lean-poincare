/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D11.HeatKernelBridge.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom audit for the D11 heat-kernel bridge

Every declaration of the `Poincare.D11.HeatKernelBridge` development is printed with
`#print axioms` and then re-checked programmatically with `Lean.collectAxioms`. The expected (and
checked) outcome is that every declaration depends only on the three standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound` (or on none at all); in particular no `sorryAx`, no
user axiom, no `unsafe` declaration, no `Lean.ofReduceBool` from `native_decide`, and no
`proof_wanted` may appear.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Lean Elab Command

/-! ## The bridge interface -/

#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.FullInitialCondition
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.WeakInitialCondition
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.WeakInitialCondition.of_full
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toCore
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toCore_fullInitialCondition
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.toHeatKernelData
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.toHeatKernelData_toCore
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.toCore_toHeatKernelData
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.toCore_gaussianUpperBound
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.exists_toCore_eq_iff

/-! ## The Laplacian as a linear map -/

#print axioms Poincare.D11.HeatKernelBridge.contDiffTwoSet
#print axioms Poincare.D11.HeatKernelBridge.contDiffTwoSubmodule
#print axioms Poincare.D11.HeatKernelBridge.mem_contDiffTwoSubmodule
#print axioms Poincare.D11.HeatKernelBridge.laplacianLinearMap
#print axioms Poincare.D11.HeatKernelBridge.laplacianLinearMap_apply_of_contDiff
#print axioms Poincare.D11.HeatKernelBridge.laplacian_comp_sub

/-! ## The explicit Euclidean instance -/

#print axioms Poincare.D11.HeatKernelBridge.flatKernel
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_of_pos
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_of_nonpos
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_eq
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_nonneg
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_pos
#print axioms Poincare.D11.HeatKernelBridge.contDiff_gaussianKernel_translate
#print axioms Poincare.D11.HeatKernelBridge.laplacianLinearMap_flatKernel
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_kernel
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_volume
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_dist
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_dim
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_C_up
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_c_up
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_C_lo
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_c_lo
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_laplacian
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_normalization
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_semigroup
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_heatEquation
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_gaussianUpperBound
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_gaussianLowerBound
#print axioms Poincare.D11.HeatKernelBridge.flat_exists_heatKernelData_iff

/-! ## The weak initial condition -/

#print axioms Poincare.D11.HeatKernelBridge.tendsto_rpow_neg_mul_exp_neg_div
#print axioms Poincare.D11.HeatKernelBridge.tendsto_exp_neg_div
#print axioms Poincare.D11.HeatKernelBridge.tendsto_prefactor_mul_exp_neg_div
#print axioms Poincare.D11.HeatKernelBridge.tendstoUniformlyOn_gaussianKernel_compl
#print axioms Poincare.D11.HeatKernelBridge.integrable_exp_neg_mul_norm_sq
#print axioms Poincare.D11.HeatKernelBridge.prefactor_mul_eight
#print axioms Poincare.D11.HeatKernelBridge.setIntegral_compl_ball_gaussianKernel_le
#print axioms Poincare.D11.HeatKernelBridge.tendsto_setIntegral_compl_ball_gaussianKernel
#print axioms Poincare.D11.HeatKernelBridge.tendsto_setIntegral_ball_gaussianKernel
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_tendsto_integral
#print axioms Poincare.D11.HeatKernelBridge.flatKernel_tendsto_integral_of_hasCompactSupport
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_weakInitialCondition
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_weakInitialCondition_apply

/-! ## The full D7 datum in dimension zero -/

#print axioms Poincare.D11.HeatKernelBridge.volume_euclideanSpace_fin_zero
#print axioms Poincare.D11.HeatKernelBridge.integrable_euclideanSpace_fin_zero
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_fullInitialCondition_zero
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_kernel
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_volume
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_toCore

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations of the D11 heat-kernel bridge. -/
private def bridgeAuditedDeclarations : List Name :=
  [ ``Poincare.D11.HeatKernelBridge.HeatKernelCore,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.FullInitialCondition,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.WeakInitialCondition,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.WeakInitialCondition.of_full,
    ``Poincare.D7.HeatKernel.HeatKernelData.toCore,
    ``Poincare.D7.HeatKernel.HeatKernelData.toCore_fullInitialCondition,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.toHeatKernelData,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.toHeatKernelData_toCore,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.toCore_toHeatKernelData,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.toCore_gaussianUpperBound,
    ``Poincare.D11.HeatKernelBridge.HeatKernelCore.exists_toCore_eq_iff,
    ``Poincare.D11.HeatKernelBridge.contDiffTwoSet,
    ``Poincare.D11.HeatKernelBridge.contDiffTwoSubmodule,
    ``Poincare.D11.HeatKernelBridge.mem_contDiffTwoSubmodule,
    ``Poincare.D11.HeatKernelBridge.laplacianLinearMap,
    ``Poincare.D11.HeatKernelBridge.laplacianLinearMap_apply_of_contDiff,
    ``Poincare.D11.HeatKernelBridge.laplacian_comp_sub,
    ``Poincare.D11.HeatKernelBridge.flatKernel,
    ``Poincare.D11.HeatKernelBridge.flatKernel_of_pos,
    ``Poincare.D11.HeatKernelBridge.flatKernel_of_nonpos,
    ``Poincare.D11.HeatKernelBridge.flatKernel_eq,
    ``Poincare.D11.HeatKernelBridge.flatKernel_nonneg,
    ``Poincare.D11.HeatKernelBridge.flatKernel_pos,
    ``Poincare.D11.HeatKernelBridge.contDiff_gaussianKernel_translate,
    ``Poincare.D11.HeatKernelBridge.laplacianLinearMap_flatKernel,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_kernel,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_volume,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_dist,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_dim,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_C_up,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_c_up,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_C_lo,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_c_lo,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_laplacian,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_normalization,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_semigroup,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_heatEquation,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_gaussianUpperBound,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_gaussianLowerBound,
    ``Poincare.D11.HeatKernelBridge.flat_exists_heatKernelData_iff,
    ``Poincare.D11.HeatKernelBridge.tendsto_rpow_neg_mul_exp_neg_div,
    ``Poincare.D11.HeatKernelBridge.tendsto_exp_neg_div,
    ``Poincare.D11.HeatKernelBridge.tendsto_prefactor_mul_exp_neg_div,
    ``Poincare.D11.HeatKernelBridge.tendstoUniformlyOn_gaussianKernel_compl,
    ``Poincare.D11.HeatKernelBridge.integrable_exp_neg_mul_norm_sq,
    ``Poincare.D11.HeatKernelBridge.prefactor_mul_eight,
    ``Poincare.D11.HeatKernelBridge.setIntegral_compl_ball_gaussianKernel_le,
    ``Poincare.D11.HeatKernelBridge.tendsto_setIntegral_compl_ball_gaussianKernel,
    ``Poincare.D11.HeatKernelBridge.tendsto_setIntegral_ball_gaussianKernel,
    ``Poincare.D11.HeatKernelBridge.flatKernel_tendsto_integral,
    ``Poincare.D11.HeatKernelBridge.flatKernel_tendsto_integral_of_hasCompactSupport,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_weakInitialCondition,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_weakInitialCondition_apply,
    ``Poincare.D11.HeatKernelBridge.volume_euclideanSpace_fin_zero,
    ``Poincare.D11.HeatKernelBridge.integrable_euclideanSpace_fin_zero,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelCore_fullInitialCondition_zero,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_kernel,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_volume,
    ``Poincare.D11.HeatKernelBridge.flatHeatKernelData_zero_toCore ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def bridgeApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in bridgeAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !bridgeApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D11AxiomCheck: PASS — all {bridgeAuditedDeclarations.length} declarations \
      of the D11 heat-kernel bridge depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D11AxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D11AxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
