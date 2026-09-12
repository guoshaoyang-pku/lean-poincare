/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom audit for the D12 heat-semigroup development

Every declaration of the `Poincare.D12.HeatSemigroup` development is printed with
`#print axioms`, and then the same cones are checked programmatically with
`Lean.collectAxioms`. The expected (and checked) outcome is that every declaration depends
only on the three standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` (or on none
at all); in particular no `sorryAx`, no user axiom, no `unsafe` declaration, no
`Lean.ofReduceBool` from `native_decide`, and no `proof_wanted` may appear. The check is
fail-closed: any declaration outside the approved cone makes this module fail to compile.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file or in
the files it imports.
-/

open Lean Elab Command

namespace Poincare.D12.HeatSemigroup.AxiomAudit

/-! ## Per-declaration `#print axioms` -/

#print axioms Poincare.D12.HeatSemigroup.heatOperator
#print axioms Poincare.D12.HeatSemigroup.heatOperator_zero
#print axioms Poincare.D12.HeatSemigroup.heatOperator_add_of_integrable
#print axioms Poincare.D12.HeatSemigroup.heatOperator_smul
#print axioms Poincare.D12.HeatSemigroup.heatOperator_eq_integral_flatKernel
#print axioms Poincare.D12.HeatSemigroup.heatOperator_eq_integral_sub
#print axioms Poincare.D12.HeatSemigroup.integrable_gaussianKernel_sub
#print axioms Poincare.D12.HeatSemigroup.integral_gaussianKernel_sub
#print axioms Poincare.D12.HeatSemigroup.integrable_gaussianKernel_sub_left
#print axioms Poincare.D12.HeatSemigroup.integral_gaussianKernel_sub_left
#print axioms Poincare.D12.HeatSemigroup.gaussianKernel_sub_le_prefactor
#print axioms Poincare.D12.HeatSemigroup.heatOperator_nonneg
#print axioms Poincare.D12.HeatSemigroup.heatOperator_norm_le_of_forall_norm_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_abs_le_of_forall_abs_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_norm_le_of_forall_norm_le'
#print axioms Poincare.D12.HeatSemigroup.enorm_mul_of_nonneg_left
#print axioms Poincare.D12.HeatSemigroup.lintegral_enorm_gaussianKernel_sub_left
#print axioms Poincare.D12.HeatSemigroup.heatOperator_enorm_le_lintegral_enorm
#print axioms Poincare.D12.HeatSemigroup.lintegral_enorm_heatKernelProduct_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_lintegral_enorm_le
#print axioms Poincare.D12.HeatSemigroup.heatKernelProduct_integrable
#print axioms Poincare.D12.HeatSemigroup.heatOperator_integrable
#print axioms Poincare.D12.HeatSemigroup.heatOperator_integral_norm_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_integral_eq_integral
#print axioms Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM
#print axioms Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM_apply
#print axioms Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM
#print axioms Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_apply
#print axioms Poincare.D12.HeatSemigroup.hasFDerivAt_gaussianKernel_mul
#print axioms Poincare.D12.HeatSemigroup.continuous_gaussianKernelFDerivCLM
#print axioms Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM_norm_le
#print axioms Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_norm_le
#print axioms Poincare.D12.HeatSemigroup.norm_le_one_add_norm_sq
#print axioms Poincare.D12.HeatSemigroup.norm_sub_sq_ge_half
#print axioms Poincare.D12.HeatSemigroup.one_add_norm_sq_mul_exp_neg_le
#print axioms Poincare.D12.HeatSemigroup.heatSmoothingBoundConst
#print axioms Poincare.D12.HeatSemigroup.heatSmoothingBoundConst_nonneg
#print axioms Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_bound_ball
#print axioms Poincare.D12.HeatSemigroup.integrable_heatSmoothingBound
#print axioms Poincare.D12.HeatSemigroup.hasFDerivAt_heatOperator
#print axioms Poincare.D12.HeatSemigroup.differentiable_heatOperator
#print axioms Poincare.D12.HeatSemigroup.continuous_heatOperator
#print axioms Poincare.D12.HeatSemigroup.fderiv_heatOperator
#print axioms Poincare.D12.HeatSemigroup.heatOperatorBCF
#print axioms Poincare.D12.HeatSemigroup.heatOperatorBCF_apply
#print axioms Poincare.D12.HeatSemigroup.heatOperatorBCF_norm_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero
#print axioms Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero_of_hasCompactSupport
#print axioms Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero_conv
#print axioms Poincare.D12.HeatSemigroup.StrongContinuityBoundedContinuousObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldHeatKernelCoreObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldLinfContractionObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldL1ContractionObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldSmoothingObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldStrongContinuityObligation
#print axioms Poincare.D12.HeatSemigroup.CompactManifoldSemigroupObligation
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_pos
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_integral
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_norm_le
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1
#print axioms Poincare.D12.HeatSemigroup.heatSemigroupKernelProduct_integrable
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_fun
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_swap
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_integral_norm_eq_zero
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded_fun
#print axioms Poincare.D12.HeatSemigroup.heatOperatorBCF_comp
#print axioms Poincare.D12.HeatSemigroup.heatOperatorBCF_comp_swap
#print axioms Poincare.D12.HeatSemigroup.continuousAt_gaussianKernel_time
#print axioms Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound
#print axioms Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound_le
#print axioms Poincare.D12.HeatSemigroup.tendsto_integral_abs_gaussianKernel_sub_of_seq
#print axioms Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations of the D12 heat-semigroup development. -/
private def heatSemigroupAuditedDeclarations : List Name :=
  [ ``Poincare.D12.HeatSemigroup.heatOperator,
    ``Poincare.D12.HeatSemigroup.heatOperator_zero,
    ``Poincare.D12.HeatSemigroup.heatOperator_add_of_integrable,
    ``Poincare.D12.HeatSemigroup.heatOperator_smul,
    ``Poincare.D12.HeatSemigroup.heatOperator_eq_integral_flatKernel,
    ``Poincare.D12.HeatSemigroup.heatOperator_eq_integral_sub,
    ``Poincare.D12.HeatSemigroup.integrable_gaussianKernel_sub,
    ``Poincare.D12.HeatSemigroup.integral_gaussianKernel_sub,
    ``Poincare.D12.HeatSemigroup.integrable_gaussianKernel_sub_left,
    ``Poincare.D12.HeatSemigroup.integral_gaussianKernel_sub_left,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_sub_le_prefactor,
    ``Poincare.D12.HeatSemigroup.heatOperator_nonneg,
    ``Poincare.D12.HeatSemigroup.heatOperator_norm_le_of_forall_norm_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_abs_le_of_forall_abs_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_norm_le_of_forall_norm_le',
    ``Poincare.D12.HeatSemigroup.enorm_mul_of_nonneg_left,
    ``Poincare.D12.HeatSemigroup.lintegral_enorm_gaussianKernel_sub_left,
    ``Poincare.D12.HeatSemigroup.heatOperator_enorm_le_lintegral_enorm,
    ``Poincare.D12.HeatSemigroup.lintegral_enorm_heatKernelProduct_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_lintegral_enorm_le,
    ``Poincare.D12.HeatSemigroup.heatKernelProduct_integrable,
    ``Poincare.D12.HeatSemigroup.heatOperator_integrable,
    ``Poincare.D12.HeatSemigroup.heatOperator_integral_norm_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_integral_eq_integral,
    ``Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM,
    ``Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM_apply,
    ``Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM,
    ``Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_apply,
    ``Poincare.D12.HeatSemigroup.hasFDerivAt_gaussianKernel_mul,
    ``Poincare.D12.HeatSemigroup.continuous_gaussianKernelFDerivCLM,
    ``Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM_norm_le,
    ``Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_norm_le,
    ``Poincare.D12.HeatSemigroup.norm_le_one_add_norm_sq,
    ``Poincare.D12.HeatSemigroup.norm_sub_sq_ge_half,
    ``Poincare.D12.HeatSemigroup.one_add_norm_sq_mul_exp_neg_le,
    ``Poincare.D12.HeatSemigroup.heatSmoothingBoundConst,
    ``Poincare.D12.HeatSemigroup.heatSmoothingBoundConst_nonneg,
    ``Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_bound_ball,
    ``Poincare.D12.HeatSemigroup.integrable_heatSmoothingBound,
    ``Poincare.D12.HeatSemigroup.hasFDerivAt_heatOperator,
    ``Poincare.D12.HeatSemigroup.differentiable_heatOperator,
    ``Poincare.D12.HeatSemigroup.continuous_heatOperator,
    ``Poincare.D12.HeatSemigroup.fderiv_heatOperator,
    ``Poincare.D12.HeatSemigroup.heatOperatorBCF,
    ``Poincare.D12.HeatSemigroup.heatOperatorBCF_apply,
    ``Poincare.D12.HeatSemigroup.heatOperatorBCF_norm_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero,
    ``Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero_of_hasCompactSupport,
    ``Poincare.D12.HeatSemigroup.heatOperator_tendsto_nhdsGT_zero_conv,
    ``Poincare.D12.HeatSemigroup.StrongContinuityBoundedContinuousObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldHeatKernelCoreObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldLinfContractionObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldL1ContractionObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldSmoothingObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldStrongContinuityObligation,
    ``Poincare.D12.HeatSemigroup.CompactManifoldSemigroupObligation,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_pos,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_integral,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_norm_le,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1,
    ``Poincare.D12.HeatSemigroup.heatSemigroupKernelProduct_integrable,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_fun,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_swap,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_integral_norm_eq_zero,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded,
    ``Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded_fun,
    ``Poincare.D12.HeatSemigroup.heatOperatorBCF_comp,
    ``Poincare.D12.HeatSemigroup.heatOperatorBCF_comp_swap,
    ``Poincare.D12.HeatSemigroup.continuousAt_gaussianKernel_time,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound_le,
    ``Poincare.D12.HeatSemigroup.tendsto_integral_abs_gaussianKernel_sub_of_seq,
    ``Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def heatSemigroupApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in heatSemigroupAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !heatSemigroupApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D12AxiomCheck: PASS — all {heatSemigroupAuditedDeclarations.length} declarations \
      of the D12 heat-semigroup development depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D12AxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D12AxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"

end Poincare.D12.HeatSemigroup.AxiomAudit
