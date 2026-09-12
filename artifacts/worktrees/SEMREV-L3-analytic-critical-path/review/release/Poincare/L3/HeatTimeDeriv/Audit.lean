/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (L3-analytic-critical-path)

# Fail-closed axiom audit for the L3 heat-time-derivative development

Every declaration authored by `Poincare.L3.HeatTimeDeriv` is printed with `#print axioms` and
re-checked programmatically with `Lean.collectAxioms`.  The enforced outcome is that every
authored declaration depends only on the three standard Lean axioms `propext`,
`Classical.choice`, `Quot.sound` (or on none).  The `#print axioms` lines are informational
transcripts; the enforceable fail-closed gate is the `run_cmd` re-check at the end, which aborts
the build on any axiom outside the approved cone.

The same check is applied to the load-bearing snapshot declarations that the new modules consume
(the D12 heat convolution and its strong continuity, the D10 kernel identities, and the D12
obligation `mildToClassicalBridge` that this task discharges).

The negative control (`../audit-evidence/negcontrol/L3NegControl.lean`, outside the release
package) declares an unapproved axiom and is rejected by the same predicate with exit code 1; it
is deliberately not part of this module or of the package.
-/

import Poincare.L3.HeatTimeDeriv.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-! ## Downstream-use notes (kernel-checked consumers of the delivered lemmas)

* `mildToClassicalBridge_holds n` has the *exact* type `Poincare.D12.ParabolicLocal.mildToClassicalBridge n`
  for every `n`, so it is a drop-in inhabitant of the D12 obligation (checked below by
  type ascription, not by prose);
* `hasDerivAt_heatConv_apply` consumes the D10 kernel identity `hasDerivAt_gaussianKernel` and the
  D12 heat-convolution API (`heatConv_apply`, `heatConv_tendsto_self_BUC`);
* `hasDerivAt_heatConv_apply_kernelLaplacian` consumes `laplacian_gaussianKernel` (D10);
* `heatConv_classicalHeatSolution` packages the orbit as a `KernelClassicalHeatSolution`, whose
  `isSolution` field is the bridge and whose `initial` field is D12's `heatConv_tendsto_self_BUC`;
* `mildToClassicalBridge_of_uniform` consumes the residual `UniformMildToClassicalBridge` and
  derives the discharged obligation from it, certifying the residual as a genuine strengthening.
-/

/-! ## Axiom transcripts -/

#print axioms Poincare.L3.HeatTimeDeriv.timeCoeff
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivKernel
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivBound
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivBound_nonneg
#print axioms Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le
#print axioms Poincare.L3.HeatTimeDeriv.normSq_mul_exp_neg_le
#print axioms Poincare.L3.HeatTimeDeriv.integrable_gaussianKernel_mul_normSq
#print axioms Poincare.L3.HeatTimeDeriv.integrable_gaussianKernel_mul_coeff
#print axioms Poincare.L3.HeatTimeDeriv.integrable_timeDerivBound
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator
#print axioms Poincare.L3.HeatTimeDeriv.heatOperator_time_deriv_eq_kernelLaplacian
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator_kernelLaplacian
#print axioms Poincare.L3.HeatTimeDeriv.heatOperator_const
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator_const
#print axioms Poincare.L3.HeatTimeDeriv.integral_timeDerivKernel_mul_const
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivIntegral
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply_kernelLaplacian
#print axioms Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_pointwise
#print axioms Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds
#print axioms Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_const
#print axioms Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution
#print axioms Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution
#print axioms Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge
#print axioms Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_of_uniform
#print axioms Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge
#print axioms Poincare.L3.HeatTimeDeriv.integrable_timeDerivBound_one
#print axioms Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le_normalized
#print axioms Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le_normalized_self
#print axioms Poincare.L3.HeatTimeDeriv.continuous_timeDerivKernel
#print axioms Poincare.L3.HeatTimeDeriv.integrable_abs_timeDerivKernel_sub
#print axioms Poincare.L3.HeatTimeDeriv.tendsto_integral_abs_timeDerivKernel_sub
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivIntegral_eq_translate
#print axioms Poincare.L3.HeatTimeDeriv.integrable_timeDerivKernel_mul
#print axioms Poincare.L3.HeatTimeDeriv.abs_timeDerivIntegral_sub_le
#print axioms Poincare.L3.HeatTimeDeriv.exists_slope_eq_timeDerivIntegral
#print axioms Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds
#print axioms Poincare.L3.HeatTimeDeriv.continuous_timeDerivIntegral
#print axioms Poincare.L3.HeatTimeDeriv.norm_timeDerivIntegral_le
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivBCF
#print axioms Poincare.L3.HeatTimeDeriv.timeDerivBCF_apply
#print axioms Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF

/-! ## Load-bearing snapshot declarations consumed -/

#print axioms Poincare.D12.ParabolicLocal.mildToClassicalBridge
#print axioms Poincare.D12.ParabolicLocal.heatConv
#print axioms Poincare.D12.ParabolicLocal.heatConv_apply
#print axioms Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC
#print axioms Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel
#print axioms Poincare.D12.HeatSemigroup.heatOperator
#print axioms Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound
#print axioms Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound_le

/-! ## Type-level downstream use (the D12 obligation name is inhabited exactly) -/

#check (Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds 3 :
  Poincare.D12.ParabolicLocal.mildToClassicalBridge 3)
#check (fun (f : Poincare.D12.ParabolicLocal.BUCn 2) =>
  (Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution 2 f).isSolution)
#check (fun (f : Poincare.D12.ParabolicLocal.BUCn 1)
  (x : EuclideanSpace ℝ (Fin 1)) =>
  Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply (t := (1 : ℝ)) 1 (by norm_num) f x)
#check (fun (n : ℕ) => Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_of_uniform n
  (Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds n))
#check (fun (n : ℕ) (f : Poincare.D12.ParabolicLocal.BUCn n) =>
  Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF n (by norm_num : (0 : ℝ) < 1) f)

/-- The declarations audited by this module: every authored declaration of the L3
heat-time-derivative development, plus the load-bearing snapshot declarations it consumes. -/
def l3HeatTimeDerivAuditedDeclarations : List Name :=
  [ ``Poincare.L3.HeatTimeDeriv.timeCoeff,
    ``Poincare.L3.HeatTimeDeriv.timeDerivKernel,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBound,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBound_nonneg,
    ``Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le,
    ``Poincare.L3.HeatTimeDeriv.normSq_mul_exp_neg_le,
    ``Poincare.L3.HeatTimeDeriv.integrable_gaussianKernel_mul_normSq,
    ``Poincare.L3.HeatTimeDeriv.integrable_gaussianKernel_mul_coeff,
    ``Poincare.L3.HeatTimeDeriv.integrable_timeDerivBound,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator,
    ``Poincare.L3.HeatTimeDeriv.heatOperator_time_deriv_eq_kernelLaplacian,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator_kernelLaplacian,
    ``Poincare.L3.HeatTimeDeriv.heatOperator_const,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatOperator_const,
    ``Poincare.L3.HeatTimeDeriv.integral_timeDerivKernel_mul_const,
    ``Poincare.L3.HeatTimeDeriv.timeDerivIntegral,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_apply_kernelLaplacian,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_pointwise,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_const,
    ``Poincare.L3.HeatTimeDeriv.KernelClassicalHeatSolution,
    ``Poincare.L3.HeatTimeDeriv.heatConv_classicalHeatSolution,
    ``Poincare.L3.HeatTimeDeriv.UniformMildToClassicalBridge,
    ``Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_of_uniform,
    ``Poincare.L3.HeatTimeDeriv.SpatialLaplacianBridge,
    ``Poincare.L3.HeatTimeDeriv.integrable_timeDerivBound_one,
    ``Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le_normalized,
    ``Poincare.L3.HeatTimeDeriv.norm_timeDerivKernel_le_normalized_self,
    ``Poincare.L3.HeatTimeDeriv.continuous_timeDerivKernel,
    ``Poincare.L3.HeatTimeDeriv.integrable_abs_timeDerivKernel_sub,
    ``Poincare.L3.HeatTimeDeriv.tendsto_integral_abs_timeDerivKernel_sub,
    ``Poincare.L3.HeatTimeDeriv.timeDerivIntegral_eq_translate,
    ``Poincare.L3.HeatTimeDeriv.integrable_timeDerivKernel_mul,
    ``Poincare.L3.HeatTimeDeriv.abs_timeDerivIntegral_sub_le,
    ``Poincare.L3.HeatTimeDeriv.exists_slope_eq_timeDerivIntegral,
    ``Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds,
    ``Poincare.L3.HeatTimeDeriv.continuous_timeDerivIntegral,
    ``Poincare.L3.HeatTimeDeriv.norm_timeDerivIntegral_le,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBCF,
    ``Poincare.L3.HeatTimeDeriv.timeDerivBCF_apply,
    ``Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF,
    ``Poincare.D12.ParabolicLocal.mildToClassicalBridge,
    ``Poincare.D12.ParabolicLocal.heatConv,
    ``Poincare.D12.ParabolicLocal.heatConv_apply,
    ``Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC,
    ``Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel,
    ``Poincare.D12.HeatSemigroup.heatOperator,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound,
    ``Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound_le ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def l3HeatTimeDerivApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  let mut missing : Array Name := #[]
  for d in l3HeatTimeDerivAuditedDeclarations do
    if (← getEnv).contains d then
      let axs ← Lean.collectAxioms d
      let bad := axs.toList.filter (fun a => !l3HeatTimeDerivApprovedAxioms.contains a)
      if !bad.isEmpty then
        unapprovedTotal := unapprovedTotal.push (d, bad)
    else
      missing := missing.push d
  if !missing.isEmpty then
    for d in missing do
      logError m!"L3HeatTimeDerivAxiomCheck: audited declaration {d} is absent from the environment"
    throwError "L3HeatTimeDerivAxiomCheck: FAIL — {missing.size} declared name(s) not found"
  if unapprovedTotal.isEmpty then
    logInfo m!"L3HeatTimeDerivAxiomCheck: PASS — all \
      {l3HeatTimeDerivAuditedDeclarations.length} audited declarations depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"L3HeatTimeDerivAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "L3HeatTimeDerivAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
