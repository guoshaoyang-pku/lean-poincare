/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axiom audit for the Euclidean heat kernel development

Every declaration of the `Poincare.D10.HeatKernelEuclidean` development is
printed with `#print axioms`, and then the same cones are checked
programmatically with `Lean.collectAxioms`.  The expected (and checked) outcome
is that every declaration depends only on the three standard Lean axioms

`propext`, `Classical.choice`, `Quot.sound`

(or on none at all); in particular no `sorryAx`, no user axiom, no `unsafe`
declaration, no `Lean.ofReduceBool` from `native_decide`, and no
`proof_wanted` may appear.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file or in the files it imports.
-/
module

public import Poincare.D10.HeatKernelEuclidean.HeatEquation
public import Poincare.D10.HeatKernelEuclidean.Semigroup

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-! ## Kernel definition and elementary properties -/

#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_apply
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_nonneg
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_pos
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_ne_zero
#print axioms Poincare.D10.HeatKernelEuclidean.measurable_gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.continuous_gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.norm_sq_eq_sum_sq
#print axioms Poincare.D10.HeatKernelEuclidean.inner_basisFun
#print axioms Poincare.D10.HeatKernelEuclidean.finrank_euclideanSpace_fin
#print axioms Poincare.D10.HeatKernelEuclidean.rpow_prefactor_ne_zero

/-! ## Gaussian integrals and the Laplacian of `exp (a ‖x‖²)` -/

#print axioms Poincare.D10.HeatKernelEuclidean.innerCLM
#print axioms Poincare.D10.HeatKernelEuclidean.innerCLM_apply
#print axioms Poincare.D10.HeatKernelEuclidean.integral_exp_neg_mul_norm_sq
#print axioms Poincare.D10.HeatKernelEuclidean.integral_exp_neg_mul_norm_sq_sub
#print axioms Poincare.D10.HeatKernelEuclidean.iteratedFDeriv_two_exp_norm_sq
#print axioms Poincare.D10.HeatKernelEuclidean.laplacian_exp_norm_sq

/-! ## Total mass -/

#print axioms Poincare.D10.HeatKernelEuclidean.finrank_euclideanSpace_fin_real
#print axioms Poincare.D10.HeatKernelEuclidean.exp_part_eq
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral

/-! ## The heat equation -/

#print axioms Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel
#print axioms Poincare.D10.HeatKernelEuclidean.heat_equation
#print axioms Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel_fun
#print axioms Poincare.D10.HeatKernelEuclidean.heat_equation_fun

/-! ## The semigroup / convolution identity -/

#print axioms Poincare.D10.HeatKernelEuclidean.conv_exponent_identity
#print axioms Poincare.D10.HeatKernelEuclidean.prefactor_mul
#print axioms Poincare.D10.HeatKernelEuclidean.SemigroupConvolutionIdentity
#print axioms Poincare.D10.HeatKernelEuclidean.semigroupConvolutionIdentity
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel_convolution

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations of the `D10` heat-kernel development. -/
private def heatKernelAuditedDeclarations : List Name :=
  [ ``Poincare.D10.HeatKernelEuclidean.gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_apply,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_nonneg,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_pos,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_ne_zero,
    ``Poincare.D10.HeatKernelEuclidean.measurable_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.continuous_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.norm_sq_eq_sum_sq,
    ``Poincare.D10.HeatKernelEuclidean.inner_basisFun,
    ``Poincare.D10.HeatKernelEuclidean.finrank_euclideanSpace_fin,
    ``Poincare.D10.HeatKernelEuclidean.finrank_euclideanSpace_fin_real,
    ``Poincare.D10.HeatKernelEuclidean.rpow_prefactor_ne_zero,
    ``Poincare.D10.HeatKernelEuclidean.innerCLM,
    ``Poincare.D10.HeatKernelEuclidean.innerCLM_apply,
    ``Poincare.D10.HeatKernelEuclidean.integral_exp_neg_mul_norm_sq,
    ``Poincare.D10.HeatKernelEuclidean.integral_exp_neg_mul_norm_sq_sub,
    ``Poincare.D10.HeatKernelEuclidean.iteratedFDeriv_two_exp_norm_sq,
    ``Poincare.D10.HeatKernelEuclidean.laplacian_exp_norm_sq,
    ``Poincare.D10.HeatKernelEuclidean.exp_part_eq,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_integral,
    ``Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel,
    ``Poincare.D10.HeatKernelEuclidean.heat_equation,
    ``Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel_fun,
    ``Poincare.D10.HeatKernelEuclidean.heat_equation_fun,
    ``Poincare.D10.HeatKernelEuclidean.conv_exponent_identity,
    ``Poincare.D10.HeatKernelEuclidean.prefactor_mul,
    ``Poincare.D10.HeatKernelEuclidean.SemigroupConvolutionIdentity,
    ``Poincare.D10.HeatKernelEuclidean.semigroupConvolutionIdentity,
    ``Poincare.D10.HeatKernelEuclidean.gaussianKernel_convolution ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def heatKernelApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in heatKernelAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !heatKernelApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D10AxiomCheck: PASS — all {heatKernelAuditedDeclarations.length} declarations \
      of the D10 heat-kernel development depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D10AxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D10AxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
