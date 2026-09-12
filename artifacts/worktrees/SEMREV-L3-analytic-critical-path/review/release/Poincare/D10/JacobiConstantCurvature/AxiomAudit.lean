/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D10 — kernel axiom audit for the Jacobi / Rauch comparison development

This file contains no mathematics: it asks the Lean kernel to print the axiom dependencies of
every headline declaration of the D10 Jacobi development.  The expected (and observed) answer
for all of them is the standard classical trio

`[propext, Classical.choice, Quot.sound]`

with no `sorryAx`, no `native_decide`, no custom axiom and no `unsafe` declaration anywhere in
the dependency cone.
-/
import Poincare.D10.JacobiConstantCurvature.Comparison

/-! ## Definitions -/

#print axioms Poincare.D10.jacobiSolSphere
#print axioms Poincare.D10.jacobiSolFlat
#print axioms Poincare.D10.jacobiSolHyperbolic
#print axioms Poincare.D10.jacobiSol
#print axioms Poincare.D10.jacobiDeriv

/-! ## Initial conditions -/

#print axioms Poincare.D10.jacobiSol_zero
#print axioms Poincare.D10.jacobiDeriv_zero
#print axioms Poincare.D10.jacobiSolSphere_initial
#print axioms Poincare.D10.jacobiSolFlat_initial
#print axioms Poincare.D10.jacobiSolHyperbolic_initial
#print axioms Poincare.D10.jacobiSol_initial
#print axioms Poincare.D10.jacobiSol_deriv_zero
#print axioms Poincare.D10.jacobiSolSphere_deriv_zero
#print axioms Poincare.D10.jacobiSolFlat_deriv_zero
#print axioms Poincare.D10.jacobiSolHyperbolic_deriv_zero

/-! ## The scalar Jacobi ODE `j'' + K j = 0` -/

#print axioms Poincare.D10.SolvesJacobiODE
#print axioms Poincare.D10.HasNormalizedInitial
#print axioms Poincare.D10.jacobiSolSphere_solvesJacobiODE
#print axioms Poincare.D10.jacobiSolFlat_solvesJacobiODE
#print axioms Poincare.D10.jacobiSolHyperbolic_solvesJacobiODE
#print axioms Poincare.D10.jacobiSolSphere_hasNormalizedInitial
#print axioms Poincare.D10.jacobiSolFlat_hasNormalizedInitial
#print axioms Poincare.D10.jacobiSolHyperbolic_hasNormalizedInitial
#print axioms Poincare.D10.jacobiSolSphere_deriv
#print axioms Poincare.D10.jacobiSolSphere_ode
#print axioms Poincare.D10.jacobiSolFlat_deriv
#print axioms Poincare.D10.jacobiSolFlat_ode
#print axioms Poincare.D10.jacobiSolHyperbolic_deriv
#print axioms Poincare.D10.jacobiSolHyperbolic_ode
#print axioms Poincare.D10.jacobiSol_deriv
#print axioms Poincare.D10.jacobiSol_ode
#print axioms Poincare.D10.jacobiSol_solves_ivp
#print axioms Poincare.D10.jacobiSol_solvesJacobiODE
#print axioms Poincare.D10.jacobiSol_hasNormalizedInitial

/-! ## Rauch comparison -/

#print axioms Poincare.D10.jacobiDeriv_le_of_le
#print axioms Poincare.D10.jacobiSol_nonneg
#print axioms Poincare.D10.jacobiSol_firstZero
#print axioms Poincare.D10.rauch_comparison
#print axioms Poincare.D10.rauch_comparison_sphere
#print axioms Poincare.D10.rauch_comparison_of_nonpos
