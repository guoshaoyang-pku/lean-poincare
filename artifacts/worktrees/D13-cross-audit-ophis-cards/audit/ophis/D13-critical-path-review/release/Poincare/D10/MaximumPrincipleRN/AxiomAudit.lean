/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D10 builder

# D10 — Kernel axiom audit

`#print axioms` for every headline declaration of the D10 maximum-principle development.
Unconditional theorems must depend only on `propext`, `Classical.choice`, `Quot.sound` (and
must not use `sorryAx`, project axioms, `unsafe` or `native_decide`).
-/

import Poincare.D10.MaximumPrincipleRN.WeakMaximumPrinciple
import Poincare.D10.MaximumPrincipleRN.Semidiscrete

#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_strict
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_sSup
#print axioms Poincare.D10.MaximumPrincipleRN.exists_max_on_parabolicBoundary
#print axioms Poincare.D10.MaximumPrincipleRN.deriv_deriv_nonpos_of_isLocalMax
#print axioms Poincare.D10.MaximumPrincipleRN.hasDerivWithinAt_nonneg_of_isMaxOn_Icc
#print axioms Poincare.D10.MaximumPrincipleRN.continuousOn_Icc_of_differentiableOn
#print axioms Poincare.D10.MaximumPrincipleRN.continuous_update_coord
#print axioms Poincare.D10.MaximumPrincipleRN.semidiscrete_comparison_principle
#print axioms Poincare.D10.MaximumPrincipleRN.semidiscrete_heat_comparison
#print axioms Poincare.D10.MaximumPrincipleRN.semidiscrete_comparison_matrix
#print axioms Poincare.D10.MaximumPrincipleRN.scalar_ode_comparison
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.subTime
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.subTime_operator_le
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.of_classical
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.of_twoSided
#print axioms Poincare.D10.MaximumPrincipleRN.IsHeatSubsolutionOn.of_classical
#print axioms Poincare.D10.MaximumPrincipleRN.IsHeatSubsolutionOn.subTime
#print axioms Poincare.D10.MaximumPrincipleRN.parabolicBoundary_eq
#print axioms Poincare.D10.MaximumPrincipleRN.mem_parabolicBoundary
#print axioms Poincare.D10.MaximumPrincipleRN.IsHeatSubsolutionOn.of_twoSided
#print axioms Poincare.D10.MaximumPrincipleRN.isHeatSubsolutionOn_const
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle_const
