/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11 builder

# D11 — Kernel audit of the tensor maximum principle development

`#print axioms` for every headline declaration authored by task `D11-maximum-principle-tensor`.
Unconditional theorems must depend only on `propext`, `Classical.choice`, `Quot.sound` and must
not use `sorryAx`, project axioms, `unsafe` or `native_decide`.  The statement-only `Prop`
`ConeInvariantUnderReaction` is a *definition*, not an axiom: it is used only as an explicit
hypothesis (`tensor_maximum_principle_ode`), and its block below reports the empty axiom cone.
-/

import Poincare.D11.MaximumPrincipleTensor.Basic
import Poincare.D11.MaximumPrincipleTensor.Euler
import Poincare.D11.MaximumPrincipleTensor.ScalarODE
import Poincare.D11.MaximumPrincipleTensor.Flow

-- Cone algebra and the Loewner order
#print axioms Poincare.D11.MaximumPrincipleTensor.psdCone_closed
#print axioms Poincare.D11.MaximumPrincipleTensor.psdCone_convex
#print axioms Poincare.D11.MaximumPrincipleTensor.le_iff_sub_posSemidef
#print axioms Poincare.D11.MaximumPrincipleTensor.posSemidef_iff_quadForm_nonneg
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_nonneg
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_eq_zero_iff_mulVec_eq_zero
#print axioms Poincare.D11.MaximumPrincipleTensor.hasDerivAt_quadForm

-- Null directions and the reaction conditions
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_eulerStep_of_nullVector
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_eulerStep_nonneg_of_nullVector
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_eulerStep_nonneg_of_boundary
#print axioms Poincare.D11.MaximumPrincipleTensor.not_posSemidef_eulerStep_of_nullVector

-- The discrete tensor maximum principle and its sharpness
#print axioms Poincare.D11.MaximumPrincipleTensor.eulerStep_posSemidef
#print axioms Poincare.D11.MaximumPrincipleTensor.eulerIterate_posSemidef
#print axioms Poincare.D11.MaximumPrincipleTensor.eulerStep_mono
#print axioms Poincare.D11.MaximumPrincipleTensor.PositivityPreserving.sq
#print axioms Poincare.D11.MaximumPrincipleTensor.positivityPreserving_const_smul_add_sq
#print axioms Poincare.D11.MaximumPrincipleTensor.exp_smul_posSemidef
#print axioms Poincare.D11.MaximumPrincipleTensor.not_positivityPreserving_neg
#print axioms Poincare.D11.MaximumPrincipleTensor.boundary_condition_strictly_weaker

-- The scalar case
#print axioms Poincare.D11.MaximumPrincipleTensor.scalar_forward_invariance
#print axioms Poincare.D11.MaximumPrincipleTensor.scalar_forward_invariance_of_global_reaction
#print axioms Poincare.D11.MaximumPrincipleTensor.exp_shift_forward_invariance
#print axioms Poincare.D11.MaximumPrincipleTensor.oneByOne_posSemidef_iff
#print axioms Poincare.D11.MaximumPrincipleTensor.oneByOne_forward_invariance
#print axioms Poincare.D11.MaximumPrincipleTensor.sqrtNegReaction_nonneg
#print axioms Poincare.D11.MaximumPrincipleTensor.sqrtNegReaction_negSquare
#print axioms Poincare.D11.MaximumPrincipleTensor.hasDerivAt_negSquare
#print axioms Poincare.D11.MaximumPrincipleTensor.scalar_invariance_oneSided_false

-- The continuum interface
#print axioms Poincare.D11.MaximumPrincipleTensor.ConeInvariantUnderReaction
#print axioms Poincare.D11.MaximumPrincipleTensor.tensor_maximum_principle_ode
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_monotone_of_reaction_posSemidef
#print axioms Poincare.D11.MaximumPrincipleTensor.mat_one_eq_oneByOne
#print axioms Poincare.D11.MaximumPrincipleTensor.coneInvariantUnderReaction_oneByOne
