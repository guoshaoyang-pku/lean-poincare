/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré formalization longrun (D10-bochner-euclidean)

# Axiom audit for the D10 Bochner-identity development

Every declaration below is checked with `#print axioms`. The only axioms admitted
anywhere in this development are mathlib's three standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
-/

import Poincare.D10.BochnerEuclidean.Basic
import Poincare.D10.BochnerEuclidean.Bochner
import Poincare.D10.BochnerEuclidean.Corollary
import Poincare.D10.BochnerEuclidean.Compat

open Poincare.D10.BochnerEuclidean

/-! ## `Basic.lean` -/

#print axioms basis_apply
#print axioms D_apply
#print axioms D_of_contDiff
#print axioms D_of_contDiffAt
#print axioms D_add
#print axioms D_const
#print axioms D_mul
#print axioms D_const_mul
#print axioms D_pow_two
#print axioms D_sum
#print axioms fderiv_D
#print axioms D_D
#print axioms D_comm
#print axioms DDD_comm
#print axioms D_lap

/-! ## `Bochner.lean` -/

#print axioms D_gradNormSq
#print axioms DD_gradNormSq
#print axioms bochner_identity_components
#print axioms grad_apply
#print axioms norm_sq_grad
#print axioms inner_grad_grad_lap
#print axioms hessNormSq_eq
#print axioms bochner_identity

/-! ## `Corollary.lean` -/

#print axioms hessNormSq_nonneg
#print axioms harmonic_lap_gradNormSq
#print axioms harmonic_lap_gradNormSq_nonneg
#print axioms harmonic_energy_density_subharmonic

/-! ## `Compat.lean` -/

#print axioms sum_basis
#print axioms inner_basis_right
#print axioms grad_eq_gradient
#print axioms lap_eq_laplacian

/-! ## Definitions -/

#print axioms basis
#print axioms D
#print axioms grad
#print axioms gradNormSq
#print axioms hess
#print axioms hessNormSq
#print axioms lap
#print axioms gradLapDot
#print axioms Harmonic

/-! ## Headline statements -/

#print bochner_identity
#print harmonic_energy_density_subharmonic
