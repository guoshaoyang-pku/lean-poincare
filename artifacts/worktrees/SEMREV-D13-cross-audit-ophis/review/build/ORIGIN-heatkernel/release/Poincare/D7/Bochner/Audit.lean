/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Poincare.D7.Bochner.Probe

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Audit

**D7 Bochner / Weitzenböck layer, part 7: the `#print axioms` audit.**

This module runs `#print axioms` on every principal declaration of the D7 Bochner layer. It
compiles (exit 0) and the expected output is one of

```
'<declaration>' does not depend on any axioms
'<declaration>' depends on axioms: [propext]
'<declaration>' depends on axioms: [propext, Quot.sound]
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

for every entry, with no nonstandard dependency and no incomplete-proof marker.
-/

open Poincare.D7.Bochner

/-! ## Basic: the scalar quantities and the certificate -/

#print axioms hessNormSq
#print axioms gradLaplacianDot
#print axioms ricciPairing
#print axioms hessNormSq_nonneg
#print axioms ricciPairing_zero
#print axioms ricciPairing_zero_grad
#print axioms gradLaplacianDot_zero_right
#print axioms gradLaplacianDot_zero_left
#print axioms IsRicciNonnegative
#print axioms isRicciNonnegative_zero
#print axioms IsRicciNonnegative.apply
#print axioms BochnerCertificate
#print axioms BochnerCertificate.bochner'
#print axioms BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero
#print axioms BochnerCertificate.roughLaplacian_le_oneFormLaplacian
#print axioms BochnerCertificate.ricciPairing_nonneg
#print axioms BochnerCertificate.ricciContraction_eq_zero_of_ric_zero
#print axioms BochnerCertificate.ricciContraction_eq_zero_of_ricciPairing_zero
#print axioms BochnerCertificate.ricciContraction_eq_sub
#print axioms BochnerCertificate.ricciContraction_eq_ricciPairing

/-! ## Euclidean: the finite cyclic difference model and the flat certificate -/

#print axioms Conf
#print axioms shift
#print axioms diff
#print axioms shift_comm
#print axioms shift_add
#print axioms shift_sub
#print axioms shift_univ_sum
#print axioms diff_add
#print axioms diff_sub
#print axioms diff_univ_sum
#print axioms diff_shift_comm
#print axioms diff_comm
#print axioms laplacian
#print axioms laplacian_apply
#print axioms diff_laplacian_comm
#print axioms Euclidean.grad
#print axioms Euclidean.hess
#print axioms Euclidean.hess_symm
#print axioms Euclidean.oneFormLaplacian
#print axioms Euclidean.roughLaplacian
#print axioms Euclidean.oneFormLaplacian_eq_roughLaplacian_of_commutation
#print axioms Euclidean.oneFormLaplacian_eq_roughLaplacian
#print axioms Euclidean.euclidean_bochner_identity
#print axioms Euclidean.euclideanBochnerCertificate
#print axioms Euclidean.euclideanBochnerCertificate_ric
#print axioms Euclidean.euclideanBochnerCertificate_ricciContraction
#print axioms Euclidean.euclideanBochnerCertificate_oneFormLaplacian
#print axioms Euclidean.euclideanBochnerCertificate_hess_symm

/-! ## GradientEstimate: the gradient-estimate toy -/

#print axioms GradientCertificate
#print axioms GradientCertificate.bochner_inequality
#print axioms GradientCertificate.gradient_estimate
#print axioms GradientCertificate.gradient_estimate'
#print axioms GradientCertificate.gradient_estimate_eq_iff_ricci_zero
#print axioms GradientCertificate.gradient_estimate_eq_of_ricci_zero
#print axioms GradientCertificate.laplacianGradNormSq_nonneg
#print axioms GradientCertificate.ricci_nonneg
#print axioms GradientCertificate.ricciPairing_nonneg
#print axioms gradientCertificateOfData

/-! ## Example: concrete witnesses and the negative control -/

#print axioms flatExampleCertificate
#print axioms curvedExampleCertificate
#print axioms flatExampleCertificate_ricci_zero
#print axioms flatExampleCertificate_identity
#print axioms curvedExampleCertificate_ricci
#print axioms curvedExampleCertificate_ricci_pos
#print axioms curvedExampleCertificate_hessNormSq
#print axioms curvedExampleCertificate_bochner
#print axioms flatExampleGradient
#print axioms curvedExampleGradient
#print axioms curvedExampleGradient_laplacianGradNormSq
#print axioms curvedExampleGradient_hessNormSq
#print axioms curvedExampleGradient_estimate
#print axioms curvedExampleGradient_estimate_strict
#print axioms flatExampleGradient_estimate_eq
#print axioms flatExampleGradient_laplacianGradNormSq
#print axioms RawGradientModel
#print axioms negativeControl
#print axioms negativeControl_ricci_neg
#print axioms negativeControl_estimate_fails
#print axioms euclideanCertificate_zero_identity

/-! ## Blocked: the smooth statement, blockers, and dependency lists -/

#print axioms BlockerHessian
#print axioms BlockerLaplaceBeltrami
#print axioms BlockerRoughLaplacian
#print axioms BlockerManifoldCurvature
#print axioms BlockerBochnerWeitzenbock
#print axioms BlockerHessian_ne_nil
#print axioms BlockerLaplaceBeltrami_ne_nil
#print axioms BlockerRoughLaplacian_ne_nil
#print axioms BlockerManifoldCurvature_ne_nil
#print axioms BlockerBochnerWeitzenbock_ne_nil
#print axioms SmoothBochnerDatum
#print axioms IsSmoothBochnerDatum
#print axioms SmoothBochnerFormulaStatement
#print axioms SmoothBochnerWeitzenbockStatement
#print axioms SmoothBochnerGradientEstimateStatement
#print axioms SmoothBochnerDatum.zero
#print axioms SmoothBochnerDatum.zero_not_isSmooth_of_nontrivial
#print axioms SmoothBochnerDatum.isSmooth_zero_of_isEmpty
#print axioms MissingMathlibDependencies
#print axioms PresentMathlibDependencies
#print axioms MissingMathlibDependencies_ne_nil
#print axioms MissingMathlibDependencies_length
#print axioms PresentMathlibDependencies_ne_nil
#print axioms PresentMathlibDependencies_length
