/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — consolidated `#print axioms` audit driver

This module declares nothing.  It runs `#print axioms` over every lemma, theorem and
definition authored in `Poincare/D11/BochnerManifold/` (the files `Basic`, `RadialBochner`,
`ModelSpace`, `Corollaries`, `D7Bridge`; `Probe.lean` declares nothing).  The required
audit outcome is that every printed axioms list is exactly

    [propext, Classical.choice, Quot.sound]

— the standard Lean cone — with no `sorryAx`, no project axiom, and nothing else.  The
checked declarations are:

* D10 restatement: `euclidean_bochner_identity_restated`, `euclidean_bochner_identity_components_restated`,
  `euclidean_harmonic_subharmonic_restated`;
* warped-model operators: `gradSq`, `lapG`, `hessSq`, `gradDot`, `ricTerm`;
* one-variable calculus: `deriv_gradSq`, `deriv_deriv_gradSq`, `deriv_lapG`,
  `differentiable_deriv_of_contDiff`, `differentiable_deriv_deriv_of_contDiff`,
  `differentiableAt_of_contDiff_one`, `differentiableAt_deriv_deriv_of_contDiff`,
  `deriv_abs_deriv_eq_of_pos`, `deriv_abs_deriv_eq_of_neg`, `deriv_deriv_abs_deriv_eq_of_pos`,
  `deriv_deriv_abs_deriv_eq_of_neg`, `lap_gradSq_split`;
* radial Bochner: `radial_bochner_identity`, `euclidean_radial_bochner`, `radial_bochner_defect`,
  `radial_bochner_identity_dim_zero`;
* constant-curvature model: `jacobiMeanCurvature`, `jacobiMeanCurvature_of_pos`,
  `jacobiMeanCurvature_of_zero`, `jacobiMeanCurvature_of_neg`, `hasDerivAt_jacobiMeanCurvature`,
  `jacobiMeanCurvature_deriv_eq`, `jacobiMeanCurvature_riccati`, `jacobiSol_second_deriv_div`,
  `radial_ricci_of_model`, `modelLap`, `modelHessSq`, `modelGradSq`, `modelGradDot`,
  `modelRicciTerm`, `modelRicciTerm_eq`, `model_bochner_weitzenbock`,
  `model_bochner_weitzenbock_unfolded`, `model_flat_bochner`;
* corollary chains: `model_bochner_weitzenbock_harmonic`, `modelHessSq_nonneg`,
  `modelRicciTerm_nonneg_of_nonneg`, `subharmonic_energy_density_of_nonneg_ricci`,
  `subharmonic_energy_density_of_harmonic`, `model_bochner_inequality_of_nonneg_ricci`,
  `gradient_estimate_inequality`, `model_kato`, `gradient_estimate_of_norm`,
  `gradient_estimate_eq_iff_ricci_zero`;
* D7 bridge: `modelGradVec`, `modelGradLapVec`, `modelHessMat`, `modelRicMat`,
  `frame_ricci_pairing_sum`, `frame_hess_norm_sq_sum`, `frame_grad_lap_dot_sum`,
  `model_ricci_pairing_eq_ricciTerm`, `model_hess_norm_sq_eq_hessSq`,
  `model_grad_lap_dot_eq_gradDot`, `modelBochnerCertificate`, `model_bochner_certificate_bochner`,
  `modelGradientCertificate`, `model_gradient_certificate_hess_norm_sq`,
  `model_gradient_certificate_laplacian_grad_norm_sq`,
  `d7_gradient_estimate_gives_model_subharmonic`,
  `d7_gradient_estimate_implies_model_subharmonic_nonneg`,
  `d7_estimate_iff_ricci_nonneg`, `modelFlatBochnerCertificate`, `model_flat_certificate_identity`,
  `flatCertificateWitness`, `flatCertificateWitness_ricci_zero`,
  `flatCertificateWitness_oneFormLaplacian`, `flatCertificateWitness_roughLaplacian`,
  `flatCertificateWitness_bochner`.

Run `lake env lean release/Poincare/D11/BochnerManifold/Axioms.lean` and check that every
printed list equals `[propext, Classical.choice, Quot.sound]`.
-/

import Poincare.D11.BochnerManifold.D7Bridge

#print axioms Poincare.D11.BochnerManifold.euclidean_bochner_identity_restated
#print axioms Poincare.D11.BochnerManifold.euclidean_bochner_identity_components_restated
#print axioms Poincare.D11.BochnerManifold.euclidean_harmonic_subharmonic_restated
#print axioms Poincare.D11.BochnerManifold.gradSq
#print axioms Poincare.D11.BochnerManifold.lapG
#print axioms Poincare.D11.BochnerManifold.hessSq
#print axioms Poincare.D11.BochnerManifold.gradDot
#print axioms Poincare.D11.BochnerManifold.ricTerm
#print axioms Poincare.D11.BochnerManifold.deriv_gradSq
#print axioms Poincare.D11.BochnerManifold.deriv_deriv_gradSq
#print axioms Poincare.D11.BochnerManifold.deriv_lapG
#print axioms Poincare.D11.BochnerManifold.differentiable_deriv_of_contDiff
#print axioms Poincare.D11.BochnerManifold.differentiable_deriv_deriv_of_contDiff
#print axioms Poincare.D11.BochnerManifold.differentiableAt_of_contDiff_one
#print axioms Poincare.D11.BochnerManifold.differentiableAt_deriv_deriv_of_contDiff
#print axioms Poincare.D11.BochnerManifold.deriv_abs_deriv_eq_of_pos
#print axioms Poincare.D11.BochnerManifold.deriv_abs_deriv_eq_of_neg
#print axioms Poincare.D11.BochnerManifold.deriv_deriv_abs_deriv_eq_of_pos
#print axioms Poincare.D11.BochnerManifold.deriv_deriv_abs_deriv_eq_of_neg
#print axioms Poincare.D11.BochnerManifold.lap_gradSq_split
#print axioms Poincare.D11.BochnerManifold.radial_bochner_identity
#print axioms Poincare.D11.BochnerManifold.euclidean_radial_bochner
#print axioms Poincare.D11.BochnerManifold.radial_bochner_defect
#print axioms Poincare.D11.BochnerManifold.radial_bochner_identity_dim_zero
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_of_pos
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_of_zero
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_of_neg
#print axioms Poincare.D11.BochnerManifold.hasDerivAt_jacobiMeanCurvature
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_deriv_eq
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_riccati
#print axioms Poincare.D11.BochnerManifold.jacobiSol_second_deriv_div
#print axioms Poincare.D11.BochnerManifold.radial_ricci_of_model
#print axioms Poincare.D11.BochnerManifold.modelLap
#print axioms Poincare.D11.BochnerManifold.modelHessSq
#print axioms Poincare.D11.BochnerManifold.modelGradSq
#print axioms Poincare.D11.BochnerManifold.modelGradDot
#print axioms Poincare.D11.BochnerManifold.modelRicciTerm
#print axioms Poincare.D11.BochnerManifold.modelRicciTerm_eq
#print axioms Poincare.D11.BochnerManifold.model_bochner_weitzenbock
#print axioms Poincare.D11.BochnerManifold.model_bochner_weitzenbock_unfolded
#print axioms Poincare.D11.BochnerManifold.model_flat_bochner
#print axioms Poincare.D11.BochnerManifold.model_bochner_weitzenbock_harmonic
#print axioms Poincare.D11.BochnerManifold.modelHessSq_nonneg
#print axioms Poincare.D11.BochnerManifold.modelRicciTerm_nonneg_of_nonneg
#print axioms Poincare.D11.BochnerManifold.subharmonic_energy_density_of_nonneg_ricci
#print axioms Poincare.D11.BochnerManifold.subharmonic_energy_density_of_harmonic
#print axioms Poincare.D11.BochnerManifold.model_bochner_inequality_of_nonneg_ricci
#print axioms Poincare.D11.BochnerManifold.gradient_estimate_inequality
#print axioms Poincare.D11.BochnerManifold.model_kato
#print axioms Poincare.D11.BochnerManifold.gradient_estimate_of_norm
#print axioms Poincare.D11.BochnerManifold.gradient_estimate_eq_iff_ricci_zero
#print axioms Poincare.D11.BochnerManifold.modelGradVec
#print axioms Poincare.D11.BochnerManifold.modelGradLapVec
#print axioms Poincare.D11.BochnerManifold.modelHessMat
#print axioms Poincare.D11.BochnerManifold.modelRicMat
#print axioms Poincare.D11.BochnerManifold.frame_ricci_pairing_sum
#print axioms Poincare.D11.BochnerManifold.frame_hess_norm_sq_sum
#print axioms Poincare.D11.BochnerManifold.frame_grad_lap_dot_sum
#print axioms Poincare.D11.BochnerManifold.model_ricci_pairing_eq_ricciTerm
#print axioms Poincare.D11.BochnerManifold.model_hess_norm_sq_eq_hessSq
#print axioms Poincare.D11.BochnerManifold.model_grad_lap_dot_eq_gradDot
#print axioms Poincare.D11.BochnerManifold.modelBochnerCertificate
#print axioms Poincare.D11.BochnerManifold.model_bochner_certificate_bochner
#print axioms Poincare.D11.BochnerManifold.modelGradientCertificate
#print axioms Poincare.D11.BochnerManifold.model_gradient_certificate_hess_norm_sq
#print axioms Poincare.D11.BochnerManifold.model_gradient_certificate_laplacian_grad_norm_sq
#print axioms Poincare.D11.BochnerManifold.d7_gradient_estimate_gives_model_subharmonic
#print axioms Poincare.D11.BochnerManifold.d7_gradient_estimate_implies_model_subharmonic_nonneg
#print axioms Poincare.D11.BochnerManifold.d7_estimate_iff_ricci_nonneg
#print axioms Poincare.D11.BochnerManifold.modelFlatBochnerCertificate
#print axioms Poincare.D11.BochnerManifold.model_flat_certificate_identity
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness_ricci_zero
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness_oneFormLaplacian
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness_roughLaplacian
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness_bochner
