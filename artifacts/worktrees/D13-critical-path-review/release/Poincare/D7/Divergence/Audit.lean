/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Probe

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Divergence.Audit

**D7 divergence / integration-by-parts layer, part 7: the `#print axioms` audit.**

This module runs `#print axioms` on every principal declaration of the D7 divergence layer. It
compiles (exit 0) and the expected output is the single cone

```
'<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

for every entry, with no `sorryAx`, `native_decide`, `proof_wanted`, or any other unapproved
axiom.
-/

open Poincare.D7.Divergence

/-! ## Basic: the datum, the discrete operators, and the certificate -/

#print axioms DivergenceData
#print axioms DivergenceData.outFlow
#print axioms DivergenceData.inFlow
#print axioms DivergenceData.divergence
#print axioms DivergenceData.outFlux
#print axioms DivergenceData.inFlux
#print axioms DivergenceData.boundaryFlux
#print axioms DivergenceData.outPairing
#print axioms DivergenceData.inPairing
#print axioms DivergenceData.boundaryOut
#print axioms DivergenceData.boundaryIn
#print axioms DivergenceData.boundaryPairing
#print axioms DivergenceData.gradientPairing
#print axioms DivergenceData.divPairing
#print axioms DivergenceData.bothPairing
#print axioms DivergenceData.bothPairing'
#print axioms IBPCertificate
#print axioms IBPCertificate.boundaryTerm
#print axioms IBPCertificate.ibp'
#print axioms IBPCertificate.eq_zero_of_boundaryTerm_eq_zero
#print axioms IBPCertificate.interiorTerm_eq_neg_fluxTerm_of_boundaryTerm_eq_zero

/-! ## Basic: the combinatorial sum lemmas -/

#print axioms DivergenceData.sum_fiber_of_mem
#print axioms DivergenceData.sum_filter_split
#print axioms DivergenceData.bothPairing_sub_bothPairing'
#print axioms DivergenceData.sum_outFlow
#print axioms DivergenceData.sum_inFlow
#print axioms DivergenceData.sum_mul_outFlow
#print axioms DivergenceData.sum_mul_inFlow

/-! ## Graph: the discrete divergence theorem and integration by parts -/

#print axioms DivergenceData.sum_divergence_eq_boundaryFlux
#print axioms DivergenceData.graph_ibp
#print axioms DivergenceData.ibpCertificate
#print axioms DivergenceData.boundaryPairing_one
#print axioms DivergenceData.gradientPairing_one
#print axioms DivergenceData.sum_divergence_eq_boundaryFlux_of_ibp
#print axioms DivergenceData.sum_divergence_univ_eq_zero
#print axioms DivergenceData.sum_divergence_eq_zero_of_closed

/-! ## Slab: the finite-difference telescoping, product rule, and integration by parts -/

#print axioms slabForwardDiff
#print axioms slabDivergence
#print axioms sum_telescope
#print axioms slab_product_rule
#print axioms slab_ibp
#print axioms slab_ibp_vanishing
#print axioms slab_ibp_vanishing'
#print axioms slab_ibp_divergence_form
#print axioms slabIBPCertificate
#print axioms slabIBPCertificate_boundaryTerm
#print axioms slabIBPCertificate_boundaryTerm_eq_zero
#print axioms slabIBPCertificate_eq_zero

/-! ## Example: concrete non-vacuity witnesses -/

#print axioms edgeData
#print axioms edgeFlow
#print axioms edgePotential
#print axioms edgeData_divergence_zero
#print axioms edgeData_divergence_one
#print axioms edgeData_boundaryFlux_singleton_zero
#print axioms edgeData_boundaryFlux_singleton_one
#print axioms edgeData_divergence_theorem
#print axioms edgeData_divergence_theorem_value
#print axioms edgeData_total_divergence_zero
#print axioms edgeData_divPairing
#print axioms edgeData_gradientPairing
#print axioms edgeData_boundaryPairing
#print axioms edgeData_ibp
#print axioms edgeData_ibpCertificate
#print axioms triangleSrc
#print axioms triangleTgt
#print axioms triangleData
#print axioms triangleFlow
#print axioms triangleData_divergence_zero
#print axioms triangleData_divergence_one
#print axioms triangleData_divergence_two
#print axioms triangleData_boundaryFlux_univ
#print axioms triangleData_total_divergence_zero
#print axioms triangleData_divergences_sum
#print axioms slabExampleU
#print axioms slabExampleV
#print axioms slabExampleU_zero
#print axioms slabExampleV_last
#print axioms slabExample_interiorTerm
#print axioms slabExample_fluxTerm
#print axioms slabExample_boundaryTerm
#print axioms slabExample_ibp
#print axioms slabExample_ibp_vanishing

/-! ## Blocked: the smooth-manifold divergence theorem and the missing dependencies -/

#print axioms BlockerStokes
#print axioms BlockerRiemannianVolumeMeasure
#print axioms BlockerManifoldBoundary
#print axioms BlockerManifoldDivergence
#print axioms BlockerStokes_ne_nil
#print axioms BlockerRiemannianVolumeMeasure_ne_nil
#print axioms BlockerManifoldBoundary_ne_nil
#print axioms BlockerManifoldDivergence_ne_nil
#print axioms ManifoldDivergenceDatum
#print axioms IsRiemannianDivergenceDatum
#print axioms SmoothManifoldDivergenceTheoremStatement
#print axioms ManifoldDivergenceDatum.zero
#print axioms ManifoldDivergenceDatum.not_isRiemannian_zero
#print axioms ManifoldDivergenceDatum.isRiemannian_zero_of_isEmpty
#print axioms MissingMathlibDependencies
#print axioms MissingMathlibDependencies_ne_nil
#print axioms MissingMathlibDependencies_length
#print axioms PresentMathlibDependencies
#print axioms PresentMathlibDependencies_ne_nil
#print axioms PresentMathlibDependencies_length
