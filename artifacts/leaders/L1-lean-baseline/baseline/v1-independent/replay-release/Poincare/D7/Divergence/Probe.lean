/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Blocked
import Poincare.D7.Divergence.Example
import Poincare.D7.Divergence.Slab

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Divergence.Probe

**D7 divergence / integration-by-parts layer, part 6: the mathlib API probe and the D7 API
index.**

This module is a compilable probe. Every `#check` below must succeed against the pinned
toolchain, and every `#check_failure` must fail (recording a genuinely absent declaration). The
output of this file is the machine-checked record of the probe required by the task.

## Probe result (pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`)

* **Present and reused (discrete side)**: `Finset.sum_filter`, `Finset.sum_ite_eq`,
  `Finset.sum_ite_eq'`, `Finset.sum_comm`, `Finset.sum_fiberwise`, `Finset.sum_sub_distrib`,
  `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_filter_split` (D7),
  `Fin.sum_univ_succ`, `Fin.sum_univ_castSucc`.
* **Present and reused (smooth side)**: `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
  (the Euclidean box divergence theorem), `ModelWithCorners.boundary`,
  `ModelWithCorners.IsInteriorPoint`, `ModelWithCorners.IsBoundaryPoint`, `mfderiv`, `ContMDiff`,
  `TangentSpace`, `RiemannianBundle`, `IsRiemannianManifold`, `Measure.addHaar`,
  `Measure.IsAddHaarMeasure`, `Measure.haar`, `Measure.IsHaarMeasure`.
* **Absent**: `Stokes`, `Manifold.stokes`, `StokesTheorem`, `RiemannianVolumeMeasure`,
  `Manifold.divergence`, `ManifoldOrientation`, `MeasureTheory.Measure.riemannianVolume`,
  `Bundle.AlternatingMap`. The smooth-manifold divergence theorem is therefore the blocked `Prop`
  of `Poincare.D7.Divergence.Blocked`, with the exact missing dependencies listed there.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Bundle Finset Manifold MeasureTheory

open scoped Bundle

namespace Poincare.D7.Divergence

/-! ## 1. Discrete mathlib API: present and reused -/

#check Finset.sum_filter
#check Finset.sum_ite_eq
#check Finset.sum_ite_eq'
#check Finset.sum_comm
#check Finset.sum_fiberwise
#check Finset.sum_fiberwise_of_maps_to
#check Finset.sum_sub_distrib
#check Finset.sum_add_distrib
#check Finset.sum_eq_zero
#check Finset.sum_congr
#check Finset.sum_bij
#check Finset.mul_sum
#check Finset.sum_mul
#check Fin.sum_univ_succ
#check Fin.sum_univ_castSucc

/-! ## 2. Smooth mathlib API: present and reused by the blocked statement -/

#check MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
#check MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
#check ModelWithCorners.boundary
#check ModelWithCorners.IsInteriorPoint
#check ModelWithCorners.IsBoundaryPoint
#check mfderiv
#check ContMDiff
#check TangentSpace
#check RiemannianBundle
#check IsRiemannianManifold
#check Measure.addHaar
#check Measure.IsAddHaarMeasure
#check Measure.haar
#check Measure.IsHaarMeasure

/-! ## 3. Absent at the pinned revision (recorded by `#check_failure`) -/

#check_failure Stokes
#check_failure Manifold.stokes
#check_failure StokesTheorem
#check_failure RiemannianVolumeMeasure
#check_failure Manifold.divergence
#check_failure ManifoldOrientation
#check_failure MeasureTheory.Measure.riemannianVolume
#check_failure Bundle.AlternatingMap

/-! ## 4. D7 API index: the discrete divergence layer -/

#check DivergenceData
#check DivergenceData.outFlow
#check DivergenceData.inFlow
#check DivergenceData.divergence
#check DivergenceData.outFlux
#check DivergenceData.inFlux
#check DivergenceData.boundaryFlux
#check DivergenceData.outPairing
#check DivergenceData.inPairing
#check DivergenceData.boundaryOut
#check DivergenceData.boundaryIn
#check DivergenceData.boundaryPairing
#check DivergenceData.gradientPairing
#check DivergenceData.divPairing
#check DivergenceData.bothPairing
#check DivergenceData.bothPairing'
#check IBPCertificate
#check IBPCertificate.boundaryTerm
#check IBPCertificate.ibp'
#check IBPCertificate.eq_zero_of_boundaryTerm_eq_zero
#check DivergenceData.sum_fiber_of_mem
#check DivergenceData.sum_filter_split
#check DivergenceData.bothPairing_sub_bothPairing'
#check DivergenceData.sum_outFlow
#check DivergenceData.sum_inFlow
#check DivergenceData.sum_mul_outFlow
#check DivergenceData.sum_mul_inFlow
#check DivergenceData.sum_divergence_eq_boundaryFlux
#check DivergenceData.graph_ibp
#check DivergenceData.ibpCertificate
#check DivergenceData.boundaryPairing_one
#check DivergenceData.gradientPairing_one
#check DivergenceData.sum_divergence_univ_eq_zero
#check DivergenceData.sum_divergence_eq_zero_of_closed

/-! ## 5. D7 API index: the finite-difference slab -/

#check slabForwardDiff
#check slabDivergence
#check sum_telescope
#check slab_product_rule
#check slab_ibp
#check slab_ibp_vanishing
#check slab_ibp_vanishing'
#check slab_ibp_divergence_form
#check slabIBPCertificate
#check slabIBPCertificate_boundaryTerm
#check slabIBPCertificate_boundaryTerm_eq_zero
#check slabIBPCertificate_eq_zero

/-! ## 6. D7 API index: concrete witnesses -/

#check edgeData
#check edgeData_divergence_zero
#check edgeData_divergence_one
#check edgeData_boundaryFlux_singleton_zero
#check edgeData_divergence_theorem_value
#check edgeData_total_divergence_zero
#check edgeData_divPairing
#check edgeData_gradientPairing
#check edgeData_boundaryPairing
#check edgeData_ibp
#check triangleData
#check triangleData_divergence_zero
#check triangleData_divergence_one
#check triangleData_divergence_two
#check triangleData_total_divergence_zero
#check triangleData_divergences_sum
#check slabExampleU
#check slabExampleV
#check slabExample_interiorTerm
#check slabExample_fluxTerm
#check slabExample_boundaryTerm
#check slabExample_ibp

/-! ## 7. D7 API index: the blocked smooth-manifold statement -/

#check BlockerStokes
#check BlockerRiemannianVolumeMeasure
#check BlockerManifoldBoundary
#check BlockerManifoldDivergence
#check ManifoldDivergenceDatum
#check IsRiemannianDivergenceDatum
#check SmoothManifoldDivergenceTheoremStatement
#check ManifoldDivergenceDatum.zero
#check ManifoldDivergenceDatum.not_isRiemannian_zero
#check ManifoldDivergenceDatum.isRiemannian_zero_of_isEmpty
#check MissingMathlibDependencies
#check PresentMathlibDependencies

end Poincare.D7.Divergence
