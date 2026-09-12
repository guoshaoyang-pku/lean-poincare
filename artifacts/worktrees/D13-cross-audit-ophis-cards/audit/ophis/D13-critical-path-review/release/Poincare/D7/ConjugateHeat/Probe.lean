/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.All
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option linter.style.haveILetI false

/-!
# Poincare.D7.ConjugateHeat.Probe

**D7 conjugate-heat layer, part 7: a compilable mathlib/D7 API probe.**

Every `#check` below must succeed and every `#check_failure` must fail, so this file is itself a
kernel-checked record of which pieces of the layer and of mathlib are available at the pinned
revision, and which analytic inputs of the conjugate heat kernel are missing.

## Present and reused

Algebra and finite sums: `LinearMap.mk₂`, `LinearMap.pi`, `Finset.sum_ite_eq'`,
`Finset.sum_filter`, `Finset.sum_nonneg`, `Finset.sum_comm`.
Measure and topology: `MeasureTheory.Measure`, `MeasureTheory.integral`, `Measure.dirac`,
`Measure.addHaar`, `Filter.Tendsto`.
Manifold API: `ModelWithCorners.boundary`, `mfderiv`, `ContMDiff`, `TangentSpace`,
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.

## Absent at the pinned revision (recorded with `#check_failure`)

`heatKernel`, `Manifold.heatKernel`, `conjugateHeatKernel`, `MeasureTheory.diracDelta`,
`GaussianUpperBound`, `parabolicMaximumPrinciple`, `RicciFlow`, `HeatSemigroup`.

These absences are the blockers `B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE`, `B-D7-HEAT-KERNEL-MANIFOLD`,
`B-D7-DIRAC-DELTA`, `B-D7-GAUSSIAN-BOUNDS`, `B-D7-RICCI-FLOW-SPACETIME`, and
`B-D7-PARABOLIC-MAXIMUM-PRINCIPLE` of `Poincare.D7.ConjugateHeat.Blocked`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.ConjugateHeat

/-! ## The layer's own declarations -/

#check @pairingLM
#check @scalarMulLM
#check @edgeLap
#check @graphLaplacian
#check @laplaceBeltrami
#check @dirichletForm
#check @boundaryPair
#check @boundaryForm
#check @green_first
#check @green_second
#check @dirichletForm_nonneg
#check @boundaryPair_univ
#check @MetricFlowInterface
#check @Jet
#check @ConjugateHeatData
#check @ConjugateHeatData.formal_adjoint
#check @ConjugateHeatData.isConjugateHeatJet_self
#check @ConjugateHeatData.isHeatJet_self
#check @ConjugateHeatIBPCertificate
#check @conjugateHeatIBPCertificate
#check @metricFlowInterface
#check @conjugateHeatData
#check @conjugateHeatData_formal_adjoint
#check @energy
#check @conjugateHeatStep
#check @energy_le_energy_conjugateHeatStep
#check @energy_mono_slab
#check @ConjugateHeatKernelExistenceStatement
#check @IsConjugateHeatKernel
#check @IsRiemannianConjugateHeatSpacetime
#check @blockers
#check @MissingMathlibDependencies

/-! ## Present mathlib API -/

#check @LinearMap.mk₂
#check @LinearMap.pi
#check @LinearMap.proj
#check @Finset.sum_ite_eq'
#check @Finset.sum_filter
#check @Finset.sum_nonneg
#check @Finset.sum_comm
#check @mul_self_nonneg
#check @MeasureTheory.Measure
#check @MeasureTheory.integral
#check @Measure.dirac
#check @Measure.addHaar
#check @Filter.Tendsto
#check @ModelWithCorners.boundary
#check @mfderiv
#check @ContMDiff
#check @TangentSpace
#check @MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable

/-! ## Absent at the pinned revision -/

#check_failure heatKernel
#check_failure Manifold.heatKernel
#check_failure conjugateHeatKernel
#check_failure MeasureTheory.diracDelta
#check_failure GaussianUpperBound
#check_failure parabolicMaximumPrinciple
#check_failure RicciFlow
#check_failure HeatSemigroup

end Poincare.D7.ConjugateHeat
