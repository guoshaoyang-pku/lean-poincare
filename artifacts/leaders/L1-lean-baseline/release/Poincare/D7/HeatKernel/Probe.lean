/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.All

set_option linter.style.haveILetI false

/-!
# Poincare.D7.HeatKernel.Probe

**D7 heat-kernel layer, part 7: a compilable mathlib/D7 API probe.**

Every `#check` below must succeed and every `#check_failure` must fail, so this file is itself a
kernel-checked record of which pieces of the layer and of mathlib are available at the pinned
revision, and which analytic inputs of the heat-kernel existence statement are missing.

## Present and reused

Measure and topology: `MeasureTheory.Measure`, `MeasureTheory.integral`, `Measure.dirac`,
`Filter.Tendsto`, `Continuous`, `IsCompact`, `BorelSpace`.
Analysis: `HasDerivAt`, `Real.rpow`, `Real.exp`, `Antitone`, `antitone_nat_of_succ_le`.
Algebra: `LinearMap`, `Matrix`, `Matrix.mul_assoc`, `Finset.sum_mul_sq_le_sq_mul_sq`.

## Absent at the pinned revision (recorded with `#check_failure`)

`heatKernel`, `Manifold.heatKernel`, `HeatKernel`, `HeatSemigroup`, `HeatEquation`,
`parabolicRegularity`, `parabolicMaximumPrinciple`, `SobolevSpace`, `SobolevEmbedding`,
`RellichKondrachov`, `Schauder`, `LiYau`, `GaussianUpperBound`, `MeasureTheory.diracDelta`.

These absences are the blockers `B-D7-HEAT-KERNEL-EXISTENCE`, `B-D7-PARABOLIC-REGULARITY`,
`B-D7-SOBOLEV-EMBEDDING`, `B-D7-SPECTRAL-THEOREM`, `B-D7-DIRAC-DELTA`, `B-D7-GAUSSIAN-BOUNDS`, and
`B-D7-MAXIMUM-PRINCIPLE` of `Poincare.D7.HeatKernel.Blocked`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

/-! ## The layer's own declarations -/

#check @HeatKernelData
#check @HeatKernelData.gaussianUpperBound
#check @HeatKernelData.gaussianLowerBound
#check @HeatKernelData.semigroup
#check @HeatKernelData.normalization
#check @HeatKernelData.symmetry
#check @HeatKernelData.initialCondition
#check @HeatKernelData.heatEquation
#check @HeatKernelData.kernel_pos_of_lowerBound
#check @HeatKernelData.upperBound_self
#check @HeatKernelData.semigroup_symm
#check @heatStep
#check @heatStep_one
#check @heatStep_mul
#check @FiniteGridHeatKernel
#check @FiniteGridHeatKernel.eq_pow_of
#check @FiniteGridHeatKernel.eq_pow
#check @FiniteGridHeatKernel.unique
#check @IsFiniteGridHeatKernel
#check @finiteGrid_heatKernel_unique
#check @gridKernel
#check @GridHeatSolution
#check @GridHeatSolution.unique
#check @gridFlow
#check @gridFlow_succ
#check @gridFlow_nonneg
#check @heatContent
#check @l2Energy
#check @weighted_cauchy_schwarz
#check @heatContent_heatStep_le
#check @heatContent_antitone
#check @l2Energy_heatStep_le
#check @l2Energy_antitone
#check @heatContent_gridFlow_antitone
#check @l2Energy_gridFlow_antitone
#check @punitHeatKernelData
#check @punitHeatKernelData_pos
#check @twoPointStep
#check @twoPointGridKernel
#check @twoPointGridKernel_unique
#check @heatContent_u0
#check @uFlow
#check @heatContent_uFlow_antitone
#check @HeatSpacetime
#check @HeatSpacetime.heatOperator
#check @IsClosedRiemannianManifold
#check @IsHeatKernel
#check @HeatKernelExistenceStatement
#check @blockers
#check @MissingMathlibDependencies

/-! ## Present mathlib dependencies -/

#check @MeasureTheory.Measure
#check @MeasureTheory.integral
#check @Measure.dirac
#check @Filter.Tendsto
#check @Continuous
#check @IsCompact
#check @BorelSpace
#check @HasDerivAt
#check @Real.rpow
#check @Real.exp
#check @Antitone
#check @antitone_nat_of_succ_le
#check @LinearMap
#check @Matrix
#check @Matrix.mul_assoc
#check @Finset.sum_mul_sq_le_sq_mul_sq

/-! ## Absent at the pinned revision -/

#check_failure heatKernel
#check_failure Manifold.heatKernel
#check_failure HeatKernel
#check_failure HeatSemigroup
#check_failure HeatEquation
#check_failure parabolicRegularity
#check_failure parabolicMaximumPrinciple
#check_failure SobolevSpace
#check_failure SobolevEmbedding
#check_failure RellichKondrachov
#check_failure Schauder
#check_failure LiYau
#check_failure GaussianUpperBound
#check_failure MeasureTheory.diracDelta

end Poincare.D7.HeatKernel
