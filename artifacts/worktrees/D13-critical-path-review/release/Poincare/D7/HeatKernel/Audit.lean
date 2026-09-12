/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.All

set_option linter.style.haveILetI false

/-!
# Poincare.D7.HeatKernel.Audit

**D7 heat-kernel layer, part 8: the `#print axioms` audit.**

One `#print axioms` command per principal declaration of the layer. Every cone is expected to be a
subset of `{propext, Classical.choice, Quot.sound}`; no `sorryAx`, no `native_decide`, and no
`proof_wanted` may appear.
-/

-- Basic.lean
-- Basic (structure)
#print axioms Poincare.D7.HeatKernel.HeatKernelData
-- Basic (theorem)
#print axioms Poincare.D7.HeatKernel.HeatKernelData.kernel_pos_of_lowerBound
-- Basic (theorem)
#print axioms Poincare.D7.HeatKernel.HeatKernelData.upperBound_self
-- Basic (theorem)
#print axioms Poincare.D7.HeatKernel.HeatKernelData.semigroup_symm
-- Basic (theorem)
#print axioms Poincare.D7.HeatKernel.HeatKernelData.normalization_symm
-- Basic (theorem)
#print axioms Poincare.D7.HeatKernel.HeatKernelData.gaussian_factor_nonneg
-- Grid.lean
-- Grid (def)
#print axioms Poincare.D7.HeatKernel.heatStep
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.heatStep_apply
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.heatStep_one
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.heatStep_mul
-- Grid (structure)
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.eq_pow_of
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.eq_pow
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.unique
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.apply_unique
-- Grid (def)
#print axioms Poincare.D7.HeatKernel.IsFiniteGridHeatKernel
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.finiteGrid_heatKernel_unique
-- Grid (def)
#print axioms Poincare.D7.HeatKernel.gridKernel
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.gridKernel_K
-- Grid (structure)
#print axioms Poincare.D7.HeatKernel.GridHeatSolution
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.GridHeatSolution.unique
-- Grid (def)
#print axioms Poincare.D7.HeatKernel.gridFlow
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.gridFlow_succ
-- Grid (theorem)
#print axioms Poincare.D7.HeatKernel.gridFlow_nonneg
-- Content.lean
-- Content (def)
#print axioms Poincare.D7.HeatKernel.heatContent
-- Content (def)
#print axioms Poincare.D7.HeatKernel.l2Energy
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.weighted_cauchy_schwarz
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_heatStep_le
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_antitone
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_heatStep_le
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_antitone
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_gridFlow_antitone
-- Content (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_gridFlow_antitone
-- Instance.lean
-- Instance (def)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_kernel
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_C_up
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_C_lo
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_dist
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_upper
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_lower
-- Instance (theorem)
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData_pos
-- Example.lean
-- Example (abbrev)
#print axioms Poincare.D7.HeatKernel.TwoPoint
-- Example (def)
#print axioms Poincare.D7.HeatKernel.twoPointStep
-- Example (def)
#print axioms Poincare.D7.HeatKernel.twoPointDist
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointStep_mul_self
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointStep_pow_succ
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointStep_pow_upper
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointStep_pow_lower
-- Example (def)
#print axioms Poincare.D7.HeatKernel.twoPointGridKernel
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointGridKernel_generator
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointGridKernel_K_two
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.twoPointGridKernel_unique
-- Example (def)
#print axioms Poincare.D7.HeatKernel.stepSub
-- Example (def)
#print axioms Poincare.D7.HeatKernel.u0
-- Example (def)
#print axioms Poincare.D7.HeatKernel.u1
-- Example (def)
#print axioms Poincare.D7.HeatKernel.u2
-- Example (def)
#print axioms Poincare.D7.HeatKernel.massOne
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatStep_stepSub_u0
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatStep_stepSub_u1
-- Example (def)
#print axioms Poincare.D7.HeatKernel.uFlow
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.uFlow_zero
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.uFlow_succ
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.uFlow_one
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.uFlow_two
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_u0
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_u1
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_u2
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_u0
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_u1
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_u2
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.stepSub_nonneg
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.massOne_nonneg
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.u0_nonneg
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.stepSub_col
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.stepSub_row
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.stepSub_col'
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.uFlow_nonneg
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_oneStep_le
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_uFlow_antitone
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_uFlow_antitone
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.heatContent_two_le_zero
-- Example (theorem)
#print axioms Poincare.D7.HeatKernel.l2Energy_two_le_zero
-- Blocked.lean
-- Blocked (structure)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.heatOperator
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.zero
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.zero_volume
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.zero_heatOperator
-- Blocked (structure)
#print axioms Poincare.D7.HeatKernel.IsClosedRiemannianManifold
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.not_isClosedRiemannian_zero
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.isClosedRiemannian_zero_of_isEmpty
-- Blocked (structure)
#print axioms Poincare.D7.HeatKernel.IsHeatKernel
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.not_isHeatKernel_zero
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.HeatKernelExistenceStatement
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.heatKernelExistenceStatement_isProp
-- Blocked (structure)
#print axioms Poincare.D7.HeatKernel.Blocker
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.blockers
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.blockers_length
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.blockers_ne_nil
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.MissingMathlibDependencies
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.MissingMathlibDependencies_length
-- Blocked (def)
#print axioms Poincare.D7.HeatKernel.PresentMathlibDependencies
-- Blocked (theorem)
#print axioms Poincare.D7.HeatKernel.PresentMathlibDependencies_length
