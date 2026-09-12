/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.All

/-!
# Poincare.D7.Limit.Probe

API probe for the discrete-to-continuous limit layer.  Every `#check` below is
compiled by the kernel gate; `#check_failure` records the absence of the
analytic ingredients that the state-only convergence statement names as missing
dependencies.

This file contains no mathematical content.
-/

open Filter Set
open scoped Topology

namespace Poincare.D7.Limit

/-! ## The D2 continuous heat interface -/

#check @Poincare.Longrun.PDE.ContinuousHeatHypotheses
#check @Poincare.Longrun.PDE.ContinuousHeatMaximumPrincipleInterface
#check Poincare.Longrun.PDE.ContinuousHeatHypotheses.continuous_on_slab
#check Poincare.Longrun.PDE.ContinuousHeatHypotheses.heat_equation
#check Poincare.Longrun.PDE.ContinuousHeatHypotheses.initial_nonpos
#check Poincare.Longrun.PDE.ContinuousHeatHypotheses.lateral_nonpos

/-! ## The D2 discrete heat evolution -/

#check @Poincare.Longrun.PDE.HeatGridEvolution
#check @Poincare.Longrun.PDE.HeatGridEvolution.step_eq_convex
#check @Poincare.Longrun.PDE.HeatGridEvolution.step_eq_heatStep
#check @Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le

/-! ## The D4 statement-only mesh-convergence predicate -/

#check @Poincare.Longrun.Evolution.FiniteMeshConvergence

/-! ## Order / limit API -/

#check @le_of_tendsto'
#check @Tendsto.comp
#check @Filter.Tendsto.prodMk_nhds
#check @Filter.Eventually.of_forall
#check @tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
#check @ContinuousOn.continuousWithinAt
#check @ContinuousWithinAt.tendsto
#check @Metric.tendsto_atTop
#check @tendsto_atTop_mono
#check @squeeze_zero
#check @tendsto_zero_iff_abs_tendsto_zero

/-! ## Finite sums and extrema -/

#check @Finset.sup'_le
#check @Finset.le_sup'
#check @Finset.sum_nonneg
#check @Finset.sum_le_sum
#check @Finset.sum_range_succ
#check @Finset.sum_const
#check @nsmul_eq_mul
#check @abs_le
#check @abs_add_le
#check @abs_mul
#check @abs_of_nonneg
#check @abs_eq_zero
#check @sub_eq_zero
#check @sub_sub_cancel
#check @max_le
#check @Real.dist_eq

/-! ## Grid / mesh API -/

#check @StrictMonoOn
#check @Nat.cast_sub
#check @Nat.cast_lt
#check @tendsto_natCast_atTop_atTop
#check @Tendsto.inv_tendsto_atTop
#check @tendsto_inv_atTop_zero

/-! ## Compactness / regularity (the missing analytic inputs) -/

#check @Equicontinuous
#check @EquicontinuousOn
#check @IsCompact
#check @ContinuousMap
#check @taylor_mean_remainder
#check @HasFTaylorSeriesUpTo
#check_failure @ArzelaAscoli
#check_failure (ParabolicRegularity : Prop)
#check_failure (SchauderEstimate : Prop)
#check_failure (SobolevSpace : Type)
#check_failure (UniformC2Estimate : Prop)

end Poincare.D7.Limit
