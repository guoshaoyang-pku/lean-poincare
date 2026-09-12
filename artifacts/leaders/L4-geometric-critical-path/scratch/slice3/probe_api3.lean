import Poincare.L4.Compactness.RicciToDoubling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
noncomputable section
#check @intervalIntegral.integral_add_adjacent_intervals_cancel
#check @intervalIntegral.integral_add_adjacent_intervals
#check @intervalIntegral.integral_interval_sub_left
#check @MeasureTheory.IntegrableOn.of_bound
#check @MeasureTheory.Integrable.of_bound
#check @measurable_indicator_iff
#check @Measurable.indicator
#check @ContinuousOn.measurable
#check @ContinuousOn.measurableOn
#check @MeasurableOn.indicator
#check @intervalIntegral.integral_id
#check @intervalIntegral.integral_pow
#check @intervalIntegral.integral_const_mul
#check @intervalIntegral.integral_of_le
#check @intervalIntegral.integral_nonneg
#check @setIntegral_union
#check @setIntegral_eq_zero_of_forall_eq_zero
#check @Set.Icc.indicator
