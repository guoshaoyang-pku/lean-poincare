import Poincare.L4.Compactness.RicciToDoubling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
open Poincare.D12.ComparisonGeodesics

noncomputable section

#check @Prod.dist_eq
#check @closedBall_prod_same
#check @Prod.closedBall_prod_same
#check @Metric.closedBall_prod_same
#check @ContinuousOn.congr
#check @intervalIntegral.integral_add_adjacent_intervals
#check @ContinuousOn.intervalIntegrable
#check @Set.uIcc_of_le
#check @intervalIntegral.integral_congr
#check @intervalIntegral.integral_const_mul
#check @intervalIntegral.integral_id
#check @intervalIntegral.integral_zero
#check @MeasureTheory.Measure.volume_eq_prod
#check @MeasureTheory.Measure.prod_prod
