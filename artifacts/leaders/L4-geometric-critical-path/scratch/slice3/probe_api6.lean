import Poincare.L4.Compactness.RicciGrowthChain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
noncomputable section
#check @IsometryEquiv.preimage_closedBall
#check @isCompact_uIcc
#check @IsCompact.measure_lt_top
#check @MeasureTheory.ae_restrict_iff'
#check @MeasureTheory.ae_restrict_iff
#check @HasDerivAt.congr_of_eventuallyEq
#check @hasDerivAt_inv
#check @ContinuousOn.inv₀
#check @continuousOn_id
#check @abs_le_max_abs_abs
#check @IntervalIntegrable
#check @intervalIntegrable_iff
#check @AddCircle.equivIco
#check @AddCircle.coe_equivIco
#check @norm_mk_le_norm
#check @AddCircle.norm_le_half
#check @AddCircle.dist_eq
#check @Metric.mem_closedBall
#check @Real.volume_closedBall
