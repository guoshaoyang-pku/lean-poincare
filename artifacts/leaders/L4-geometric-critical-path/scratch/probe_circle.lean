import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.AddCircle.Real
open MeasureTheory Set Metric
example : MetricSpace (AddCircle (1:ℝ)) := inferInstance
#check @AddCircle.volume_closedBall
#check @IsometryEquiv.preimage_closedBall
#check @IsometryEquiv.image_closedBall
#check @Measure.map_apply
#check @AddCircle.dist_coe_le
#check @AddCircle.norm_coe_le
#check @AddCircle.dist_eq
#check @AddCircle.dist_coe
#check @AddCircle.coe_zero
#check @AddCircle.measure_univ
#check @AddCircle.addHaar_closedBall_center
#check @QuotientAddGroup.dist_le
#check @AddCircle.eq_coe
