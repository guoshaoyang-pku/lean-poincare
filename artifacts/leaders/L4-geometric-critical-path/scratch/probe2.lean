import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.Compactness.MeasureGrowthCovers
import Poincare.L4.PointedGH.Family

open GromovHausdorff MeasureTheory Set Metric

example : MetricSpace PUnit := inferInstance
example : CompactSpace PUnit := inferInstance
example : Nonempty PUnit := inferInstance
#check @Measure.dirac_apply_of_mem
#check @Measure.dirac_apply
#check @Metric.closedBall_eq_empty
#check @Metric.mem_closedBall_self
#check @ENat.le_floor
#check @BorelSpace
#check @borel
example : BorelSpace ℝ := inferInstance
#check @Metric.coveringNumber
#check @IsometryEquiv.image_ball
#check @IsometryEquiv.preimage_ball
#check @IsometryEquiv.isometry
