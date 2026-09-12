import Poincare.L4.Compactness.MeasureGrowthCovers
import Mathlib.Topology.MetricSpace.GromovHausdorff

open GromovHausdorff MeasureTheory

example (p : GHSpace) : MeasurableSpace p.Rep := inferInstance
example (p : GHSpace) : BorelSpace p.Rep := inferInstance
#check @GHSpace.toGHSpace_rep
#check @Metric.coveringNumber
#check @coveringNumber_le_of_measure_doubling
#check @ENat.le_floor
#check @Metric.closedBall
