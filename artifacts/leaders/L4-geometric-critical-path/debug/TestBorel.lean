import Mathlib.MeasureTheory.Measure.Doubling

open Set Metric MeasureTheory

variable {X : Type*} [PseudoMetricSpace X]

example [MeasurableSpace X] [BorelSpace X] (x : X) (r : ℝ≥0) : MeasurableSet (closedBall x r) :=
  isClosed_closedBall.measurableSet
