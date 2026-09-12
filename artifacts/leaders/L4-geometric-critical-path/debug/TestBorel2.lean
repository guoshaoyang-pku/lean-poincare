import Mathlib.MeasureTheory.Measure.Doubling
#check BorelSpace
#check @BorelSpace
#check OpensMeasurableSpace
example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] : True := trivial
