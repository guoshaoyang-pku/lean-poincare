import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
open MeasureTheory
#check @MeasureTheory.Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure
example : IsUnifLocDoublingMeasure (volume : Measure (Fin 3 → ℝ)) := inferInstance
example : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure (Fin 3 → ℝ)) := inferInstance
