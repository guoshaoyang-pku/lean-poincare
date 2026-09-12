import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
#check @MeasureTheory.Measure.IsAddHaarMeasure
#check @MeasureTheory.isUnifLocDoublingMeasureOfIsAddHaarMeasure
#check @MeasureTheory.isAddHaarMeasure_volume_pi
#check @MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure
example : IsUnifLocDoublingMeasure (volume : Measure (Fin 3 → ℝ)) := inferInstance
