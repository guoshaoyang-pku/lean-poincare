import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.MetricSpace.ProperSpace

#check @MeasureTheory.IsAddHaarMeasure
#check @MeasureTheory.isUnifLocDoublingMeasureOfIsAddHaarMeasure
#check @Module.Basis.addHaar
#check @HasBesicovitchCovering
#check @VitaliFamily
#check @MeasureTheory.Measure.hausdorffMeasure
#check (volume : Measure (Fin 3 → ℝ))
#synth MeasureTheory.IsAddHaarMeasure (volume : Measure (Fin 3 → ℝ))
#synth IsUnifLocDoublingMeasure (volume : Measure (Fin 3 → ℝ))
#check @ProperSpace
#check @Metric.isCompact_of_isClosed_isBounded
#check @Metric.totallyBounded_iff
