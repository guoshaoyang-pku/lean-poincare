import Poincare.D13.ManifoldIBP.PartialChartModelPOU
open MeasureTheory
open Poincare.D12.VolumeIBP
open scoped ContDiff Topology
noncomputable section
#check @integrable_zero
#check @MeasureTheory.integrable_zero
example : Integrable (fun _ : Vec 1 => (0:ℝ)) (volume : Measure (Vec 1)) := by
  simpa using (integrable_zero (μ := (volume : Measure (Vec 1))))
