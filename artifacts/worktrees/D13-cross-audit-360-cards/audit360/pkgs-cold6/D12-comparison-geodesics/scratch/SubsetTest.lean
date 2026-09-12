import Poincare.D12.ComparisonGeodesics.Definitions
import Mathlib.MeasureTheory.Integral.IntegrableOn
noncomputable section
open Set Filter
open scoped Topology
open MeasureTheory
namespace Poincare.D12.ComparisonGeodesics

example {m : ℝ → ℝ} {T u ε : ℝ} (hmcont : ContinuousOn m (Icc 0 T))
    (hε : ε ∈ Ioo 0 u) (huT2 : u ≤ T) :
    ContinuousOn m (Icc ε u) := by
  exact hmcont.mono (Icc_subset_Icc (le_of_lt hε.1) huT2)

end Poincare.D12.ComparisonGeodesics
