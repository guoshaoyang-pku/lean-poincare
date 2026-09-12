import Poincare.D12.TensorMaximumBochner.BochnerIdentity
open scoped BigOperators
set_option linter.unusedSectionVars false
namespace Poincare
namespace D12
namespace TensorMaximumBochner
namespace Bochner
open Poincare.Longrun.Geometry
open Poincare.Longrun.Geometry.MetricData
open Poincare.CurvatureAlgebra
universe v w uA
noncomputable section
variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {m : MetricData V ι} {b : LieBracketData ℝ V}
variable {A : Type uA} [CommRing A] [Algebra ℝ A]
include m b

example (f g : ι → A) (h : ∀ i, f i = g i) : (∑ i, f i) = ∑ i, g i := by
  apply Finset.sum_congr rfl
  intro i _
  exact h i

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
