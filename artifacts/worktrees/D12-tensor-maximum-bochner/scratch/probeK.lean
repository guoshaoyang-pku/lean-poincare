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

example (d : LeviCivitaData m b) (i j : ι) :
    (∀ l : ι, gammaX d (d.nabla (m.basis i) (m.basis i)) l j
      = ∑ mm : ι, (gamma d i i mm * gamma d mm l j : A)) := by
  intro l
  unfold gammaX gamma
  sorry

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
