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

example (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    (∑ i : ι, 2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u))
          (nablaField dd d (m.basis i) (gradField dd u))
        + fieldInner (gradField dd u)
          (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))))
        - 2 * fieldInner (gradField dd u)
          (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u)))
      = ∑ i : ι, (2 * (∑ j : ι, H dd d u i j * H dd d u i j)
          + 2 * (∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
              (nablaField dd d (m.basis i) (gradField dd u)) j
            - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))) := by
  apply Finset.sum_congr rfl
  intro i _
  sorry

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
