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

/-- **The metric half of the Bochner identity**: `Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, Δ∇u⟩`.
Uses only metric compatibility (via `nablaField_metric`, `D_gradSq`) and the
gradient–Hessian duality (`nablaField_grad_coeff`); no commutator, no torsion. -/
lemma bochner_metric_half (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    (∑ i : ι, dd.D (m.basis i) (dd.D (m.basis i) (gradSq dd u))
        - dd.D (d.nabla (m.basis i) (m.basis i)) (gradSq dd u))
      = 2 * hessSq dd d u + 2 * fieldInner (gradField dd u) (fieldLaplacian dd d u) := by
  have hD1 : ∀ i, dd.D (m.basis i) (gradSq dd u)
      = 2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u)) :=
    fun i => D_gradSq dd d (m.basis i) u
  have hD2 : ∀ i, dd.D (d.nabla (m.basis i) (m.basis i)) (gradSq dd u) =
      2 * fieldInner (gradField dd u) (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u)) :=
    fun i => D_gradSq dd d (d.nabla (m.basis i) (m.basis i)) u
  unfold hessSq fieldLaplacian
  simp_rw [hD1, hD2]
  simp_rw [show ∀ i, dd.D (m.basis i) (2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))) =
      2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u)) (nablaField dd d (m.basis i) (gradField dd u))
        + fieldInner (gradField dd u) (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))) by
    intro i
    rw [show 2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))
        = fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))
          + fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u)) by ring]
    rw [(dd.D (m.basis i)).map_add]
    rw [nablaField_metric dd d (m.basis i) (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))]
    have hc : fieldInner (gradField dd u) (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))) =
        fieldInner (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))) (gradField dd u) := by
      unfold fieldInner
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    rw [hc]
    ring]
  rw [← Finset.sum_sub_distrib]
  rw [show (∑ i : ι, 2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u)) (nablaField dd d (m.basis i) (gradField dd u))
        + fieldInner (gradField dd u) (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))))
      - ∑ i : ι, 2 * fieldInner (gradField dd u) (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u))
      = 2 * (∑ i : ι, ∑ j : ι, H dd d u i j * H dd d u i j)
        + 2 * (∑ j : ι, ui dd u j * (∑ i : ι,
            nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)) j
              - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)) by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · unfold fieldInner
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [nablaField_grad_coeff dd d u i j]
    · rfl]
  unfold fieldInner
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · rfl
  · rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sub]

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
