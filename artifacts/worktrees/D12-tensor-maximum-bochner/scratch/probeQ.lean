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

example (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) (j : ι) :
    (∑ a : ι, ∑ b : ι, (cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
        + (if j = a then ∑ i : ι, gamma d i i b else 0)
        - (if j = b then ∑ i : ι, gamma d i i a else 0)) * dd.D (m.basis a) (ui dd u b))
      = (∑ a : ι, ∑ b : ι, cG d a j b * dd.D (m.basis a) (ui dd u b))
        - (∑ a : ι, ∑ b : ι, cG d j b a * dd.D (m.basis a) (ui dd u b)) := by
  rw [show (∑ a : ι, ∑ b : ι, (cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
        + (if j = a then ∑ i : ι, gamma d i i b else 0)
        - (if j = b then ∑ i : ι, gamma d i i a else 0)) * dd.D (m.basis a) (ui dd u b))
      = ∑ a : ι, ∑ b : ι, ((cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
        + (if a = j then ∑ i : ι, gamma d i i b else 0)
        - (if b = j then ∑ i : ι, gamma d i i a else 0)) * dd.D (m.basis a) (ui dd u b)) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [eq_comm]]
  sorry

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
