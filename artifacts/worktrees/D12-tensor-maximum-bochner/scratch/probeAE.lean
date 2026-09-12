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

example (d : LeviCivitaData m b) (j p : ι) :
    (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A))
      = - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

example (d : LeviCivitaData m b) (j p : ι) :
    (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A))
      = (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) - ricciForm d j p := by
  have hc := weitz_coefficient d j p
  rw [show (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A))
      = - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring]
  have hc' : - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A))
      = (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) - ricciForm d j p := by
    have hsum : (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A))
        = ricciForm d j p - (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) := by
      rw [← hc]
      abel
    rw [hsum]
    abel
  exact hc'

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
