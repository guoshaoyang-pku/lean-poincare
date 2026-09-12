import Poincare.L4.Compactness.MeasureGrowthChain
import Poincare.L4.Compactness.FamilyCoversWitness
open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff
noncomputable section
namespace Poincare.L4.Compactness

def twoPointEquiv : (toGHSpace (Disc 2)).Rep ≃ᵢ Disc 2 :=
  Classical.choice (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc 2))
def twoPointZero : (toGHSpace (Disc 2)).Rep := twoPointEquiv.symm ⟨0, by decide⟩

example : twoPointEquiv twoPointZero = ⟨0, by decide⟩ := by
  rw [twoPointZero]
  exact twoPointEquiv.apply_symm_apply ⟨0, by decide⟩

example (c : (toGHSpace (Disc 2)).Rep) :
    (twoPointEquiv c = ⟨0, by decide⟩ ∨ twoPointEquiv c = ⟨1, by decide⟩) := by
  have hfin : ∀ k : Disc 2, k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ := by
    intro k
    fin_cases k <;> simp
  exact hfin (twoPointEquiv c)

end Poincare.L4.Compactness
