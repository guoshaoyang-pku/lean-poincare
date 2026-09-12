import Mathlib.Topology.MetricSpace.CoveringNumbers
import Poincare.D12.GeometricCompactness.Criterion
open Set Metric Poincare.D12.GeometricCompactness
#check @Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist
#check @Set.encard_eq_coe_toFinset_card
#check @ENat.card_eq_coe_fintypeCard
#check @Set.Finite.toFinset_card
example (C : Set ℝ) (hC : C.Finite) : C.encard = (Fintype.card C : ℕ∞) := by
  rw [hC.encard_eq_coe_toFinset_card, ENat.card_eq_coe_fintypeCard]
  congr 1
  exact (Fintype.card_coe C).symm
example (C : Set ℝ) (hC : C.Finite) : (univ : Set C).encard = C.encard := by
  rw [Set.encard_univ, ENat.card_eq_coe_fintypeCard, hC.encard_eq_coe_toFinset_card,
    ENat.card_eq_coe_fintypeCard]
  congr 1
  exact (Fintype.card_coe C).symm
