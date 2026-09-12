/- Independent reviewer concrete checks on the discrete witness model. -/
import Poincare.L4.Compactness.FamilyCoversWitness
open Set Metric
open scoped NNReal ENNReal
open GromovHausdorff
namespace ReviewerConcrete
open Poincare.L4.Compactness

example : dist (show Disc 3 from (⟨0, by norm_num⟩ : Fin 3))
    (show Disc 3 from (⟨2, by norm_num⟩ : Fin 3)) = 1 :=
  Disc.dist_eq_one (by decide)

example : dist (show Disc 3 from (⟨1, by norm_num⟩ : Fin 3))
    (show Disc 3 from (⟨1, by norm_num⟩ : Fin 3)) = 0 :=
  Disc.dist_eq_zero rfl

example : (univ : Set (Disc 3)).encard = (3 : ℕ∞) := by simp [Disc]
example : (univ : Set (Disc 0)).encard = (0 : ℕ∞) := by simp [Disc]

-- sharpness chain: every 1/2-cover of the largest witness member needs N+1 centres
example (N : ℕ) {s : Set (GHSpace.Rep (discGH N))}
    (h : (univ : Set (GHSpace.Rep (discGH N))) ⊆ ⋃ x ∈ s, ball x (1 / 2 : ℝ)) :
    N + 1 ≤ Cardinal.mk s :=
  finiteDiscFamily_cover_half_card_ge N h

-- hypotheses of the main theorem hold on the finite witness with n = N+1, R = 1
example (N : ℕ) : (∀ p ∈ finiteDiscFamily N, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ ((N + 1 : ℕ) : ℕ∞)) ∧
    (∃ R : ℝ≥0, ∀ p ∈ finiteDiscFamily N, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :=
  finiteDiscFamily_hypotheses N

end ReviewerConcrete
