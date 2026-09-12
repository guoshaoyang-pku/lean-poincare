import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid A] (f : ι → ι → A) (j : ι) :
    (∑ a : ι, ∑ b : ι, (if j = a then f a b else 0))
      = ∑ a : ι, ∑ b : ι, (if a = j then f a b else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [eq_comm]
