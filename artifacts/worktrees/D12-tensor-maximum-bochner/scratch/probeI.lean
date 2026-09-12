import Mathlib
open scoped BigOperators

example {ι A : Type} [Fintype ι] [Sub A] [Add A] (f g h : ι → A) :
    (∑ i : ι, 2 * (f i + g i) - 2 * h i) = ∑ i : ι, 2 * (f i + g i) - 2 * h i := by
  apply Finset.sum_congr rfl
  intro i _
  rfl
