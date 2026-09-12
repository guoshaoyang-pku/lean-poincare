import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A]
    (a b c d e f : ι → ι → A) :
    (∑ x : ι, ∑ y : ι, (a x y - b x y - c x y + d x y + e x y - f x y))
      = (∑ x : ι, ∑ y : ι, a x y) - (∑ x : ι, ∑ y : ι, b x y)
        - (∑ x : ι, ∑ y : ι, c x y) + (∑ x : ι, ∑ y : ι, d x y)
        + (∑ x : ι, ∑ y : ι, e x y) - (∑ x : ι, ∑ y : ι, f x y) := by
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
