import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (f g : ι → A) :
    True := by
  have h : (∑ m : ι, f m) = -∑ m : ι, g m := by
    rw [show (∑ m : ι, f m) = ∑ m : ι, -(g m) by
      apply Finset.sum_congr rfl
      intro m _
      sorry]
    rw [← Finset.sum_neg_distrib]
  trivial

example {ι A : Type*} [Fintype ι] [Ring A] (f g : ι → A) :
    (∑ m : ι, f m) + (∑ m : ι, g m) = (∑ m : ι, f m) - ∑ m : ι, g m := by
  abel
