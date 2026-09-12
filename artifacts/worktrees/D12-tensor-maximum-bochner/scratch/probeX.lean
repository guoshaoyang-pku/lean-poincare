import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f : ι → ι → A) :
    (∑ l : ι, ui * ∑ k : ι, f l k) = ∑ l : ι, ∑ k : ι, ui * f l k := by
  rw [show (∑ l : ι, ui * ∑ k : ι, f l k) = ∑ l : ι, ∑ k : ι, ui * f l k by
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]]
