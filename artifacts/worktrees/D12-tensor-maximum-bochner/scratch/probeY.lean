import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f : ι → ι → A) :
    (∑ i_1 : ι, ui * ∑ l : ι, f i_1 l) = ∑ i_1 : ι, ∑ l : ι, ui * f i_1 l := by
  rw [Finset.mul_sum]

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f g h : ι → ι → A) :
    (∑ i_1 : ι, ui * ∑ l : ι, f i_1 l) = ∑ i_1 : ι, ∑ l : ι, ui * f i_1 l := by
  repeat rw [Finset.mul_sum]
