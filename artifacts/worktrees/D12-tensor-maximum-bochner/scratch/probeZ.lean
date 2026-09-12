import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f : ι → ι → A) :
    (ui * ∑ l : ι, f 0 l) = (ui * ∑ l : ι, f 0 l) := rfl

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f : ι → ι → A) :
    (ui * (∑ l : ι, f 0 l)) = (∑ l : ι, ui * f 0 l) := by
  rw [Finset.mul_sum]

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (f : ι → ι → A) :
    (ui * ∑ l : ι, f 0 l) = (∑ l : ι, ui * f 0 l) := by
  change ui * (∑ l : ι, f 0 l) = ∑ l : ι, ui * f 0 l
  rw [Finset.mul_sum]
