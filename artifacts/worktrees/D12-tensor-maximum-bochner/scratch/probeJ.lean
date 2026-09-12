import Mathlib
open scoped BigOperators

example {ι A : Type} [Fintype ι] [AddCommMonoid A] (f g : ι → A) : True := by
  let P : Prop := (∑ i : ι, f i + g i) = (∑ i : ι, f i + g i)
  trivial

example {ι A : Type} [Fintype ι] [AddCommMonoid A] (f g : ι → A) :
    (∑ i : ι, (f i + g i)) = ∑ i : ι, (f i + g i) := by
  apply Finset.sum_congr rfl
  intro i _
  rfl
