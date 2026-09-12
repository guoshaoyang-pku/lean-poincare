import Mathlib
open scoped BigOperators

example {ι A : Type} [Fintype ι] [Sub A] [Add A] (f g h : ι → A) :
    True := by
  let P1 : Prop := (∑ i : ι, 2 * (f i + g i) - 2 * h i) = ∑ i : ι, 2 * (f i + g i) - 2 * h i
  let P2 : Prop := ((∑ i : ι, 2 * (f i + g i)) - 2 * h i) = ((∑ i : ι, 2 * (f i + g i)) - 2 * h i)
  trivial
