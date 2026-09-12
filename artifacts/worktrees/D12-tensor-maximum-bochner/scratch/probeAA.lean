import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (s1 s2 s3 s4 s5 s6 : ι → A) :
    (∑ x : ι, (s1 x - s2 x - s3 x + s4 x)) + (∑ mm : ι, s5 mm) - (∑ l : ι, s6 l)
      = (∑ mm : ι, (s1 mm - s2 mm - s3 mm + s4 mm)) + (∑ k : ι, (s5 k - s6 k)) := by
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  abel
