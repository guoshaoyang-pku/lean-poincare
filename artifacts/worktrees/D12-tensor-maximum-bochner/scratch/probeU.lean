import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (a b c d : ι → A) :
    (∑ y : ι, (a y - b y - c y + d y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) + (∑ y : ι, d y) := by
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

example {ι A : Type*} [Fintype ι] [Ring A] (a b c d e f : ι → A) :
    (∑ y : ι, (a y - b y - c y + d y + e y - f y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) + (∑ y : ι, d y) + (∑ y : ι, e y) - (∑ y : ι, f y) := by
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

example {ι A : Type*} [Fintype ι] [Ring A] (a b c d e f : ι → A) :
    (∑ y : ι, (a y - b y - c y + d y + e y - f y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) + (∑ y : ι, d y) + (∑ y : ι, e y) - (∑ y : ι, f y) := by
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_sub_distrib]
