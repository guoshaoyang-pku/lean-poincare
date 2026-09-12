import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (a b c : ι → A) :
    (∑ y : ι, (a y - b y - c y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) := by
  simp_rw [Finset.sum_sub_distrib]

example {ι A : Type*} [Fintype ι] [Ring A] (a b c : ι → A) :
    (∑ y : ι, (a y - b y - c y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) := by
  repeat rw [Finset.sum_sub_distrib]

example {ι A : Type*} [Fintype ι] [Ring A] (a b c : ι → A) :
    (∑ y : ι, (a y - b y - c y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

example {ι A : Type*} [Fintype ι] [Ring A] (a b c : ι → A) :
    (∑ y : ι, (a y - b y - c y)) = (∑ y : ι, a y) - (∑ y : ι, b y) - (∑ y : ι, c y) := by
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_sub_distrib]
