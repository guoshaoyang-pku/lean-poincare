import Mathlib
open scoped BigOperators

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (X Y Z : ι → A) :
    ui * ((∑ mm : ι, X mm) - (∑ mm : ι, Y mm) + (∑ mm : ι, Z mm))
      = (∑ mm : ι, ui * X mm) - (∑ mm : ι, ui * Y mm) + (∑ mm : ι, ui * Z mm) := by
  rw [mul_add]
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

example {ι A : Type*} [Fintype ι] [Ring A] (ui : A) (X Y : ι → A) :
    ui * ((∑ mm : ι, X mm) - (∑ mm : ι, Y mm))
      = (∑ mm : ι, ui * X mm) - (∑ mm : ι, ui * Y mm) := by
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
