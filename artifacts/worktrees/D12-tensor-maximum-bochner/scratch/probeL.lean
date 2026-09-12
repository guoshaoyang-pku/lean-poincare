import Mathlib
open scoped BigOperators

example {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (f : ι → V →ₗ[ℝ] ℝ) (v : V) :
    (∑ i : ι, f i) v = ∑ i : ι, f i v := by
  exact LinearMap.sum_apply Finset.univ f v

example {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (f : ι → V →ₗ[ℝ] ℝ) (v : V) :
    (∑ i : ι, f i) v = ∑ i : ι, f i v := by
  rw [LinearMap.sum_apply]
