import Mathlib
open scoped BigOperators

example {A : Type*} [Ring A] (ui s1 s2 s3 s4 : A) :
    ui * s1 + (-1 : ℤ) • (ui * s2) + (-1 : ℤ) • (ui * s3) + ui * s4
      = ui * (s1 - s2 - s3 + s4) := by
  ring_nf

example {A : Type*} [Ring A] (ui s1 s2 s3 s4 : A) :
    ui * s1 + (-1 : ℤ) • (ui * s2) + (-1 : ℤ) • (ui * s3) + ui * s4
      = ui * (s1 - s2 - s3 + s4) := by
  simp_rw [neg_one_smul]
  ring_nf
