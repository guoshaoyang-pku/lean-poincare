import Mathlib.Tactic

section
universe uA
variable {A : Type uA} [CommRing A]
variable (x : A)

theorem test_three : (x : A) = x := by
  rfl

theorem test_four : True := by
  have h := x
  trivial
end
