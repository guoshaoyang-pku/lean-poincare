import Mathlib.Tactic

section
universe uA
variable {A : Type uA} [CommRing A]
variable (hfoo : (0 : A) = 0)

theorem test_one : (0 : A) = 0 := by
  exact hfoo

theorem test_two : True := by
  have h := hfoo
  trivial
end
