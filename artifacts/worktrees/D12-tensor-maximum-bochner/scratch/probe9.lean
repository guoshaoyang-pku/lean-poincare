import Mathlib.Tactic

section
variable (hfoo : True)

theorem test_five : True := by
  exact hfoo
end
