import Mathlib.Tactic

namespace Probe
universe uA
variable {A : Type uA} [CommRing A]
variable (hfoo : (0 : A) = 0)

lemma test_one : (0 : A) = 0 := by
  exact hfoo

lemma test_two : True := by
  have h := hfoo
  trivial

end Probe
